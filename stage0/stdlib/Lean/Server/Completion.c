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
lean_object* v_key_16_; lean_object* v_tail_17_; lean_object* v_fst_18_; lean_object* v_snd_19_; lean_object* v_fst_20_; lean_object* v_snd_21_; uint8_t v___x_22_; 
v_key_16_ = lean_ctor_get(v_x_14_, 0);
v_tail_17_ = lean_ctor_get(v_x_14_, 2);
v_fst_18_ = lean_ctor_get(v_key_16_, 0);
v_snd_19_ = lean_ctor_get(v_key_16_, 1);
v_fst_20_ = lean_ctor_get(v_a_13_, 0);
v_snd_21_ = lean_ctor_get(v_a_13_, 1);
v___x_22_ = lean_string_dec_eq(v_fst_18_, v_fst_20_);
if (v___x_22_ == 0)
{
v_x_14_ = v_tail_17_;
goto _start;
}
else
{
uint8_t v___x_24_; 
v___x_24_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0(v_snd_19_, v_snd_21_);
if (v___x_24_ == 0)
{
v_x_14_ = v_tail_17_;
goto _start;
}
else
{
return v___x_24_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg___boxed(lean_object* v_a_26_, lean_object* v_x_27_){
_start:
{
uint8_t v_res_28_; lean_object* v_r_29_; 
v_res_28_ = l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg(v_a_26_, v_x_27_);
lean_dec(v_x_27_);
lean_dec_ref(v_a_26_);
v_r_29_ = lean_box(v_res_28_);
return v_r_29_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__3___redArg(lean_object* v_x_30_, lean_object* v_x_31_){
_start:
{
if (lean_obj_tag(v_x_31_) == 0)
{
return v_x_30_;
}
else
{
lean_object* v_key_32_; lean_object* v_value_33_; lean_object* v_tail_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_67_; 
v_key_32_ = lean_ctor_get(v_x_31_, 0);
v_value_33_ = lean_ctor_get(v_x_31_, 1);
v_tail_34_ = lean_ctor_get(v_x_31_, 2);
v_isSharedCheck_67_ = !lean_is_exclusive(v_x_31_);
if (v_isSharedCheck_67_ == 0)
{
v___x_36_ = v_x_31_;
v_isShared_37_ = v_isSharedCheck_67_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_tail_34_);
lean_inc(v_value_33_);
lean_inc(v_key_32_);
lean_dec(v_x_31_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_67_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v_fst_38_; lean_object* v_snd_39_; lean_object* v___x_40_; uint64_t v___x_41_; uint64_t v___y_43_; 
v_fst_38_ = lean_ctor_get(v_key_32_, 0);
v_snd_39_ = lean_ctor_get(v_key_32_, 1);
v___x_40_ = lean_array_get_size(v_x_30_);
v___x_41_ = lean_string_hash(v_fst_38_);
if (lean_obj_tag(v_snd_39_) == 0)
{
uint64_t v___x_62_; 
v___x_62_ = 11ULL;
v___y_43_ = v___x_62_;
goto v___jp_42_;
}
else
{
lean_object* v_val_63_; uint64_t v___x_64_; uint64_t v___x_65_; uint64_t v___x_66_; 
v_val_63_ = lean_ctor_get(v_snd_39_, 0);
v___x_64_ = l_Lean_Lsp_instHashableInsertReplaceEdit_hash(v_val_63_);
v___x_65_ = 13ULL;
v___x_66_ = lean_uint64_mix_hash(v___x_64_, v___x_65_);
v___y_43_ = v___x_66_;
goto v___jp_42_;
}
v___jp_42_:
{
uint64_t v___x_44_; uint64_t v___x_45_; uint64_t v___x_46_; uint64_t v_fold_47_; uint64_t v___x_48_; uint64_t v___x_49_; uint64_t v___x_50_; size_t v___x_51_; size_t v___x_52_; size_t v___x_53_; size_t v___x_54_; size_t v___x_55_; lean_object* v___x_56_; lean_object* v___x_58_; 
v___x_44_ = lean_uint64_mix_hash(v___x_41_, v___y_43_);
v___x_45_ = 32ULL;
v___x_46_ = lean_uint64_shift_right(v___x_44_, v___x_45_);
v_fold_47_ = lean_uint64_xor(v___x_44_, v___x_46_);
v___x_48_ = 16ULL;
v___x_49_ = lean_uint64_shift_right(v_fold_47_, v___x_48_);
v___x_50_ = lean_uint64_xor(v_fold_47_, v___x_49_);
v___x_51_ = lean_uint64_to_usize(v___x_50_);
v___x_52_ = lean_usize_of_nat(v___x_40_);
v___x_53_ = ((size_t)1ULL);
v___x_54_ = lean_usize_sub(v___x_52_, v___x_53_);
v___x_55_ = lean_usize_land(v___x_51_, v___x_54_);
v___x_56_ = lean_array_uget_borrowed(v_x_30_, v___x_55_);
lean_inc(v___x_56_);
if (v_isShared_37_ == 0)
{
lean_ctor_set(v___x_36_, 2, v___x_56_);
v___x_58_ = v___x_36_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_61_; 
v_reuseFailAlloc_61_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_61_, 0, v_key_32_);
lean_ctor_set(v_reuseFailAlloc_61_, 1, v_value_33_);
lean_ctor_set(v_reuseFailAlloc_61_, 2, v___x_56_);
v___x_58_ = v_reuseFailAlloc_61_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
lean_object* v___x_59_; 
v___x_59_ = lean_array_uset(v_x_30_, v___x_55_, v___x_58_);
v_x_30_ = v___x_59_;
v_x_31_ = v_tail_34_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2___redArg(lean_object* v_i_68_, lean_object* v_source_69_, lean_object* v_target_70_){
_start:
{
lean_object* v___x_71_; uint8_t v___x_72_; 
v___x_71_ = lean_array_get_size(v_source_69_);
v___x_72_ = lean_nat_dec_lt(v_i_68_, v___x_71_);
if (v___x_72_ == 0)
{
lean_dec_ref(v_source_69_);
lean_dec(v_i_68_);
return v_target_70_;
}
else
{
lean_object* v_es_73_; lean_object* v___x_74_; lean_object* v_source_75_; lean_object* v_target_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v_es_73_ = lean_array_fget(v_source_69_, v_i_68_);
v___x_74_ = lean_box(0);
v_source_75_ = lean_array_fset(v_source_69_, v_i_68_, v___x_74_);
v_target_76_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__3___redArg(v_target_70_, v_es_73_);
v___x_77_ = lean_unsigned_to_nat(1u);
v___x_78_ = lean_nat_add(v_i_68_, v___x_77_);
lean_dec(v_i_68_);
v_i_68_ = v___x_78_;
v_source_69_ = v_source_75_;
v_target_70_ = v_target_76_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg(lean_object* v_data_80_){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v_nbuckets_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_81_ = lean_array_get_size(v_data_80_);
v___x_82_ = lean_unsigned_to_nat(2u);
v_nbuckets_83_ = lean_nat_mul(v___x_81_, v___x_82_);
v___x_84_ = lean_unsigned_to_nat(0u);
v___x_85_ = lean_box(0);
v___x_86_ = lean_mk_array(v_nbuckets_83_, v___x_85_);
v___x_87_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2___redArg(v___x_84_, v_data_80_, v___x_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__2(lean_object* v_as_88_, size_t v_sz_89_, size_t v_i_90_, lean_object* v_b_91_){
_start:
{
lean_object* v_a_93_; uint8_t v___x_97_; 
v___x_97_ = lean_usize_dec_lt(v_i_90_, v_sz_89_);
if (v___x_97_ == 0)
{
return v_b_91_;
}
else
{
lean_object* v_snd_98_; lean_object* v_fst_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_170_; 
v_snd_98_ = lean_ctor_get(v_b_91_, 1);
v_fst_99_ = lean_ctor_get(v_b_91_, 0);
v_isSharedCheck_170_ = !lean_is_exclusive(v_b_91_);
if (v_isSharedCheck_170_ == 0)
{
v___x_101_ = v_b_91_;
v_isShared_102_ = v_isSharedCheck_170_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_snd_98_);
lean_inc(v_fst_99_);
lean_dec(v_b_91_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_170_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v_size_103_; lean_object* v_buckets_104_; lean_object* v_a_105_; lean_object* v_fst_107_; lean_object* v_snd_108_; lean_object* v_label_117_; lean_object* v_textEdit_x3f_118_; lean_object* v___x_119_; lean_object* v___x_120_; uint64_t v___x_121_; uint64_t v___y_123_; 
v_size_103_ = lean_ctor_get(v_snd_98_, 0);
v_buckets_104_ = lean_ctor_get(v_snd_98_, 1);
v_a_105_ = lean_array_uget_borrowed(v_as_88_, v_i_90_);
v_label_117_ = lean_ctor_get(v_a_105_, 0);
v_textEdit_x3f_118_ = lean_ctor_get(v_a_105_, 4);
lean_inc(v_textEdit_x3f_118_);
lean_inc_ref(v_label_117_);
v___x_119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_119_, 0, v_label_117_);
lean_ctor_set(v___x_119_, 1, v_textEdit_x3f_118_);
v___x_120_ = lean_array_get_size(v_buckets_104_);
v___x_121_ = lean_string_hash(v_label_117_);
if (lean_obj_tag(v_textEdit_x3f_118_) == 0)
{
uint64_t v___x_165_; 
v___x_165_ = 11ULL;
v___y_123_ = v___x_165_;
goto v___jp_122_;
}
else
{
lean_object* v_val_166_; uint64_t v___x_167_; uint64_t v___x_168_; uint64_t v___x_169_; 
v_val_166_ = lean_ctor_get(v_textEdit_x3f_118_, 0);
v___x_167_ = l_Lean_Lsp_instHashableInsertReplaceEdit_hash(v_val_166_);
v___x_168_ = 13ULL;
v___x_169_ = lean_uint64_mix_hash(v___x_167_, v___x_168_);
v___y_123_ = v___x_169_;
goto v___jp_122_;
}
v___jp_106_:
{
uint8_t v___x_109_; 
v___x_109_ = lean_unbox(v_fst_107_);
lean_dec(v_fst_107_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; lean_object* v___x_112_; 
lean_inc(v_a_105_);
v___x_110_ = lean_array_push(v_fst_99_, v_a_105_);
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 1, v_snd_108_);
lean_ctor_set(v___x_101_, 0, v___x_110_);
v___x_112_ = v___x_101_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v___x_110_);
lean_ctor_set(v_reuseFailAlloc_113_, 1, v_snd_108_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
v_a_93_ = v___x_112_;
goto v___jp_92_;
}
}
else
{
lean_object* v___x_115_; 
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 1, v_snd_108_);
v___x_115_ = v___x_101_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_fst_99_);
lean_ctor_set(v_reuseFailAlloc_116_, 1, v_snd_108_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
v_a_93_ = v___x_115_;
goto v___jp_92_;
}
}
}
v___jp_122_:
{
uint64_t v___x_124_; uint64_t v___x_125_; uint64_t v___x_126_; uint64_t v_fold_127_; uint64_t v___x_128_; uint64_t v___x_129_; uint64_t v___x_130_; size_t v___x_131_; size_t v___x_132_; size_t v___x_133_; size_t v___x_134_; size_t v___x_135_; lean_object* v_bkt_136_; uint8_t v___x_137_; 
v___x_124_ = lean_uint64_mix_hash(v___x_121_, v___y_123_);
v___x_125_ = 32ULL;
v___x_126_ = lean_uint64_shift_right(v___x_124_, v___x_125_);
v_fold_127_ = lean_uint64_xor(v___x_124_, v___x_126_);
v___x_128_ = 16ULL;
v___x_129_ = lean_uint64_shift_right(v_fold_127_, v___x_128_);
v___x_130_ = lean_uint64_xor(v_fold_127_, v___x_129_);
v___x_131_ = lean_uint64_to_usize(v___x_130_);
v___x_132_ = lean_usize_of_nat(v___x_120_);
v___x_133_ = ((size_t)1ULL);
v___x_134_ = lean_usize_sub(v___x_132_, v___x_133_);
v___x_135_ = lean_usize_land(v___x_131_, v___x_134_);
v_bkt_136_ = lean_array_uget_borrowed(v_buckets_104_, v___x_135_);
v___x_137_ = l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg(v___x_119_, v_bkt_136_);
if (v___x_137_ == 0)
{
lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_161_; 
lean_inc_ref(v_buckets_104_);
lean_inc(v_size_103_);
v_isSharedCheck_161_ = !lean_is_exclusive(v_snd_98_);
if (v_isSharedCheck_161_ == 0)
{
lean_object* v_unused_162_; lean_object* v_unused_163_; 
v_unused_162_ = lean_ctor_get(v_snd_98_, 1);
lean_dec(v_unused_162_);
v_unused_163_ = lean_ctor_get(v_snd_98_, 0);
lean_dec(v_unused_163_);
v___x_139_ = v_snd_98_;
v_isShared_140_ = v_isSharedCheck_161_;
goto v_resetjp_138_;
}
else
{
lean_dec(v_snd_98_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_161_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v_size_x27_143_; lean_object* v___x_144_; lean_object* v_buckets_x27_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; uint8_t v___x_151_; 
v___x_141_ = lean_box(0);
v___x_142_ = lean_unsigned_to_nat(1u);
v_size_x27_143_ = lean_nat_add(v_size_103_, v___x_142_);
lean_dec(v_size_103_);
lean_inc(v_bkt_136_);
v___x_144_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_144_, 0, v___x_119_);
lean_ctor_set(v___x_144_, 1, v___x_141_);
lean_ctor_set(v___x_144_, 2, v_bkt_136_);
v_buckets_x27_145_ = lean_array_uset(v_buckets_104_, v___x_135_, v___x_144_);
v___x_146_ = lean_unsigned_to_nat(4u);
v___x_147_ = lean_nat_mul(v_size_x27_143_, v___x_146_);
v___x_148_ = lean_unsigned_to_nat(3u);
v___x_149_ = lean_nat_div(v___x_147_, v___x_148_);
lean_dec(v___x_147_);
v___x_150_ = lean_array_get_size(v_buckets_x27_145_);
v___x_151_ = lean_nat_dec_le(v___x_149_, v___x_150_);
lean_dec(v___x_149_);
if (v___x_151_ == 0)
{
lean_object* v_val_152_; lean_object* v___x_154_; 
v_val_152_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg(v_buckets_x27_145_);
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 1, v_val_152_);
lean_ctor_set(v___x_139_, 0, v_size_x27_143_);
v___x_154_ = v___x_139_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_size_x27_143_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v_val_152_);
v___x_154_ = v_reuseFailAlloc_156_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
lean_object* v___x_155_; 
v___x_155_ = lean_box(v___x_137_);
v_fst_107_ = v___x_155_;
v_snd_108_ = v___x_154_;
goto v___jp_106_;
}
}
else
{
lean_object* v___x_158_; 
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 1, v_buckets_x27_145_);
lean_ctor_set(v___x_139_, 0, v_size_x27_143_);
v___x_158_ = v___x_139_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_size_x27_143_);
lean_ctor_set(v_reuseFailAlloc_160_, 1, v_buckets_x27_145_);
v___x_158_ = v_reuseFailAlloc_160_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
lean_object* v___x_159_; 
v___x_159_ = lean_box(v___x_137_);
v_fst_107_ = v___x_159_;
v_snd_108_ = v___x_158_;
goto v___jp_106_;
}
}
}
}
else
{
lean_object* v___x_164_; 
lean_dec_ref_known(v___x_119_, 2);
v___x_164_ = lean_box(v___x_137_);
v_fst_107_ = v___x_164_;
v_snd_108_ = v_snd_98_;
goto v___jp_106_;
}
}
}
}
v___jp_92_:
{
size_t v___x_94_; size_t v___x_95_; 
v___x_94_ = ((size_t)1ULL);
v___x_95_ = lean_usize_add(v_i_90_, v___x_94_);
v_i_90_ = v___x_95_;
v_b_91_ = v_a_93_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__2___boxed(lean_object* v_as_171_, lean_object* v_sz_172_, lean_object* v_i_173_, lean_object* v_b_174_){
_start:
{
size_t v_sz_boxed_175_; size_t v_i_boxed_176_; lean_object* v_res_177_; 
v_sz_boxed_175_ = lean_unbox_usize(v_sz_172_);
lean_dec(v_sz_172_);
v_i_boxed_176_ = lean_unbox_usize(v_i_173_);
lean_dec(v_i_173_);
v_res_177_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__2(v_as_171_, v_sz_boxed_175_, v_i_boxed_176_, v_b_174_);
lean_dec_ref(v_as_171_);
return v_res_177_;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__1(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_180_ = lean_box(0);
v___x_181_ = lean_unsigned_to_nat(16u);
v___x_182_ = lean_mk_array(v___x_181_, v___x_180_);
return v___x_182_;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__2(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v_index_185_; 
v___x_183_ = lean_obj_once(&l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__1, &l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__1_once, _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__1);
v___x_184_ = lean_unsigned_to_nat(0u);
v_index_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_index_185_, 0, v___x_184_);
lean_ctor_set(v_index_185_, 1, v___x_183_);
return v_index_185_;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__3(void){
_start:
{
lean_object* v_index_186_; lean_object* v_r_187_; lean_object* v___x_188_; 
v_index_186_ = lean_obj_once(&l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__2, &l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__2_once, _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__2);
v_r_187_ = ((lean_object*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__0));
v___x_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_188_, 0, v_r_187_);
lean_ctor_set(v___x_188_, 1, v_index_186_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems(lean_object* v_items_189_){
_start:
{
lean_object* v___x_190_; size_t v_sz_191_; size_t v___x_192_; lean_object* v___x_193_; lean_object* v_fst_194_; 
v___x_190_ = lean_obj_once(&l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__3, &l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__3_once, _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__3);
v_sz_191_ = lean_array_size(v_items_189_);
v___x_192_ = ((size_t)0ULL);
v___x_193_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__2(v_items_189_, v_sz_191_, v___x_192_, v___x_190_);
v_fst_194_ = lean_ctor_get(v___x_193_, 0);
lean_inc(v_fst_194_);
lean_dec_ref(v___x_193_);
return v_fst_194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___boxed(lean_object* v_items_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems(v_items_195_);
lean_dec_ref(v_items_195_);
return v_res_196_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0(lean_object* v_00_u03b2_197_, lean_object* v_a_198_, lean_object* v_x_199_){
_start:
{
uint8_t v___x_200_; 
v___x_200_ = l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg(v_a_198_, v_x_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___boxed(lean_object* v_00_u03b2_201_, lean_object* v_a_202_, lean_object* v_x_203_){
_start:
{
uint8_t v_res_204_; lean_object* v_r_205_; 
v_res_204_ = l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0(v_00_u03b2_201_, v_a_202_, v_x_203_);
lean_dec(v_x_203_);
lean_dec_ref(v_a_202_);
v_r_205_ = lean_box(v_res_204_);
return v_r_205_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1(lean_object* v_00_u03b2_206_, lean_object* v_data_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg(v_data_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2(lean_object* v_00_u03b2_209_, lean_object* v_i_210_, lean_object* v_source_211_, lean_object* v_target_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2___redArg(v_i_210_, v_source_211_, v_target_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_214_, lean_object* v_x_215_, lean_object* v_x_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__3___redArg(v_x_215_, v_x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__0(lean_object* v_uri_218_, lean_object* v_pos_219_, lean_object* v_caps_220_, lean_object* v_as_221_, size_t v_sz_222_, size_t v_i_223_, lean_object* v_b_224_, lean_object* v___y_225_){
_start:
{
lean_object* v_a_228_; lean_object* v_completions_232_; uint8_t v___x_237_; 
v___x_237_ = lean_usize_dec_lt(v_i_223_, v_sz_222_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; lean_object* v___x_239_; 
lean_dec_ref(v_caps_220_);
lean_dec_ref(v_pos_219_);
lean_dec_ref(v_uri_218_);
v___x_238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_238_, 0, v_b_224_);
v___x_239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
return v___x_239_;
}
else
{
lean_object* v_a_240_; lean_object* v_fst_241_; lean_object* v_snd_242_; lean_object* v___x_243_; 
v_a_240_ = lean_array_uget_borrowed(v_as_221_, v_i_223_);
v_fst_241_ = lean_ctor_get(v_a_240_, 0);
v_snd_242_ = lean_ctor_get(v_a_240_, 1);
v___x_243_ = l_Lean_Server_CancellableM_checkCancelled(v___y_225_);
if (lean_obj_tag(v___x_243_) == 0)
{
lean_object* v_a_244_; 
v_a_244_ = lean_ctor_get(v___x_243_, 0);
lean_inc(v_a_244_);
lean_dec_ref_known(v___x_243_, 1);
if (lean_obj_tag(v_a_244_) == 0)
{
lean_object* v_a_245_; 
lean_dec_ref(v_b_224_);
lean_dec_ref(v_caps_220_);
lean_dec_ref(v_pos_219_);
lean_dec_ref(v_uri_218_);
v_a_245_ = lean_ctor_get(v_a_244_, 0);
lean_inc(v_a_245_);
lean_dec_ref_known(v_a_244_, 1);
v_a_228_ = v_a_245_;
goto v___jp_227_;
}
else
{
lean_object* v_info_246_; 
lean_dec_ref_known(v_a_244_, 1);
v_info_246_ = lean_ctor_get(v_fst_241_, 2);
switch(lean_obj_tag(v_info_246_))
{
case 1:
{
lean_object* v_hoverInfo_247_; lean_object* v_ctx_248_; lean_object* v_stx_249_; lean_object* v_id_250_; uint8_t v_danglingDot_251_; lean_object* v_lctx_252_; lean_object* v___x_253_; 
v_hoverInfo_247_ = lean_ctor_get(v_fst_241_, 0);
v_ctx_248_ = lean_ctor_get(v_fst_241_, 1);
v_stx_249_ = lean_ctor_get(v_info_246_, 0);
v_id_250_ = lean_ctor_get(v_info_246_, 1);
v_danglingDot_251_ = lean_ctor_get_uint8(v_info_246_, sizeof(void*)*4);
v_lctx_252_ = lean_ctor_get(v_info_246_, 2);
lean_inc(v_hoverInfo_247_);
lean_inc(v_id_250_);
lean_inc(v_stx_249_);
lean_inc_ref(v_lctx_252_);
lean_inc_ref(v_ctx_248_);
lean_inc(v_snd_242_);
lean_inc_ref(v_pos_219_);
lean_inc_ref(v_uri_218_);
v___x_253_ = l_Lean_Server_Completion_idCompletion(v_uri_218_, v_pos_219_, v_snd_242_, v_ctx_248_, v_lctx_252_, v_stx_249_, v_id_250_, v_hoverInfo_247_, v_danglingDot_251_, v___y_225_);
if (lean_obj_tag(v___x_253_) == 0)
{
lean_object* v_a_254_; 
v_a_254_ = lean_ctor_get(v___x_253_, 0);
lean_inc(v_a_254_);
lean_dec_ref_known(v___x_253_, 1);
if (lean_obj_tag(v_a_254_) == 0)
{
lean_object* v_a_255_; 
lean_dec_ref(v_b_224_);
lean_dec_ref(v_caps_220_);
lean_dec_ref(v_pos_219_);
lean_dec_ref(v_uri_218_);
v_a_255_ = lean_ctor_get(v_a_254_, 0);
lean_inc(v_a_255_);
lean_dec_ref_known(v_a_254_, 1);
v_a_228_ = v_a_255_;
goto v___jp_227_;
}
else
{
lean_object* v_a_256_; 
v_a_256_ = lean_ctor_get(v_a_254_, 0);
lean_inc(v_a_256_);
lean_dec_ref_known(v_a_254_, 1);
v_completions_232_ = v_a_256_;
goto v___jp_231_;
}
}
else
{
lean_dec_ref(v_b_224_);
lean_dec_ref(v_caps_220_);
lean_dec_ref(v_pos_219_);
lean_dec_ref(v_uri_218_);
return v___x_253_;
}
}
case 0:
{
lean_object* v_ctx_257_; lean_object* v_termInfo_258_; lean_object* v___x_259_; 
v_ctx_257_ = lean_ctor_get(v_fst_241_, 1);
v_termInfo_258_ = lean_ctor_get(v_info_246_, 0);
lean_inc_ref(v_termInfo_258_);
lean_inc_ref(v_ctx_257_);
lean_inc(v_snd_242_);
lean_inc_ref(v_pos_219_);
lean_inc_ref(v_uri_218_);
v___x_259_ = l_Lean_Server_Completion_dotCompletion(v_uri_218_, v_pos_219_, v_snd_242_, v_ctx_257_, v_termInfo_258_, v___y_225_);
if (lean_obj_tag(v___x_259_) == 0)
{
lean_object* v_a_260_; 
v_a_260_ = lean_ctor_get(v___x_259_, 0);
lean_inc(v_a_260_);
lean_dec_ref_known(v___x_259_, 1);
if (lean_obj_tag(v_a_260_) == 0)
{
lean_object* v_a_261_; 
lean_dec_ref(v_b_224_);
lean_dec_ref(v_caps_220_);
lean_dec_ref(v_pos_219_);
lean_dec_ref(v_uri_218_);
v_a_261_ = lean_ctor_get(v_a_260_, 0);
lean_inc(v_a_261_);
lean_dec_ref_known(v_a_260_, 1);
v_a_228_ = v_a_261_;
goto v___jp_227_;
}
else
{
lean_object* v_a_262_; 
v_a_262_ = lean_ctor_get(v_a_260_, 0);
lean_inc(v_a_262_);
lean_dec_ref_known(v_a_260_, 1);
v_completions_232_ = v_a_262_;
goto v___jp_231_;
}
}
else
{
lean_dec_ref(v_b_224_);
lean_dec_ref(v_caps_220_);
lean_dec_ref(v_pos_219_);
lean_dec_ref(v_uri_218_);
return v___x_259_;
}
}
case 2:
{
lean_object* v_ctx_263_; lean_object* v_id_264_; lean_object* v_lctx_265_; lean_object* v_expectedType_x3f_266_; lean_object* v___x_267_; 
v_ctx_263_ = lean_ctor_get(v_fst_241_, 1);
v_id_264_ = lean_ctor_get(v_info_246_, 1);
v_lctx_265_ = lean_ctor_get(v_info_246_, 2);
v_expectedType_x3f_266_ = lean_ctor_get(v_info_246_, 3);
lean_inc(v_expectedType_x3f_266_);
lean_inc(v_id_264_);
lean_inc_ref(v_lctx_265_);
lean_inc_ref(v_ctx_263_);
lean_inc(v_snd_242_);
lean_inc_ref(v_pos_219_);
lean_inc_ref(v_uri_218_);
v___x_267_ = l_Lean_Server_Completion_dotIdCompletion(v_uri_218_, v_pos_219_, v_snd_242_, v_ctx_263_, v_lctx_265_, v_id_264_, v_expectedType_x3f_266_, v___y_225_);
if (lean_obj_tag(v___x_267_) == 0)
{
lean_object* v_a_268_; 
v_a_268_ = lean_ctor_get(v___x_267_, 0);
lean_inc(v_a_268_);
lean_dec_ref_known(v___x_267_, 1);
if (lean_obj_tag(v_a_268_) == 0)
{
lean_object* v_a_269_; 
lean_dec_ref(v_b_224_);
lean_dec_ref(v_caps_220_);
lean_dec_ref(v_pos_219_);
lean_dec_ref(v_uri_218_);
v_a_269_ = lean_ctor_get(v_a_268_, 0);
lean_inc(v_a_269_);
lean_dec_ref_known(v_a_268_, 1);
v_a_228_ = v_a_269_;
goto v___jp_227_;
}
else
{
lean_object* v_a_270_; 
v_a_270_ = lean_ctor_get(v_a_268_, 0);
lean_inc(v_a_270_);
lean_dec_ref_known(v_a_268_, 1);
v_completions_232_ = v_a_270_;
goto v___jp_231_;
}
}
else
{
lean_dec_ref(v_b_224_);
lean_dec_ref(v_caps_220_);
lean_dec_ref(v_pos_219_);
lean_dec_ref(v_uri_218_);
return v___x_267_;
}
}
case 3:
{
lean_object* v_ctx_271_; lean_object* v_id_272_; lean_object* v_lctx_273_; lean_object* v_structName_274_; lean_object* v___x_275_; 
v_ctx_271_ = lean_ctor_get(v_fst_241_, 1);
v_id_272_ = lean_ctor_get(v_info_246_, 1);
v_lctx_273_ = lean_ctor_get(v_info_246_, 2);
v_structName_274_ = lean_ctor_get(v_info_246_, 3);
lean_inc(v_structName_274_);
lean_inc(v_id_272_);
lean_inc_ref(v_lctx_273_);
lean_inc_ref(v_ctx_271_);
lean_inc(v_snd_242_);
lean_inc_ref(v_pos_219_);
lean_inc_ref(v_uri_218_);
v___x_275_ = l_Lean_Server_Completion_fieldIdCompletion(v_uri_218_, v_pos_219_, v_snd_242_, v_ctx_271_, v_lctx_273_, v_id_272_, v_structName_274_, v___y_225_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_a_276_);
lean_dec_ref_known(v___x_275_, 1);
if (lean_obj_tag(v_a_276_) == 0)
{
lean_object* v_a_277_; 
lean_dec_ref(v_b_224_);
lean_dec_ref(v_caps_220_);
lean_dec_ref(v_pos_219_);
lean_dec_ref(v_uri_218_);
v_a_277_ = lean_ctor_get(v_a_276_, 0);
lean_inc(v_a_277_);
lean_dec_ref_known(v_a_276_, 1);
v_a_228_ = v_a_277_;
goto v___jp_227_;
}
else
{
lean_object* v_a_278_; 
v_a_278_ = lean_ctor_get(v_a_276_, 0);
lean_inc(v_a_278_);
lean_dec_ref_known(v_a_276_, 1);
v_completions_232_ = v_a_278_;
goto v___jp_231_;
}
}
else
{
lean_dec_ref(v_b_224_);
lean_dec_ref(v_caps_220_);
lean_dec_ref(v_pos_219_);
lean_dec_ref(v_uri_218_);
return v___x_275_;
}
}
case 5:
{
lean_object* v_ctx_279_; lean_object* v_stx_280_; lean_object* v___x_281_; 
v_ctx_279_ = lean_ctor_get(v_fst_241_, 1);
v_stx_280_ = lean_ctor_get(v_info_246_, 0);
lean_inc_ref(v_caps_220_);
lean_inc(v_stx_280_);
lean_inc_ref(v_ctx_279_);
lean_inc(v_snd_242_);
lean_inc_ref(v_pos_219_);
lean_inc_ref(v_uri_218_);
v___x_281_ = l_Lean_Server_Completion_optionCompletion(v_uri_218_, v_pos_219_, v_snd_242_, v_ctx_279_, v_stx_280_, v_caps_220_);
if (lean_obj_tag(v___x_281_) == 0)
{
lean_object* v_a_282_; 
v_a_282_ = lean_ctor_get(v___x_281_, 0);
lean_inc(v_a_282_);
lean_dec_ref_known(v___x_281_, 1);
v_completions_232_ = v_a_282_;
goto v___jp_231_;
}
else
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_290_; 
lean_dec_ref(v_b_224_);
lean_dec_ref(v_caps_220_);
lean_dec_ref(v_pos_219_);
lean_dec_ref(v_uri_218_);
v_a_283_ = lean_ctor_get(v___x_281_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_281_);
if (v_isSharedCheck_290_ == 0)
{
v___x_285_ = v___x_281_;
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v___x_281_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_288_; 
if (v_isShared_286_ == 0)
{
v___x_288_ = v___x_285_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_a_283_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
}
case 6:
{
lean_object* v_ctx_291_; lean_object* v_partialId_292_; lean_object* v___x_293_; 
v_ctx_291_ = lean_ctor_get(v_fst_241_, 1);
v_partialId_292_ = lean_ctor_get(v_info_246_, 1);
lean_inc_ref(v_caps_220_);
lean_inc(v_partialId_292_);
lean_inc_ref(v_ctx_291_);
lean_inc(v_snd_242_);
lean_inc_ref(v_pos_219_);
lean_inc_ref(v_uri_218_);
v___x_293_ = l_Lean_Server_Completion_errorNameCompletion(v_uri_218_, v_pos_219_, v_snd_242_, v_ctx_291_, v_partialId_292_, v_caps_220_);
if (lean_obj_tag(v___x_293_) == 0)
{
lean_object* v_a_294_; 
v_a_294_ = lean_ctor_get(v___x_293_, 0);
lean_inc(v_a_294_);
lean_dec_ref_known(v___x_293_, 1);
v_completions_232_ = v_a_294_;
goto v___jp_231_;
}
else
{
lean_object* v_a_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_302_; 
lean_dec_ref(v_b_224_);
lean_dec_ref(v_caps_220_);
lean_dec_ref(v_pos_219_);
lean_dec_ref(v_uri_218_);
v_a_295_ = lean_ctor_get(v___x_293_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v___x_293_);
if (v_isSharedCheck_302_ == 0)
{
v___x_297_ = v___x_293_;
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_a_295_);
lean_dec(v___x_293_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_300_; 
if (v_isShared_298_ == 0)
{
v___x_300_ = v___x_297_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_a_295_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
}
case 7:
{
lean_object* v_id_x3f_303_; uint8_t v_danglingDot_304_; lean_object* v_scopeNames_305_; lean_object* v___x_306_; 
v_id_x3f_303_ = lean_ctor_get(v_info_246_, 1);
v_danglingDot_304_ = lean_ctor_get_uint8(v_info_246_, sizeof(void*)*3);
v_scopeNames_305_ = lean_ctor_get(v_info_246_, 2);
lean_inc(v_scopeNames_305_);
lean_inc(v_id_x3f_303_);
lean_inc(v_snd_242_);
lean_inc_ref(v_pos_219_);
lean_inc_ref(v_uri_218_);
v___x_306_ = l_Lean_Server_Completion_endSectionCompletion(v_uri_218_, v_pos_219_, v_snd_242_, v_id_x3f_303_, v_danglingDot_304_, v_scopeNames_305_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v_a_307_; 
v_a_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc(v_a_307_);
lean_dec_ref_known(v___x_306_, 1);
v_completions_232_ = v_a_307_;
goto v___jp_231_;
}
else
{
lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_315_; 
lean_dec_ref(v_b_224_);
lean_dec_ref(v_caps_220_);
lean_dec_ref(v_pos_219_);
lean_dec_ref(v_uri_218_);
v_a_308_ = lean_ctor_get(v___x_306_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_315_ == 0)
{
v___x_310_ = v___x_306_;
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_306_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_313_; 
if (v_isShared_311_ == 0)
{
v___x_313_ = v___x_310_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_a_308_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
case 8:
{
lean_object* v_ctx_316_; lean_object* v___x_317_; 
v_ctx_316_ = lean_ctor_get(v_fst_241_, 1);
lean_inc_ref(v_ctx_316_);
lean_inc(v_snd_242_);
lean_inc_ref(v_pos_219_);
lean_inc_ref(v_uri_218_);
v___x_317_ = l_Lean_Server_Completion_tacticCompletion(v_uri_218_, v_pos_219_, v_snd_242_, v_ctx_316_);
if (lean_obj_tag(v___x_317_) == 0)
{
lean_object* v_a_318_; 
v_a_318_ = lean_ctor_get(v___x_317_, 0);
lean_inc(v_a_318_);
lean_dec_ref_known(v___x_317_, 1);
v_completions_232_ = v_a_318_;
goto v___jp_231_;
}
else
{
lean_object* v_a_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_326_; 
lean_dec_ref(v_b_224_);
lean_dec_ref(v_caps_220_);
lean_dec_ref(v_pos_219_);
lean_dec_ref(v_uri_218_);
v_a_319_ = lean_ctor_get(v___x_317_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_326_ == 0)
{
v___x_321_ = v___x_317_;
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_a_319_);
lean_dec(v___x_317_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_324_; 
if (v_isShared_322_ == 0)
{
v___x_324_ = v___x_321_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_a_319_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
default: 
{
lean_object* v_allCompletions_327_; 
v_allCompletions_327_ = ((lean_object*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__0));
v_completions_232_ = v_allCompletions_327_;
goto v___jp_231_;
}
}
}
}
else
{
lean_object* v_a_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_335_; 
lean_dec_ref(v_b_224_);
lean_dec_ref(v_caps_220_);
lean_dec_ref(v_pos_219_);
lean_dec_ref(v_uri_218_);
v_a_328_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_335_ == 0)
{
v___x_330_ = v___x_243_;
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_a_328_);
lean_dec(v___x_243_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_333_; 
if (v_isShared_331_ == 0)
{
v___x_333_ = v___x_330_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_a_328_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
v___jp_227_:
{
lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_229_, 0, v_a_228_);
v___x_230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
return v___x_230_;
}
v___jp_231_:
{
lean_object* v___x_233_; size_t v___x_234_; size_t v___x_235_; 
v___x_233_ = l_Array_append___redArg(v_b_224_, v_completions_232_);
lean_dec_ref(v_completions_232_);
v___x_234_ = ((size_t)1ULL);
v___x_235_ = lean_usize_add(v_i_223_, v___x_234_);
v_i_223_ = v___x_235_;
v_b_224_ = v___x_233_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__0___boxed(lean_object* v_uri_336_, lean_object* v_pos_337_, lean_object* v_caps_338_, lean_object* v_as_339_, lean_object* v_sz_340_, lean_object* v_i_341_, lean_object* v_b_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
size_t v_sz_boxed_345_; size_t v_i_boxed_346_; lean_object* v_res_347_; 
v_sz_boxed_345_ = lean_unbox_usize(v_sz_340_);
lean_dec(v_sz_340_);
v_i_boxed_346_ = lean_unbox_usize(v_i_341_);
lean_dec(v_i_341_);
v_res_347_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__0(v_uri_336_, v_pos_337_, v_caps_338_, v_as_339_, v_sz_boxed_345_, v_i_boxed_346_, v_b_342_, v___y_343_);
lean_dec_ref(v___y_343_);
lean_dec_ref(v_as_339_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__1(lean_object* v_uri_348_, lean_object* v_pos_349_, lean_object* v_caps_350_, lean_object* v_as_351_, size_t v_sz_352_, size_t v_i_353_, lean_object* v_b_354_, lean_object* v___y_355_){
_start:
{
uint8_t v___x_357_; 
v___x_357_ = lean_usize_dec_lt(v_i_353_, v_sz_352_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; lean_object* v___x_359_; 
lean_dec_ref(v_caps_350_);
lean_dec_ref(v_pos_349_);
lean_dec_ref(v_uri_348_);
v___x_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_358_, 0, v_b_354_);
v___x_359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
return v___x_359_;
}
else
{
lean_object* v_a_360_; size_t v_sz_361_; size_t v___x_362_; lean_object* v___x_363_; 
v_a_360_ = lean_array_uget_borrowed(v_as_351_, v_i_353_);
v_sz_361_ = lean_array_size(v_a_360_);
v___x_362_ = ((size_t)0ULL);
lean_inc_ref(v_caps_350_);
lean_inc_ref(v_pos_349_);
lean_inc_ref(v_uri_348_);
v___x_363_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__0(v_uri_348_, v_pos_349_, v_caps_350_, v_a_360_, v_sz_361_, v___x_362_, v_b_354_, v___y_355_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v_a_364_; 
v_a_364_ = lean_ctor_get(v___x_363_, 0);
lean_inc(v_a_364_);
if (lean_obj_tag(v_a_364_) == 0)
{
lean_dec_ref_known(v_a_364_, 1);
lean_dec_ref(v_caps_350_);
lean_dec_ref(v_pos_349_);
lean_dec_ref(v_uri_348_);
return v___x_363_;
}
else
{
lean_object* v_a_365_; lean_object* v___x_366_; lean_object* v___x_367_; uint8_t v___x_368_; 
v_a_365_ = lean_ctor_get(v_a_364_, 0);
lean_inc(v_a_365_);
lean_dec_ref_known(v_a_364_, 1);
v___x_366_ = lean_array_get_size(v_a_365_);
v___x_367_ = lean_unsigned_to_nat(0u);
v___x_368_ = lean_nat_dec_eq(v___x_366_, v___x_367_);
if (v___x_368_ == 0)
{
lean_dec(v_a_365_);
lean_dec_ref(v_caps_350_);
lean_dec_ref(v_pos_349_);
lean_dec_ref(v_uri_348_);
return v___x_363_;
}
else
{
size_t v___x_369_; size_t v___x_370_; 
lean_dec_ref_known(v___x_363_, 1);
v___x_369_ = ((size_t)1ULL);
v___x_370_ = lean_usize_add(v_i_353_, v___x_369_);
v_i_353_ = v___x_370_;
v_b_354_ = v_a_365_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_caps_350_);
lean_dec_ref(v_pos_349_);
lean_dec_ref(v_uri_348_);
return v___x_363_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__1___boxed(lean_object* v_uri_372_, lean_object* v_pos_373_, lean_object* v_caps_374_, lean_object* v_as_375_, lean_object* v_sz_376_, lean_object* v_i_377_, lean_object* v_b_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
size_t v_sz_boxed_381_; size_t v_i_boxed_382_; lean_object* v_res_383_; 
v_sz_boxed_381_ = lean_unbox_usize(v_sz_376_);
lean_dec(v_sz_376_);
v_i_boxed_382_ = lean_unbox_usize(v_i_377_);
lean_dec(v_i_377_);
v_res_383_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__1(v_uri_372_, v_pos_373_, v_caps_374_, v_as_375_, v_sz_boxed_381_, v_i_boxed_382_, v_b_378_, v___y_379_);
lean_dec_ref(v___y_379_);
lean_dec_ref(v_as_375_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_find_x3f(lean_object* v_uri_384_, lean_object* v_pos_385_, lean_object* v_fileMap_386_, lean_object* v_hoverPos_387_, lean_object* v_cmdStx_388_, lean_object* v_infoTree_389_, lean_object* v_caps_390_, lean_object* v_a_391_){
_start:
{
lean_object* v___x_393_; lean_object* v_fst_394_; lean_object* v_snd_395_; lean_object* v_allCompletions_396_; size_t v_sz_397_; size_t v___x_398_; lean_object* v___x_399_; 
v___x_393_ = l_Lean_Server_Completion_findPrioritizedCompletionPartitionsAt(v_fileMap_386_, v_hoverPos_387_, v_cmdStx_388_, v_infoTree_389_);
v_fst_394_ = lean_ctor_get(v___x_393_, 0);
lean_inc(v_fst_394_);
v_snd_395_ = lean_ctor_get(v___x_393_, 1);
lean_inc(v_snd_395_);
lean_dec_ref(v___x_393_);
v_allCompletions_396_ = ((lean_object*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__0));
v_sz_397_ = lean_array_size(v_fst_394_);
v___x_398_ = ((size_t)0ULL);
v___x_399_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__1(v_uri_384_, v_pos_385_, v_caps_390_, v_fst_394_, v_sz_397_, v___x_398_, v_allCompletions_396_, v_a_391_);
lean_dec(v_fst_394_);
if (lean_obj_tag(v___x_399_) == 0)
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_433_; 
v_a_400_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_433_ == 0)
{
v___x_402_ = v___x_399_;
v_isShared_403_ = v_isSharedCheck_433_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_399_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_433_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
if (lean_obj_tag(v_a_400_) == 0)
{
lean_object* v_a_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_414_; 
lean_dec(v_snd_395_);
v_a_404_ = lean_ctor_get(v_a_400_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v_a_400_);
if (v_isSharedCheck_414_ == 0)
{
v___x_406_ = v_a_400_;
v_isShared_407_ = v_isSharedCheck_414_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_a_404_);
lean_dec(v_a_400_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_414_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_409_; 
if (v_isShared_407_ == 0)
{
v___x_409_ = v___x_406_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_a_404_);
v___x_409_ = v_reuseFailAlloc_413_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
lean_object* v___x_411_; 
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 0, v___x_409_);
v___x_411_ = v___x_402_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_409_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
}
else
{
lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_432_; 
v_a_415_ = lean_ctor_get(v_a_400_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v_a_400_);
if (v_isSharedCheck_432_ == 0)
{
v___x_417_ = v_a_400_;
v_isShared_418_ = v_isSharedCheck_432_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v_a_400_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_432_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_419_; uint8_t v___y_421_; uint8_t v___x_429_; 
v___x_419_ = l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems(v_a_415_);
lean_dec(v_a_415_);
v___x_429_ = lean_unbox(v_snd_395_);
lean_dec(v_snd_395_);
if (v___x_429_ == 0)
{
uint8_t v___x_430_; 
v___x_430_ = 1;
v___y_421_ = v___x_430_;
goto v___jp_420_;
}
else
{
uint8_t v___x_431_; 
v___x_431_ = 0;
v___y_421_ = v___x_431_;
goto v___jp_420_;
}
v___jp_420_:
{
lean_object* v___x_422_; lean_object* v___x_424_; 
v___x_422_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_422_, 0, v___x_419_);
lean_ctor_set_uint8(v___x_422_, sizeof(void*)*1, v___y_421_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 0, v___x_422_);
v___x_424_ = v___x_417_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_422_);
v___x_424_ = v_reuseFailAlloc_428_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
lean_object* v___x_426_; 
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 0, v___x_424_);
v___x_426_ = v___x_402_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v___x_424_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_441_; 
lean_dec(v_snd_395_);
v_a_434_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_441_ == 0)
{
v___x_436_ = v___x_399_;
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_399_);
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
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_Completion(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
