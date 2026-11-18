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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0(lean_object* v_x_1_, lean_object* v_x_2_){
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
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0___boxed(lean_object* v_x_9_, lean_object* v_x_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0(v_x_9_, v_x_10_);
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
v___x_24_ = l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0(v_snd_19_, v_snd_21_);
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
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v_nbuckets_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_81_ = lean_array_get_size(v_data_80_);
v___x_82_ = lean_unsigned_to_nat(2u);
v_nbuckets_83_ = lean_nat_mul(v___x_81_, v___x_82_);
v___x_84_ = lean_unsigned_to_nat(0u);
v___x_85_ = lean_box(0);
v___x_86_ = lean_mk_array(v_nbuckets_83_, v___x_85_);
v___x_87_ = lean_array_propagate_mark(v_data_80_, v___x_86_);
v___x_88_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2___redArg(v___x_84_, v_data_80_, v___x_87_);
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
lean_object* v_snd_99_; lean_object* v_fst_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_164_; 
v_snd_99_ = lean_ctor_get(v_b_92_, 1);
v_fst_100_ = lean_ctor_get(v_b_92_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v_b_92_);
if (v_isSharedCheck_164_ == 0)
{
v___x_102_ = v_b_92_;
v_isShared_103_ = v_isSharedCheck_164_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_snd_99_);
lean_inc(v_fst_100_);
lean_dec(v_b_92_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_164_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v_size_104_; lean_object* v_buckets_105_; lean_object* v_a_106_; lean_object* v_snd_108_; lean_object* v_label_113_; lean_object* v_textEdit_x3f_114_; lean_object* v___x_115_; lean_object* v___x_116_; uint64_t v___x_117_; uint64_t v___y_119_; 
v_size_104_ = lean_ctor_get(v_snd_99_, 0);
v_buckets_105_ = lean_ctor_get(v_snd_99_, 1);
v_a_106_ = lean_array_uget_borrowed(v_as_89_, v_i_91_);
v_label_113_ = lean_ctor_get(v_a_106_, 0);
v_textEdit_x3f_114_ = lean_ctor_get(v_a_106_, 4);
lean_inc(v_textEdit_x3f_114_);
lean_inc_ref(v_label_113_);
v___x_115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_115_, 0, v_label_113_);
lean_ctor_set(v___x_115_, 1, v_textEdit_x3f_114_);
v___x_116_ = lean_array_get_size(v_buckets_105_);
v___x_117_ = lean_string_hash(v_label_113_);
if (lean_obj_tag(v_textEdit_x3f_114_) == 0)
{
uint64_t v___x_159_; 
v___x_159_ = 11ULL;
v___y_119_ = v___x_159_;
goto v___jp_118_;
}
else
{
lean_object* v_val_160_; uint64_t v___x_161_; uint64_t v___x_162_; uint64_t v___x_163_; 
v_val_160_ = lean_ctor_get(v_textEdit_x3f_114_, 0);
v___x_161_ = l_Lean_Lsp_instHashableInsertReplaceEdit_hash(v_val_160_);
v___x_162_ = 13ULL;
v___x_163_ = lean_uint64_mix_hash(v___x_161_, v___x_162_);
v___y_119_ = v___x_163_;
goto v___jp_118_;
}
v___jp_107_:
{
lean_object* v___x_109_; lean_object* v___x_111_; 
lean_inc(v_a_106_);
v___x_109_ = lean_array_push(v_fst_100_, v_a_106_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 1, v_snd_108_);
lean_ctor_set(v___x_102_, 0, v___x_109_);
v___x_111_ = v___x_102_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v___x_109_);
lean_ctor_set(v_reuseFailAlloc_112_, 1, v_snd_108_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
v_a_94_ = v___x_111_;
goto v___jp_93_;
}
}
v___jp_118_:
{
uint64_t v___x_120_; uint64_t v___x_121_; uint64_t v___x_122_; uint64_t v_fold_123_; uint64_t v___x_124_; uint64_t v___x_125_; uint64_t v___x_126_; size_t v___x_127_; size_t v___x_128_; size_t v___x_129_; size_t v___x_130_; size_t v___x_131_; lean_object* v_bkt_132_; uint8_t v___x_133_; 
v___x_120_ = lean_uint64_mix_hash(v___x_117_, v___y_119_);
v___x_121_ = 32ULL;
v___x_122_ = lean_uint64_shift_right(v___x_120_, v___x_121_);
v_fold_123_ = lean_uint64_xor(v___x_120_, v___x_122_);
v___x_124_ = 16ULL;
v___x_125_ = lean_uint64_shift_right(v_fold_123_, v___x_124_);
v___x_126_ = lean_uint64_xor(v_fold_123_, v___x_125_);
v___x_127_ = lean_uint64_to_usize(v___x_126_);
v___x_128_ = lean_usize_of_nat(v___x_116_);
v___x_129_ = ((size_t)1ULL);
v___x_130_ = lean_usize_sub(v___x_128_, v___x_129_);
v___x_131_ = lean_usize_land(v___x_127_, v___x_130_);
v_bkt_132_ = lean_array_uget_borrowed(v_buckets_105_, v___x_131_);
v___x_133_ = l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg(v___x_115_, v_bkt_132_);
if (v___x_133_ == 0)
{
lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_155_; 
lean_inc_ref(v_buckets_105_);
lean_inc(v_size_104_);
v_isSharedCheck_155_ = !lean_is_exclusive(v_snd_99_);
if (v_isSharedCheck_155_ == 0)
{
lean_object* v_unused_156_; lean_object* v_unused_157_; 
v_unused_156_ = lean_ctor_get(v_snd_99_, 1);
lean_dec(v_unused_156_);
v_unused_157_ = lean_ctor_get(v_snd_99_, 0);
lean_dec(v_unused_157_);
v___x_135_ = v_snd_99_;
v_isShared_136_ = v_isSharedCheck_155_;
goto v_resetjp_134_;
}
else
{
lean_dec(v_snd_99_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_155_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v_size_x27_139_; lean_object* v___x_140_; lean_object* v_buckets_x27_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; uint8_t v___x_147_; 
v___x_137_ = lean_box(0);
v___x_138_ = lean_unsigned_to_nat(1u);
v_size_x27_139_ = lean_nat_add(v_size_104_, v___x_138_);
lean_dec(v_size_104_);
lean_inc(v_bkt_132_);
v___x_140_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_140_, 0, v___x_115_);
lean_ctor_set(v___x_140_, 1, v___x_137_);
lean_ctor_set(v___x_140_, 2, v_bkt_132_);
v_buckets_x27_141_ = lean_array_uset(v_buckets_105_, v___x_131_, v___x_140_);
v___x_142_ = lean_unsigned_to_nat(4u);
v___x_143_ = lean_nat_mul(v_size_x27_139_, v___x_142_);
v___x_144_ = lean_unsigned_to_nat(3u);
v___x_145_ = lean_nat_div(v___x_143_, v___x_144_);
lean_dec(v___x_143_);
v___x_146_ = lean_array_get_size(v_buckets_x27_141_);
v___x_147_ = lean_nat_dec_le(v___x_145_, v___x_146_);
lean_dec(v___x_145_);
if (v___x_147_ == 0)
{
lean_object* v_val_148_; lean_object* v___x_150_; 
v_val_148_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg(v_buckets_x27_141_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 1, v_val_148_);
lean_ctor_set(v___x_135_, 0, v_size_x27_139_);
v___x_150_ = v___x_135_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_size_x27_139_);
lean_ctor_set(v_reuseFailAlloc_151_, 1, v_val_148_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
v_snd_108_ = v___x_150_;
goto v___jp_107_;
}
}
else
{
lean_object* v___x_153_; 
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 1, v_buckets_x27_141_);
lean_ctor_set(v___x_135_, 0, v_size_x27_139_);
v___x_153_ = v___x_135_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_size_x27_139_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v_buckets_x27_141_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
v_snd_108_ = v___x_153_;
goto v___jp_107_;
}
}
}
}
else
{
lean_object* v___x_158_; 
lean_dec_ref_known(v___x_115_, 2);
lean_del_object(v___x_102_);
v___x_158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_158_, 0, v_fst_100_);
lean_ctor_set(v___x_158_, 1, v_snd_99_);
v_a_94_ = v___x_158_;
goto v___jp_93_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__2___boxed(lean_object* v_as_165_, lean_object* v_sz_166_, lean_object* v_i_167_, lean_object* v_b_168_){
_start:
{
size_t v_sz_boxed_169_; size_t v_i_boxed_170_; lean_object* v_res_171_; 
v_sz_boxed_169_ = lean_unbox_usize(v_sz_166_);
lean_dec(v_sz_166_);
v_i_boxed_170_ = lean_unbox_usize(v_i_167_);
lean_dec(v_i_167_);
v_res_171_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__2(v_as_165_, v_sz_boxed_169_, v_i_boxed_170_, v_b_168_);
lean_dec_ref(v_as_165_);
return v_res_171_;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__1(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_174_ = lean_box(0);
v___x_175_ = lean_unsigned_to_nat(16u);
v___x_176_ = lean_mk_array(v___x_175_, v___x_174_);
return v___x_176_;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__2(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v_index_179_; 
v___x_177_ = lean_obj_once(&l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__1, &l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__1_once, _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__1);
v___x_178_ = lean_unsigned_to_nat(0u);
v_index_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_index_179_, 0, v___x_178_);
lean_ctor_set(v_index_179_, 1, v___x_177_);
return v_index_179_;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__3(void){
_start:
{
lean_object* v_index_180_; lean_object* v_r_181_; lean_object* v___x_182_; 
v_index_180_ = lean_obj_once(&l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__2, &l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__2_once, _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__2);
v_r_181_ = ((lean_object*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__0));
v___x_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_182_, 0, v_r_181_);
lean_ctor_set(v___x_182_, 1, v_index_180_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems(lean_object* v_items_183_){
_start:
{
lean_object* v___x_184_; size_t v_sz_185_; size_t v___x_186_; lean_object* v___x_187_; lean_object* v_fst_188_; 
v___x_184_ = lean_obj_once(&l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__3, &l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__3_once, _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__3);
v_sz_185_ = lean_array_size(v_items_183_);
v___x_186_ = ((size_t)0ULL);
v___x_187_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__2(v_items_183_, v_sz_185_, v___x_186_, v___x_184_);
v_fst_188_ = lean_ctor_get(v___x_187_, 0);
lean_inc(v_fst_188_);
lean_dec_ref(v___x_187_);
return v_fst_188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___boxed(lean_object* v_items_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems(v_items_189_);
lean_dec_ref(v_items_189_);
return v_res_190_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0(lean_object* v_00_u03b2_191_, lean_object* v_a_192_, lean_object* v_x_193_){
_start:
{
uint8_t v___x_194_; 
v___x_194_ = l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg(v_a_192_, v_x_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___boxed(lean_object* v_00_u03b2_195_, lean_object* v_a_196_, lean_object* v_x_197_){
_start:
{
uint8_t v_res_198_; lean_object* v_r_199_; 
v_res_198_ = l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0(v_00_u03b2_195_, v_a_196_, v_x_197_);
lean_dec(v_x_197_);
lean_dec_ref(v_a_196_);
v_r_199_ = lean_box(v_res_198_);
return v_r_199_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1(lean_object* v_00_u03b2_200_, lean_object* v_data_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg(v_data_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2(lean_object* v_00_u03b2_203_, lean_object* v_i_204_, lean_object* v_source_205_, lean_object* v_target_206_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2___redArg(v_i_204_, v_source_205_, v_target_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_208_, lean_object* v_x_209_, lean_object* v_x_210_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__3___redArg(v_x_209_, v_x_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__0(lean_object* v_uri_212_, lean_object* v_pos_213_, lean_object* v_caps_214_, lean_object* v_as_215_, size_t v_sz_216_, size_t v_i_217_, lean_object* v_b_218_, lean_object* v___y_219_){
_start:
{
lean_object* v_a_222_; lean_object* v_completions_226_; uint8_t v___x_231_; 
v___x_231_ = lean_usize_dec_lt(v_i_217_, v_sz_216_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; lean_object* v___x_233_; 
lean_dec_ref(v_caps_214_);
lean_dec_ref(v_pos_213_);
lean_dec_ref(v_uri_212_);
v___x_232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_232_, 0, v_b_218_);
v___x_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
return v___x_233_;
}
else
{
lean_object* v_a_234_; lean_object* v_fst_235_; lean_object* v_snd_236_; lean_object* v_allCompletions_237_; lean_object* v___x_238_; 
v_a_234_ = lean_array_uget_borrowed(v_as_215_, v_i_217_);
v_fst_235_ = lean_ctor_get(v_a_234_, 0);
v_snd_236_ = lean_ctor_get(v_a_234_, 1);
v_allCompletions_237_ = ((lean_object*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__0));
v___x_238_ = l_Lean_Server_CancellableM_checkCancelled(v___y_219_);
if (lean_obj_tag(v___x_238_) == 0)
{
lean_object* v_a_239_; 
v_a_239_ = lean_ctor_get(v___x_238_, 0);
lean_inc(v_a_239_);
lean_dec_ref_known(v___x_238_, 1);
if (lean_obj_tag(v_a_239_) == 0)
{
lean_object* v_a_240_; 
lean_dec_ref(v_b_218_);
lean_dec_ref(v_caps_214_);
lean_dec_ref(v_pos_213_);
lean_dec_ref(v_uri_212_);
v_a_240_ = lean_ctor_get(v_a_239_, 0);
lean_inc(v_a_240_);
lean_dec_ref_known(v_a_239_, 1);
v_a_222_ = v_a_240_;
goto v___jp_221_;
}
else
{
lean_object* v_info_241_; 
lean_dec_ref_known(v_a_239_, 1);
v_info_241_ = lean_ctor_get(v_fst_235_, 2);
switch(lean_obj_tag(v_info_241_))
{
case 1:
{
lean_object* v_hoverInfo_242_; lean_object* v_ctx_243_; lean_object* v_stx_244_; lean_object* v_id_245_; uint8_t v_danglingDot_246_; lean_object* v_lctx_247_; lean_object* v___x_248_; 
v_hoverInfo_242_ = lean_ctor_get(v_fst_235_, 0);
v_ctx_243_ = lean_ctor_get(v_fst_235_, 1);
v_stx_244_ = lean_ctor_get(v_info_241_, 0);
v_id_245_ = lean_ctor_get(v_info_241_, 1);
v_danglingDot_246_ = lean_ctor_get_uint8(v_info_241_, sizeof(void*)*4);
v_lctx_247_ = lean_ctor_get(v_info_241_, 2);
lean_inc(v_hoverInfo_242_);
lean_inc(v_id_245_);
lean_inc(v_stx_244_);
lean_inc_ref(v_lctx_247_);
lean_inc_ref(v_ctx_243_);
lean_inc(v_snd_236_);
lean_inc_ref(v_pos_213_);
lean_inc_ref(v_uri_212_);
v___x_248_ = l_Lean_Server_Completion_idCompletion(v_uri_212_, v_pos_213_, v_snd_236_, v_ctx_243_, v_lctx_247_, v_stx_244_, v_id_245_, v_hoverInfo_242_, v_danglingDot_246_, v___y_219_);
if (lean_obj_tag(v___x_248_) == 0)
{
lean_object* v_a_249_; 
v_a_249_ = lean_ctor_get(v___x_248_, 0);
lean_inc(v_a_249_);
lean_dec_ref_known(v___x_248_, 1);
if (lean_obj_tag(v_a_249_) == 0)
{
lean_object* v_a_250_; 
lean_dec_ref(v_b_218_);
lean_dec_ref(v_caps_214_);
lean_dec_ref(v_pos_213_);
lean_dec_ref(v_uri_212_);
v_a_250_ = lean_ctor_get(v_a_249_, 0);
lean_inc(v_a_250_);
lean_dec_ref_known(v_a_249_, 1);
v_a_222_ = v_a_250_;
goto v___jp_221_;
}
else
{
lean_object* v_a_251_; 
v_a_251_ = lean_ctor_get(v_a_249_, 0);
lean_inc(v_a_251_);
lean_dec_ref_known(v_a_249_, 1);
v_completions_226_ = v_a_251_;
goto v___jp_225_;
}
}
else
{
lean_dec_ref(v_b_218_);
lean_dec_ref(v_caps_214_);
lean_dec_ref(v_pos_213_);
lean_dec_ref(v_uri_212_);
return v___x_248_;
}
}
case 0:
{
lean_object* v_ctx_252_; lean_object* v_termInfo_253_; lean_object* v___x_254_; 
v_ctx_252_ = lean_ctor_get(v_fst_235_, 1);
v_termInfo_253_ = lean_ctor_get(v_info_241_, 0);
lean_inc_ref(v_termInfo_253_);
lean_inc_ref(v_ctx_252_);
lean_inc(v_snd_236_);
lean_inc_ref(v_pos_213_);
lean_inc_ref(v_uri_212_);
v___x_254_ = l_Lean_Server_Completion_dotCompletion(v_uri_212_, v_pos_213_, v_snd_236_, v_ctx_252_, v_termInfo_253_, v___y_219_);
if (lean_obj_tag(v___x_254_) == 0)
{
lean_object* v_a_255_; 
v_a_255_ = lean_ctor_get(v___x_254_, 0);
lean_inc(v_a_255_);
lean_dec_ref_known(v___x_254_, 1);
if (lean_obj_tag(v_a_255_) == 0)
{
lean_object* v_a_256_; 
lean_dec_ref(v_b_218_);
lean_dec_ref(v_caps_214_);
lean_dec_ref(v_pos_213_);
lean_dec_ref(v_uri_212_);
v_a_256_ = lean_ctor_get(v_a_255_, 0);
lean_inc(v_a_256_);
lean_dec_ref_known(v_a_255_, 1);
v_a_222_ = v_a_256_;
goto v___jp_221_;
}
else
{
lean_object* v_a_257_; 
v_a_257_ = lean_ctor_get(v_a_255_, 0);
lean_inc(v_a_257_);
lean_dec_ref_known(v_a_255_, 1);
v_completions_226_ = v_a_257_;
goto v___jp_225_;
}
}
else
{
lean_dec_ref(v_b_218_);
lean_dec_ref(v_caps_214_);
lean_dec_ref(v_pos_213_);
lean_dec_ref(v_uri_212_);
return v___x_254_;
}
}
case 2:
{
lean_object* v_ctx_258_; lean_object* v_id_259_; lean_object* v_lctx_260_; lean_object* v_expectedType_x3f_261_; lean_object* v___x_262_; 
v_ctx_258_ = lean_ctor_get(v_fst_235_, 1);
v_id_259_ = lean_ctor_get(v_info_241_, 1);
v_lctx_260_ = lean_ctor_get(v_info_241_, 2);
v_expectedType_x3f_261_ = lean_ctor_get(v_info_241_, 3);
lean_inc(v_expectedType_x3f_261_);
lean_inc(v_id_259_);
lean_inc_ref(v_lctx_260_);
lean_inc_ref(v_ctx_258_);
lean_inc(v_snd_236_);
lean_inc_ref(v_pos_213_);
lean_inc_ref(v_uri_212_);
v___x_262_ = l_Lean_Server_Completion_dotIdCompletion(v_uri_212_, v_pos_213_, v_snd_236_, v_ctx_258_, v_lctx_260_, v_id_259_, v_expectedType_x3f_261_, v___y_219_);
if (lean_obj_tag(v___x_262_) == 0)
{
lean_object* v_a_263_; 
v_a_263_ = lean_ctor_get(v___x_262_, 0);
lean_inc(v_a_263_);
lean_dec_ref_known(v___x_262_, 1);
if (lean_obj_tag(v_a_263_) == 0)
{
lean_object* v_a_264_; 
lean_dec_ref(v_b_218_);
lean_dec_ref(v_caps_214_);
lean_dec_ref(v_pos_213_);
lean_dec_ref(v_uri_212_);
v_a_264_ = lean_ctor_get(v_a_263_, 0);
lean_inc(v_a_264_);
lean_dec_ref_known(v_a_263_, 1);
v_a_222_ = v_a_264_;
goto v___jp_221_;
}
else
{
lean_object* v_a_265_; 
v_a_265_ = lean_ctor_get(v_a_263_, 0);
lean_inc(v_a_265_);
lean_dec_ref_known(v_a_263_, 1);
v_completions_226_ = v_a_265_;
goto v___jp_225_;
}
}
else
{
lean_dec_ref(v_b_218_);
lean_dec_ref(v_caps_214_);
lean_dec_ref(v_pos_213_);
lean_dec_ref(v_uri_212_);
return v___x_262_;
}
}
case 3:
{
lean_object* v_ctx_266_; lean_object* v_id_267_; lean_object* v_lctx_268_; lean_object* v_structName_269_; lean_object* v___x_270_; 
v_ctx_266_ = lean_ctor_get(v_fst_235_, 1);
v_id_267_ = lean_ctor_get(v_info_241_, 1);
v_lctx_268_ = lean_ctor_get(v_info_241_, 2);
v_structName_269_ = lean_ctor_get(v_info_241_, 3);
lean_inc(v_structName_269_);
lean_inc(v_id_267_);
lean_inc_ref(v_lctx_268_);
lean_inc_ref(v_ctx_266_);
lean_inc(v_snd_236_);
lean_inc_ref(v_pos_213_);
lean_inc_ref(v_uri_212_);
v___x_270_ = l_Lean_Server_Completion_fieldIdCompletion(v_uri_212_, v_pos_213_, v_snd_236_, v_ctx_266_, v_lctx_268_, v_id_267_, v_structName_269_, v___y_219_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v_a_271_; 
v_a_271_ = lean_ctor_get(v___x_270_, 0);
lean_inc(v_a_271_);
lean_dec_ref_known(v___x_270_, 1);
if (lean_obj_tag(v_a_271_) == 0)
{
lean_object* v_a_272_; 
lean_dec_ref(v_b_218_);
lean_dec_ref(v_caps_214_);
lean_dec_ref(v_pos_213_);
lean_dec_ref(v_uri_212_);
v_a_272_ = lean_ctor_get(v_a_271_, 0);
lean_inc(v_a_272_);
lean_dec_ref_known(v_a_271_, 1);
v_a_222_ = v_a_272_;
goto v___jp_221_;
}
else
{
lean_object* v_a_273_; 
v_a_273_ = lean_ctor_get(v_a_271_, 0);
lean_inc(v_a_273_);
lean_dec_ref_known(v_a_271_, 1);
v_completions_226_ = v_a_273_;
goto v___jp_225_;
}
}
else
{
lean_dec_ref(v_b_218_);
lean_dec_ref(v_caps_214_);
lean_dec_ref(v_pos_213_);
lean_dec_ref(v_uri_212_);
return v___x_270_;
}
}
case 5:
{
lean_object* v_ctx_274_; lean_object* v_stx_275_; lean_object* v___x_276_; 
v_ctx_274_ = lean_ctor_get(v_fst_235_, 1);
v_stx_275_ = lean_ctor_get(v_info_241_, 0);
lean_inc_ref(v_caps_214_);
lean_inc(v_stx_275_);
lean_inc_ref(v_ctx_274_);
lean_inc(v_snd_236_);
lean_inc_ref(v_pos_213_);
lean_inc_ref(v_uri_212_);
v___x_276_ = l_Lean_Server_Completion_optionCompletion(v_uri_212_, v_pos_213_, v_snd_236_, v_ctx_274_, v_stx_275_, v_caps_214_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v_a_277_; 
v_a_277_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_a_277_);
lean_dec_ref_known(v___x_276_, 1);
v_completions_226_ = v_a_277_;
goto v___jp_225_;
}
else
{
lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_285_; 
lean_dec_ref(v_b_218_);
lean_dec_ref(v_caps_214_);
lean_dec_ref(v_pos_213_);
lean_dec_ref(v_uri_212_);
v_a_278_ = lean_ctor_get(v___x_276_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_285_ == 0)
{
v___x_280_ = v___x_276_;
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v___x_276_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
if (v_isShared_281_ == 0)
{
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_a_278_);
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
case 6:
{
lean_object* v_ctx_286_; lean_object* v_partialId_287_; lean_object* v___x_288_; 
v_ctx_286_ = lean_ctor_get(v_fst_235_, 1);
v_partialId_287_ = lean_ctor_get(v_info_241_, 1);
lean_inc_ref(v_caps_214_);
lean_inc(v_partialId_287_);
lean_inc_ref(v_ctx_286_);
lean_inc(v_snd_236_);
lean_inc_ref(v_pos_213_);
lean_inc_ref(v_uri_212_);
v___x_288_ = l_Lean_Server_Completion_errorNameCompletion(v_uri_212_, v_pos_213_, v_snd_236_, v_ctx_286_, v_partialId_287_, v_caps_214_);
if (lean_obj_tag(v___x_288_) == 0)
{
lean_object* v_a_289_; 
v_a_289_ = lean_ctor_get(v___x_288_, 0);
lean_inc(v_a_289_);
lean_dec_ref_known(v___x_288_, 1);
v_completions_226_ = v_a_289_;
goto v___jp_225_;
}
else
{
lean_object* v_a_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_297_; 
lean_dec_ref(v_b_218_);
lean_dec_ref(v_caps_214_);
lean_dec_ref(v_pos_213_);
lean_dec_ref(v_uri_212_);
v_a_290_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_297_ == 0)
{
v___x_292_ = v___x_288_;
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_a_290_);
lean_dec(v___x_288_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_295_; 
if (v_isShared_293_ == 0)
{
v___x_295_ = v___x_292_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_a_290_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
case 7:
{
lean_object* v_id_x3f_298_; uint8_t v_danglingDot_299_; lean_object* v_scopeNames_300_; lean_object* v___x_301_; 
v_id_x3f_298_ = lean_ctor_get(v_info_241_, 1);
v_danglingDot_299_ = lean_ctor_get_uint8(v_info_241_, sizeof(void*)*3);
v_scopeNames_300_ = lean_ctor_get(v_info_241_, 2);
lean_inc(v_scopeNames_300_);
lean_inc(v_id_x3f_298_);
lean_inc(v_snd_236_);
lean_inc_ref(v_pos_213_);
lean_inc_ref(v_uri_212_);
v___x_301_ = l_Lean_Server_Completion_endSectionCompletion(v_uri_212_, v_pos_213_, v_snd_236_, v_id_x3f_298_, v_danglingDot_299_, v_scopeNames_300_);
if (lean_obj_tag(v___x_301_) == 0)
{
lean_object* v_a_302_; 
v_a_302_ = lean_ctor_get(v___x_301_, 0);
lean_inc(v_a_302_);
lean_dec_ref_known(v___x_301_, 1);
v_completions_226_ = v_a_302_;
goto v___jp_225_;
}
else
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_310_; 
lean_dec_ref(v_b_218_);
lean_dec_ref(v_caps_214_);
lean_dec_ref(v_pos_213_);
lean_dec_ref(v_uri_212_);
v_a_303_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_310_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_310_ == 0)
{
v___x_305_ = v___x_301_;
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_301_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_308_; 
if (v_isShared_306_ == 0)
{
v___x_308_ = v___x_305_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_a_303_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
}
case 8:
{
lean_object* v_ctx_311_; lean_object* v___x_312_; 
v_ctx_311_ = lean_ctor_get(v_fst_235_, 1);
lean_inc_ref(v_ctx_311_);
lean_inc(v_snd_236_);
lean_inc_ref(v_pos_213_);
lean_inc_ref(v_uri_212_);
v___x_312_ = l_Lean_Server_Completion_tacticCompletion(v_uri_212_, v_pos_213_, v_snd_236_, v_ctx_311_);
if (lean_obj_tag(v___x_312_) == 0)
{
lean_object* v_a_313_; 
v_a_313_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_a_313_);
lean_dec_ref_known(v___x_312_, 1);
v_completions_226_ = v_a_313_;
goto v___jp_225_;
}
else
{
lean_object* v_a_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_321_; 
lean_dec_ref(v_b_218_);
lean_dec_ref(v_caps_214_);
lean_dec_ref(v_pos_213_);
lean_dec_ref(v_uri_212_);
v_a_314_ = lean_ctor_get(v___x_312_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_321_ == 0)
{
v___x_316_ = v___x_312_;
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_a_314_);
lean_dec(v___x_312_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_319_; 
if (v_isShared_317_ == 0)
{
v___x_319_ = v___x_316_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_a_314_);
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
default: 
{
v_completions_226_ = v_allCompletions_237_;
goto v___jp_225_;
}
}
}
}
else
{
lean_object* v_a_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_329_; 
lean_dec_ref(v_b_218_);
lean_dec_ref(v_caps_214_);
lean_dec_ref(v_pos_213_);
lean_dec_ref(v_uri_212_);
v_a_322_ = lean_ctor_get(v___x_238_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_329_ == 0)
{
v___x_324_ = v___x_238_;
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_a_322_);
lean_dec(v___x_238_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_327_; 
if (v_isShared_325_ == 0)
{
v___x_327_ = v___x_324_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_a_322_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
v___jp_221_:
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_223_, 0, v_a_222_);
v___x_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
return v___x_224_;
}
v___jp_225_:
{
lean_object* v___x_227_; size_t v___x_228_; size_t v___x_229_; 
v___x_227_ = l_Array_append___redArg(v_b_218_, v_completions_226_);
lean_dec_ref(v_completions_226_);
v___x_228_ = ((size_t)1ULL);
v___x_229_ = lean_usize_add(v_i_217_, v___x_228_);
v_i_217_ = v___x_229_;
v_b_218_ = v___x_227_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__0___boxed(lean_object* v_uri_330_, lean_object* v_pos_331_, lean_object* v_caps_332_, lean_object* v_as_333_, lean_object* v_sz_334_, lean_object* v_i_335_, lean_object* v_b_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
size_t v_sz_boxed_339_; size_t v_i_boxed_340_; lean_object* v_res_341_; 
v_sz_boxed_339_ = lean_unbox_usize(v_sz_334_);
lean_dec(v_sz_334_);
v_i_boxed_340_ = lean_unbox_usize(v_i_335_);
lean_dec(v_i_335_);
v_res_341_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__0(v_uri_330_, v_pos_331_, v_caps_332_, v_as_333_, v_sz_boxed_339_, v_i_boxed_340_, v_b_336_, v___y_337_);
lean_dec_ref(v___y_337_);
lean_dec_ref(v_as_333_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__1(lean_object* v_uri_342_, lean_object* v_pos_343_, lean_object* v_caps_344_, lean_object* v_as_345_, size_t v_sz_346_, size_t v_i_347_, lean_object* v_b_348_, lean_object* v___y_349_){
_start:
{
uint8_t v___x_351_; 
v___x_351_ = lean_usize_dec_lt(v_i_347_, v_sz_346_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; lean_object* v___x_353_; 
lean_dec_ref(v_caps_344_);
lean_dec_ref(v_pos_343_);
lean_dec_ref(v_uri_342_);
v___x_352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_352_, 0, v_b_348_);
v___x_353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
return v___x_353_;
}
else
{
lean_object* v_a_354_; size_t v_sz_355_; size_t v___x_356_; lean_object* v___x_357_; 
v_a_354_ = lean_array_uget_borrowed(v_as_345_, v_i_347_);
v_sz_355_ = lean_array_size(v_a_354_);
v___x_356_ = ((size_t)0ULL);
lean_inc_ref(v_caps_344_);
lean_inc_ref(v_pos_343_);
lean_inc_ref(v_uri_342_);
v___x_357_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__0(v_uri_342_, v_pos_343_, v_caps_344_, v_a_354_, v_sz_355_, v___x_356_, v_b_348_, v___y_349_);
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v_a_358_; 
v_a_358_ = lean_ctor_get(v___x_357_, 0);
if (lean_obj_tag(v_a_358_) == 0)
{
lean_dec_ref(v_caps_344_);
lean_dec_ref(v_pos_343_);
lean_dec_ref(v_uri_342_);
return v___x_357_;
}
else
{
lean_object* v_a_359_; lean_object* v___x_360_; lean_object* v___x_361_; uint8_t v___x_362_; 
v_a_359_ = lean_ctor_get(v_a_358_, 0);
v___x_360_ = lean_array_get_size(v_a_359_);
v___x_361_ = lean_unsigned_to_nat(0u);
v___x_362_ = lean_nat_dec_eq(v___x_360_, v___x_361_);
if (v___x_362_ == 0)
{
lean_dec_ref(v_caps_344_);
lean_dec_ref(v_pos_343_);
lean_dec_ref(v_uri_342_);
return v___x_357_;
}
else
{
size_t v___x_363_; size_t v___x_364_; 
lean_inc(v_a_359_);
lean_dec_ref_known(v___x_357_, 1);
v___x_363_ = ((size_t)1ULL);
v___x_364_ = lean_usize_add(v_i_347_, v___x_363_);
v_i_347_ = v___x_364_;
v_b_348_ = v_a_359_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_caps_344_);
lean_dec_ref(v_pos_343_);
lean_dec_ref(v_uri_342_);
return v___x_357_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__1___boxed(lean_object* v_uri_366_, lean_object* v_pos_367_, lean_object* v_caps_368_, lean_object* v_as_369_, lean_object* v_sz_370_, lean_object* v_i_371_, lean_object* v_b_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
size_t v_sz_boxed_375_; size_t v_i_boxed_376_; lean_object* v_res_377_; 
v_sz_boxed_375_ = lean_unbox_usize(v_sz_370_);
lean_dec(v_sz_370_);
v_i_boxed_376_ = lean_unbox_usize(v_i_371_);
lean_dec(v_i_371_);
v_res_377_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__1(v_uri_366_, v_pos_367_, v_caps_368_, v_as_369_, v_sz_boxed_375_, v_i_boxed_376_, v_b_372_, v___y_373_);
lean_dec_ref(v___y_373_);
lean_dec_ref(v_as_369_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_find_x3f(lean_object* v_uri_378_, lean_object* v_pos_379_, lean_object* v_fileMap_380_, lean_object* v_hoverPos_381_, lean_object* v_cmdStx_382_, lean_object* v_infoTree_383_, lean_object* v_caps_384_, lean_object* v_a_385_){
_start:
{
lean_object* v___x_387_; lean_object* v_fst_388_; lean_object* v_snd_389_; lean_object* v_allCompletions_390_; size_t v_sz_391_; size_t v___x_392_; lean_object* v___x_393_; 
v___x_387_ = l_Lean_Server_Completion_findPrioritizedCompletionPartitionsAt(v_fileMap_380_, v_hoverPos_381_, v_cmdStx_382_, v_infoTree_383_);
v_fst_388_ = lean_ctor_get(v___x_387_, 0);
lean_inc(v_fst_388_);
v_snd_389_ = lean_ctor_get(v___x_387_, 1);
lean_inc(v_snd_389_);
lean_dec_ref(v___x_387_);
v_allCompletions_390_ = ((lean_object*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__0));
v_sz_391_ = lean_array_size(v_fst_388_);
v___x_392_ = ((size_t)0ULL);
v___x_393_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__1(v_uri_378_, v_pos_379_, v_caps_384_, v_fst_388_, v_sz_391_, v___x_392_, v_allCompletions_390_, v_a_385_);
lean_dec(v_fst_388_);
if (lean_obj_tag(v___x_393_) == 0)
{
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_427_; 
v_a_394_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_427_ == 0)
{
v___x_396_ = v___x_393_;
v_isShared_397_ = v_isSharedCheck_427_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v___x_393_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_427_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
if (lean_obj_tag(v_a_394_) == 0)
{
lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_408_; 
lean_dec(v_snd_389_);
v_a_398_ = lean_ctor_get(v_a_394_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v_a_394_);
if (v_isSharedCheck_408_ == 0)
{
v___x_400_ = v_a_394_;
v_isShared_401_ = v_isSharedCheck_408_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v_a_394_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_408_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_403_; 
if (v_isShared_401_ == 0)
{
v___x_403_ = v___x_400_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_a_398_);
v___x_403_ = v_reuseFailAlloc_407_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
lean_object* v___x_405_; 
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 0, v___x_403_);
v___x_405_ = v___x_396_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_403_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
else
{
lean_object* v_a_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_426_; 
v_a_409_ = lean_ctor_get(v_a_394_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v_a_394_);
if (v_isSharedCheck_426_ == 0)
{
v___x_411_ = v_a_394_;
v_isShared_412_ = v_isSharedCheck_426_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_a_409_);
lean_dec(v_a_394_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_426_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_413_; uint8_t v___y_415_; uint8_t v___x_423_; 
v___x_413_ = l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems(v_a_409_);
lean_dec(v_a_409_);
v___x_423_ = lean_unbox(v_snd_389_);
lean_dec(v_snd_389_);
if (v___x_423_ == 0)
{
uint8_t v___x_424_; 
v___x_424_ = 1;
v___y_415_ = v___x_424_;
goto v___jp_414_;
}
else
{
uint8_t v___x_425_; 
v___x_425_ = 0;
v___y_415_ = v___x_425_;
goto v___jp_414_;
}
v___jp_414_:
{
lean_object* v___x_416_; lean_object* v___x_418_; 
v___x_416_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_416_, 0, v___x_413_);
lean_ctor_set_uint8(v___x_416_, sizeof(void*)*1, v___y_415_);
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 0, v___x_416_);
v___x_418_ = v___x_411_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_416_);
v___x_418_ = v_reuseFailAlloc_422_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
lean_object* v___x_420_; 
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 0, v___x_418_);
v___x_420_ = v___x_396_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_418_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_435_; 
lean_dec(v_snd_389_);
v_a_428_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_435_ == 0)
{
v___x_430_ = v___x_393_;
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_393_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_428_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_find_x3f___boxed(lean_object* v_uri_436_, lean_object* v_pos_437_, lean_object* v_fileMap_438_, lean_object* v_hoverPos_439_, lean_object* v_cmdStx_440_, lean_object* v_infoTree_441_, lean_object* v_caps_442_, lean_object* v_a_443_, lean_object* v_a_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Lean_Server_Completion_find_x3f(v_uri_436_, v_pos_437_, v_fileMap_438_, v_hoverPos_439_, v_cmdStx_440_, v_infoTree_441_, v_caps_442_, v_a_443_);
lean_dec_ref(v_a_443_);
return v_res_445_;
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
