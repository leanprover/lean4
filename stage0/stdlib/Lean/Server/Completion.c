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
uint8_t l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0(lean_object* v_x_1_, lean_object* v_x_2_){
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
LEAN_EXPORT void l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1_ = stack[0].m_obj;
lean_object* v_x_2_ = stack[1].m_obj;
uint8_t v_res_9_;
v_res_9_ = l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0(v_x_1_, v_x_2_);
stack->m_num = v_res_9_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0___boxed(lean_object* v_x_10_, lean_object* v_x_11_){
_start:
{
uint8_t v_res_12_; lean_object* v_r_13_; 
v_res_12_ = l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0(v_x_10_, v_x_11_);
lean_dec(v_x_11_);
lean_dec(v_x_10_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg(lean_object* v_a_14_, lean_object* v_x_15_){
_start:
{
if (lean_obj_tag(v_x_15_) == 0)
{
uint8_t v___x_16_; 
v___x_16_ = 0;
return v___x_16_;
}
else
{
lean_object* v_key_17_; lean_object* v_tail_18_; lean_object* v_fst_19_; lean_object* v_snd_20_; lean_object* v_fst_21_; lean_object* v_snd_22_; uint8_t v___x_23_; 
v_key_17_ = lean_ctor_get(v_x_15_, 0);
v_tail_18_ = lean_ctor_get(v_x_15_, 2);
v_fst_19_ = lean_ctor_get(v_key_17_, 0);
v_snd_20_ = lean_ctor_get(v_key_17_, 1);
v_fst_21_ = lean_ctor_get(v_a_14_, 0);
v_snd_22_ = lean_ctor_get(v_a_14_, 1);
v___x_23_ = lean_string_dec_eq(v_fst_19_, v_fst_21_);
if (v___x_23_ == 0)
{
v_x_15_ = v_tail_18_;
goto _start;
}
else
{
uint8_t v___x_25_; 
v___x_25_ = l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0(v_snd_20_, v_snd_22_);
if (v___x_25_ == 0)
{
v_x_15_ = v_tail_18_;
goto _start;
}
else
{
return v___x_25_;
}
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_14_ = stack[0].m_obj;
lean_object* v_x_15_ = stack[1].m_obj;
uint8_t v_res_27_;
v_res_27_ = l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg(v_a_14_, v_x_15_);
stack->m_num = v_res_27_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg___boxed(lean_object* v_a_28_, lean_object* v_x_29_){
_start:
{
uint8_t v_res_30_; lean_object* v_r_31_; 
v_res_30_ = l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg(v_a_28_, v_x_29_);
lean_dec(v_x_29_);
lean_dec_ref(v_a_28_);
v_r_31_ = lean_box(v_res_30_);
return v_r_31_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__3___redArg(lean_object* v_x_32_, lean_object* v_x_33_){
_start:
{
if (lean_obj_tag(v_x_33_) == 0)
{
return v_x_32_;
}
else
{
lean_object* v_key_34_; lean_object* v_value_35_; lean_object* v_tail_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_69_; 
v_key_34_ = lean_ctor_get(v_x_33_, 0);
v_value_35_ = lean_ctor_get(v_x_33_, 1);
v_tail_36_ = lean_ctor_get(v_x_33_, 2);
v_isSharedCheck_69_ = !lean_is_exclusive(v_x_33_);
if (v_isSharedCheck_69_ == 0)
{
v___x_38_ = v_x_33_;
v_isShared_39_ = v_isSharedCheck_69_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_tail_36_);
lean_inc(v_value_35_);
lean_inc(v_key_34_);
lean_dec(v_x_33_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_69_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v_fst_40_; lean_object* v_snd_41_; lean_object* v___x_42_; uint64_t v___x_43_; uint64_t v___y_45_; 
v_fst_40_ = lean_ctor_get(v_key_34_, 0);
v_snd_41_ = lean_ctor_get(v_key_34_, 1);
v___x_42_ = lean_array_get_size(v_x_32_);
v___x_43_ = lean_string_hash(v_fst_40_);
if (lean_obj_tag(v_snd_41_) == 0)
{
uint64_t v___x_64_; 
v___x_64_ = 11ULL;
v___y_45_ = v___x_64_;
goto v___jp_44_;
}
else
{
lean_object* v_val_65_; uint64_t v___x_66_; uint64_t v___x_67_; uint64_t v___x_68_; 
v_val_65_ = lean_ctor_get(v_snd_41_, 0);
v___x_66_ = l_Lean_Lsp_instHashableInsertReplaceEdit_hash(v_val_65_);
v___x_67_ = 13ULL;
v___x_68_ = lean_uint64_mix_hash(v___x_66_, v___x_67_);
v___y_45_ = v___x_68_;
goto v___jp_44_;
}
v___jp_44_:
{
uint64_t v___x_46_; uint64_t v___x_47_; uint64_t v___x_48_; uint64_t v_fold_49_; uint64_t v___x_50_; uint64_t v___x_51_; uint64_t v___x_52_; size_t v___x_53_; size_t v___x_54_; size_t v___x_55_; size_t v___x_56_; size_t v___x_57_; lean_object* v___x_58_; lean_object* v___x_60_; 
v___x_46_ = lean_uint64_mix_hash(v___x_43_, v___y_45_);
v___x_47_ = 32ULL;
v___x_48_ = lean_uint64_shift_right(v___x_46_, v___x_47_);
v_fold_49_ = lean_uint64_xor(v___x_46_, v___x_48_);
v___x_50_ = 16ULL;
v___x_51_ = lean_uint64_shift_right(v_fold_49_, v___x_50_);
v___x_52_ = lean_uint64_xor(v_fold_49_, v___x_51_);
v___x_53_ = lean_uint64_to_usize(v___x_52_);
v___x_54_ = lean_usize_of_nat(v___x_42_);
v___x_55_ = ((size_t)1ULL);
v___x_56_ = lean_usize_sub(v___x_54_, v___x_55_);
v___x_57_ = lean_usize_land(v___x_53_, v___x_56_);
v___x_58_ = lean_array_uget_borrowed(v_x_32_, v___x_57_);
lean_inc(v___x_58_);
if (v_isShared_39_ == 0)
{
lean_ctor_set(v___x_38_, 2, v___x_58_);
v___x_60_ = v___x_38_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_63_; 
v_reuseFailAlloc_63_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_63_, 0, v_key_34_);
lean_ctor_set(v_reuseFailAlloc_63_, 1, v_value_35_);
lean_ctor_set(v_reuseFailAlloc_63_, 2, v___x_58_);
v___x_60_ = v_reuseFailAlloc_63_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
lean_object* v___x_61_; 
v___x_61_ = lean_array_uset(v_x_32_, v___x_57_, v___x_60_);
v_x_32_ = v___x_61_;
v_x_33_ = v_tail_36_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2___redArg(lean_object* v_i_70_, lean_object* v_source_71_, lean_object* v_target_72_){
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
v_target_78_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__3___redArg(v_target_72_, v_es_75_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg(lean_object* v_data_82_){
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
v___x_90_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2___redArg(v___x_86_, v_data_82_, v___x_89_);
return v___x_90_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__2(lean_object* v_as_91_, size_t v_sz_92_, size_t v_i_93_, lean_object* v_b_94_){
_start:
{
lean_object* v_a_96_; uint8_t v___x_100_; 
v___x_100_ = lean_usize_dec_lt(v_i_93_, v_sz_92_);
if (v___x_100_ == 0)
{
return v_b_94_;
}
else
{
lean_object* v_snd_101_; lean_object* v_fst_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_173_; 
v_snd_101_ = lean_ctor_get(v_b_94_, 1);
v_fst_102_ = lean_ctor_get(v_b_94_, 0);
v_isSharedCheck_173_ = !lean_is_exclusive(v_b_94_);
if (v_isSharedCheck_173_ == 0)
{
v___x_104_ = v_b_94_;
v_isShared_105_ = v_isSharedCheck_173_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_snd_101_);
lean_inc(v_fst_102_);
lean_dec(v_b_94_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_173_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v_size_106_; lean_object* v_buckets_107_; lean_object* v_a_108_; lean_object* v_fst_110_; lean_object* v_snd_111_; lean_object* v_label_120_; lean_object* v_textEdit_x3f_121_; lean_object* v___x_122_; lean_object* v___x_123_; uint64_t v___x_124_; uint64_t v___y_126_; 
v_size_106_ = lean_ctor_get(v_snd_101_, 0);
v_buckets_107_ = lean_ctor_get(v_snd_101_, 1);
v_a_108_ = lean_array_uget_borrowed(v_as_91_, v_i_93_);
v_label_120_ = lean_ctor_get(v_a_108_, 0);
v_textEdit_x3f_121_ = lean_ctor_get(v_a_108_, 4);
lean_inc(v_textEdit_x3f_121_);
lean_inc_ref(v_label_120_);
v___x_122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_122_, 0, v_label_120_);
lean_ctor_set(v___x_122_, 1, v_textEdit_x3f_121_);
v___x_123_ = lean_array_get_size(v_buckets_107_);
v___x_124_ = lean_string_hash(v_label_120_);
if (lean_obj_tag(v_textEdit_x3f_121_) == 0)
{
uint64_t v___x_168_; 
v___x_168_ = 11ULL;
v___y_126_ = v___x_168_;
goto v___jp_125_;
}
else
{
lean_object* v_val_169_; uint64_t v___x_170_; uint64_t v___x_171_; uint64_t v___x_172_; 
v_val_169_ = lean_ctor_get(v_textEdit_x3f_121_, 0);
v___x_170_ = l_Lean_Lsp_instHashableInsertReplaceEdit_hash(v_val_169_);
v___x_171_ = 13ULL;
v___x_172_ = lean_uint64_mix_hash(v___x_170_, v___x_171_);
v___y_126_ = v___x_172_;
goto v___jp_125_;
}
v___jp_109_:
{
uint8_t v___x_112_; 
v___x_112_ = lean_unbox(v_fst_110_);
lean_dec(v_fst_110_);
if (v___x_112_ == 0)
{
lean_object* v___x_113_; lean_object* v___x_115_; 
lean_inc(v_a_108_);
v___x_113_ = lean_array_push(v_fst_102_, v_a_108_);
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 1, v_snd_111_);
lean_ctor_set(v___x_104_, 0, v___x_113_);
v___x_115_ = v___x_104_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v___x_113_);
lean_ctor_set(v_reuseFailAlloc_116_, 1, v_snd_111_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
v_a_96_ = v___x_115_;
goto v___jp_95_;
}
}
else
{
lean_object* v___x_118_; 
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 1, v_snd_111_);
v___x_118_ = v___x_104_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_fst_102_);
lean_ctor_set(v_reuseFailAlloc_119_, 1, v_snd_111_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
v_a_96_ = v___x_118_;
goto v___jp_95_;
}
}
}
v___jp_125_:
{
uint64_t v___x_127_; uint64_t v___x_128_; uint64_t v___x_129_; uint64_t v_fold_130_; uint64_t v___x_131_; uint64_t v___x_132_; uint64_t v___x_133_; size_t v___x_134_; size_t v___x_135_; size_t v___x_136_; size_t v___x_137_; size_t v___x_138_; lean_object* v_bkt_139_; uint8_t v___x_140_; 
v___x_127_ = lean_uint64_mix_hash(v___x_124_, v___y_126_);
v___x_128_ = 32ULL;
v___x_129_ = lean_uint64_shift_right(v___x_127_, v___x_128_);
v_fold_130_ = lean_uint64_xor(v___x_127_, v___x_129_);
v___x_131_ = 16ULL;
v___x_132_ = lean_uint64_shift_right(v_fold_130_, v___x_131_);
v___x_133_ = lean_uint64_xor(v_fold_130_, v___x_132_);
v___x_134_ = lean_uint64_to_usize(v___x_133_);
v___x_135_ = lean_usize_of_nat(v___x_123_);
v___x_136_ = ((size_t)1ULL);
v___x_137_ = lean_usize_sub(v___x_135_, v___x_136_);
v___x_138_ = lean_usize_land(v___x_134_, v___x_137_);
v_bkt_139_ = lean_array_uget_borrowed(v_buckets_107_, v___x_138_);
v___x_140_ = l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg(v___x_122_, v_bkt_139_);
if (v___x_140_ == 0)
{
lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_164_; 
lean_inc_ref(v_buckets_107_);
lean_inc(v_size_106_);
v_isSharedCheck_164_ = !lean_is_exclusive(v_snd_101_);
if (v_isSharedCheck_164_ == 0)
{
lean_object* v_unused_165_; lean_object* v_unused_166_; 
v_unused_165_ = lean_ctor_get(v_snd_101_, 1);
lean_dec(v_unused_165_);
v_unused_166_ = lean_ctor_get(v_snd_101_, 0);
lean_dec(v_unused_166_);
v___x_142_ = v_snd_101_;
v_isShared_143_ = v_isSharedCheck_164_;
goto v_resetjp_141_;
}
else
{
lean_dec(v_snd_101_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_164_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v_size_x27_146_; lean_object* v___x_147_; lean_object* v_buckets_x27_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; uint8_t v___x_154_; 
v___x_144_ = lean_box(0);
v___x_145_ = lean_unsigned_to_nat(1u);
v_size_x27_146_ = lean_nat_add(v_size_106_, v___x_145_);
lean_dec(v_size_106_);
lean_inc(v_bkt_139_);
v___x_147_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_147_, 0, v___x_122_);
lean_ctor_set(v___x_147_, 1, v___x_144_);
lean_ctor_set(v___x_147_, 2, v_bkt_139_);
v_buckets_x27_148_ = lean_array_uset(v_buckets_107_, v___x_138_, v___x_147_);
v___x_149_ = lean_unsigned_to_nat(4u);
v___x_150_ = lean_nat_mul(v_size_x27_146_, v___x_149_);
v___x_151_ = lean_unsigned_to_nat(3u);
v___x_152_ = lean_nat_div(v___x_150_, v___x_151_);
lean_dec(v___x_150_);
v___x_153_ = lean_array_get_size(v_buckets_x27_148_);
v___x_154_ = lean_nat_dec_le(v___x_152_, v___x_153_);
lean_dec(v___x_152_);
if (v___x_154_ == 0)
{
lean_object* v_val_155_; lean_object* v___x_157_; 
v_val_155_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg(v_buckets_x27_148_);
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 1, v_val_155_);
lean_ctor_set(v___x_142_, 0, v_size_x27_146_);
v___x_157_ = v___x_142_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_size_x27_146_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v_val_155_);
v___x_157_ = v_reuseFailAlloc_159_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
lean_object* v___x_158_; 
v___x_158_ = lean_box(v___x_140_);
v_fst_110_ = v___x_158_;
v_snd_111_ = v___x_157_;
goto v___jp_109_;
}
}
else
{
lean_object* v___x_161_; 
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 1, v_buckets_x27_148_);
lean_ctor_set(v___x_142_, 0, v_size_x27_146_);
v___x_161_ = v___x_142_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_size_x27_146_);
lean_ctor_set(v_reuseFailAlloc_163_, 1, v_buckets_x27_148_);
v___x_161_ = v_reuseFailAlloc_163_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
lean_object* v___x_162_; 
v___x_162_ = lean_box(v___x_140_);
v_fst_110_ = v___x_162_;
v_snd_111_ = v___x_161_;
goto v___jp_109_;
}
}
}
}
else
{
lean_object* v___x_167_; 
lean_dec_ref_known(v___x_122_, 2);
v___x_167_ = lean_box(v___x_140_);
v_fst_110_ = v___x_167_;
v_snd_111_ = v_snd_101_;
goto v___jp_109_;
}
}
}
}
v___jp_95_:
{
size_t v___x_97_; size_t v___x_98_; 
v___x_97_ = ((size_t)1ULL);
v___x_98_ = lean_usize_add(v_i_93_, v___x_97_);
v_i_93_ = v___x_98_;
v_b_94_ = v_a_96_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_91_ = stack[0].m_obj;
size_t v_sz_92_ = stack[1].m_num;
size_t v_i_93_ = stack[2].m_num;
lean_object* v_b_94_ = stack[3].m_obj;
lean_object* v_res_174_;
v_res_174_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__2(v_as_91_, v_sz_92_, v_i_93_, v_b_94_);
stack->m_obj
 = v_res_174_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__2___boxed(lean_object* v_as_175_, lean_object* v_sz_176_, lean_object* v_i_177_, lean_object* v_b_178_){
_start:
{
size_t v_sz_boxed_179_; size_t v_i_boxed_180_; lean_object* v_res_181_; 
v_sz_boxed_179_ = lean_unbox_usize(v_sz_176_);
lean_dec(v_sz_176_);
v_i_boxed_180_ = lean_unbox_usize(v_i_177_);
lean_dec(v_i_177_);
v_res_181_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__2(v_as_175_, v_sz_boxed_179_, v_i_boxed_180_, v_b_178_);
lean_dec_ref(v_as_175_);
return v_res_181_;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__1(void){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_184_ = lean_box(0);
v___x_185_ = lean_unsigned_to_nat(16u);
v___x_186_ = lean_mk_array(v___x_185_, v___x_184_);
return v___x_186_;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__2(void){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v_index_189_; 
v___x_187_ = lean_obj_once(&l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__1, &l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__1_once, _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__1);
v___x_188_ = lean_unsigned_to_nat(0u);
v_index_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_index_189_, 0, v___x_188_);
lean_ctor_set(v_index_189_, 1, v___x_187_);
return v_index_189_;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__3(void){
_start:
{
lean_object* v_index_190_; lean_object* v_r_191_; lean_object* v___x_192_; 
v_index_190_ = lean_obj_once(&l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__2, &l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__2_once, _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__2);
v_r_191_ = ((lean_object*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__0));
v___x_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_192_, 0, v_r_191_);
lean_ctor_set(v___x_192_, 1, v_index_190_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems(lean_object* v_items_193_){
_start:
{
lean_object* v___x_194_; size_t v_sz_195_; size_t v___x_196_; lean_object* v___x_197_; lean_object* v_fst_198_; 
v___x_194_ = lean_obj_once(&l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__3, &l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__3_once, _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__3);
v_sz_195_ = lean_array_size(v_items_193_);
v___x_196_ = ((size_t)0ULL);
v___x_197_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__2(v_items_193_, v_sz_195_, v___x_196_, v___x_194_);
v_fst_198_ = lean_ctor_get(v___x_197_, 0);
lean_inc(v_fst_198_);
lean_dec_ref(v___x_197_);
return v_fst_198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___boxed(lean_object* v_items_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems(v_items_199_);
lean_dec_ref(v_items_199_);
return v_res_200_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0(lean_object* v_00_u03b2_201_, lean_object* v_a_202_, lean_object* v_x_203_){
_start:
{
uint8_t v___x_204_; 
v___x_204_ = l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg(v_a_202_, v_x_203_);
return v___x_204_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_202_ = stack[1].m_obj;
lean_object* v_x_203_ = stack[2].m_obj;
uint8_t v_res_205_;
v_res_205_ = l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0(lean_box(0), v_a_202_, v_x_203_);
stack->m_num = v_res_205_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___boxed(lean_object* v_00_u03b2_206_, lean_object* v_a_207_, lean_object* v_x_208_){
_start:
{
uint8_t v_res_209_; lean_object* v_r_210_; 
v_res_209_ = l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0(v_00_u03b2_206_, v_a_207_, v_x_208_);
lean_dec(v_x_208_);
lean_dec_ref(v_a_207_);
v_r_210_ = lean_box(v_res_209_);
return v_r_210_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1(lean_object* v_00_u03b2_211_, lean_object* v_data_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg(v_data_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2(lean_object* v_00_u03b2_214_, lean_object* v_i_215_, lean_object* v_source_216_, lean_object* v_target_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2___redArg(v_i_215_, v_source_216_, v_target_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_219_, lean_object* v_x_220_, lean_object* v_x_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__3___redArg(v_x_220_, v_x_221_);
return v___x_222_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__0(lean_object* v_uri_223_, lean_object* v_pos_224_, lean_object* v_caps_225_, lean_object* v_as_226_, size_t v_sz_227_, size_t v_i_228_, lean_object* v_b_229_, lean_object* v___y_230_){
_start:
{
lean_object* v_a_233_; lean_object* v_completions_237_; uint8_t v___x_242_; 
v___x_242_ = lean_usize_dec_lt(v_i_228_, v_sz_227_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; lean_object* v___x_244_; 
lean_dec_ref(v_caps_225_);
lean_dec_ref(v_pos_224_);
lean_dec_ref(v_uri_223_);
v___x_243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_243_, 0, v_b_229_);
v___x_244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
return v___x_244_;
}
else
{
lean_object* v_a_245_; lean_object* v_fst_246_; lean_object* v_snd_247_; lean_object* v_allCompletions_248_; lean_object* v___x_249_; 
v_a_245_ = lean_array_uget_borrowed(v_as_226_, v_i_228_);
v_fst_246_ = lean_ctor_get(v_a_245_, 0);
v_snd_247_ = lean_ctor_get(v_a_245_, 1);
v_allCompletions_248_ = ((lean_object*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__0));
v___x_249_ = l_Lean_Server_CancellableM_checkCancelled(v___y_230_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v_a_250_; 
v_a_250_ = lean_ctor_get(v___x_249_, 0);
lean_inc(v_a_250_);
lean_dec_ref_known(v___x_249_, 1);
if (lean_obj_tag(v_a_250_) == 0)
{
lean_object* v_a_251_; 
lean_dec_ref(v_b_229_);
lean_dec_ref(v_caps_225_);
lean_dec_ref(v_pos_224_);
lean_dec_ref(v_uri_223_);
v_a_251_ = lean_ctor_get(v_a_250_, 0);
lean_inc(v_a_251_);
lean_dec_ref_known(v_a_250_, 1);
v_a_233_ = v_a_251_;
goto v___jp_232_;
}
else
{
lean_object* v_info_252_; 
lean_dec_ref_known(v_a_250_, 1);
v_info_252_ = lean_ctor_get(v_fst_246_, 2);
switch(lean_obj_tag(v_info_252_))
{
case 1:
{
lean_object* v_hoverInfo_253_; lean_object* v_ctx_254_; lean_object* v_stx_255_; lean_object* v_id_256_; uint8_t v_danglingDot_257_; lean_object* v_lctx_258_; lean_object* v___x_259_; 
v_hoverInfo_253_ = lean_ctor_get(v_fst_246_, 0);
v_ctx_254_ = lean_ctor_get(v_fst_246_, 1);
v_stx_255_ = lean_ctor_get(v_info_252_, 0);
v_id_256_ = lean_ctor_get(v_info_252_, 1);
v_danglingDot_257_ = lean_ctor_get_uint8(v_info_252_, sizeof(void*)*4);
v_lctx_258_ = lean_ctor_get(v_info_252_, 2);
lean_inc(v_hoverInfo_253_);
lean_inc(v_id_256_);
lean_inc(v_stx_255_);
lean_inc_ref(v_lctx_258_);
lean_inc_ref(v_ctx_254_);
lean_inc(v_snd_247_);
lean_inc_ref(v_pos_224_);
lean_inc_ref(v_uri_223_);
v___x_259_ = l_Lean_Server_Completion_idCompletion(v_uri_223_, v_pos_224_, v_snd_247_, v_ctx_254_, v_lctx_258_, v_stx_255_, v_id_256_, v_hoverInfo_253_, v_danglingDot_257_, v___y_230_);
if (lean_obj_tag(v___x_259_) == 0)
{
lean_object* v_a_260_; 
v_a_260_ = lean_ctor_get(v___x_259_, 0);
lean_inc(v_a_260_);
lean_dec_ref_known(v___x_259_, 1);
if (lean_obj_tag(v_a_260_) == 0)
{
lean_object* v_a_261_; 
lean_dec_ref(v_b_229_);
lean_dec_ref(v_caps_225_);
lean_dec_ref(v_pos_224_);
lean_dec_ref(v_uri_223_);
v_a_261_ = lean_ctor_get(v_a_260_, 0);
lean_inc(v_a_261_);
lean_dec_ref_known(v_a_260_, 1);
v_a_233_ = v_a_261_;
goto v___jp_232_;
}
else
{
lean_object* v_a_262_; 
v_a_262_ = lean_ctor_get(v_a_260_, 0);
lean_inc(v_a_262_);
lean_dec_ref_known(v_a_260_, 1);
v_completions_237_ = v_a_262_;
goto v___jp_236_;
}
}
else
{
lean_dec_ref(v_b_229_);
lean_dec_ref(v_caps_225_);
lean_dec_ref(v_pos_224_);
lean_dec_ref(v_uri_223_);
return v___x_259_;
}
}
case 0:
{
lean_object* v_ctx_263_; lean_object* v_termInfo_264_; lean_object* v___x_265_; 
v_ctx_263_ = lean_ctor_get(v_fst_246_, 1);
v_termInfo_264_ = lean_ctor_get(v_info_252_, 0);
lean_inc_ref(v_termInfo_264_);
lean_inc_ref(v_ctx_263_);
lean_inc(v_snd_247_);
lean_inc_ref(v_pos_224_);
lean_inc_ref(v_uri_223_);
v___x_265_ = l_Lean_Server_Completion_dotCompletion(v_uri_223_, v_pos_224_, v_snd_247_, v_ctx_263_, v_termInfo_264_, v___y_230_);
if (lean_obj_tag(v___x_265_) == 0)
{
lean_object* v_a_266_; 
v_a_266_ = lean_ctor_get(v___x_265_, 0);
lean_inc(v_a_266_);
lean_dec_ref_known(v___x_265_, 1);
if (lean_obj_tag(v_a_266_) == 0)
{
lean_object* v_a_267_; 
lean_dec_ref(v_b_229_);
lean_dec_ref(v_caps_225_);
lean_dec_ref(v_pos_224_);
lean_dec_ref(v_uri_223_);
v_a_267_ = lean_ctor_get(v_a_266_, 0);
lean_inc(v_a_267_);
lean_dec_ref_known(v_a_266_, 1);
v_a_233_ = v_a_267_;
goto v___jp_232_;
}
else
{
lean_object* v_a_268_; 
v_a_268_ = lean_ctor_get(v_a_266_, 0);
lean_inc(v_a_268_);
lean_dec_ref_known(v_a_266_, 1);
v_completions_237_ = v_a_268_;
goto v___jp_236_;
}
}
else
{
lean_dec_ref(v_b_229_);
lean_dec_ref(v_caps_225_);
lean_dec_ref(v_pos_224_);
lean_dec_ref(v_uri_223_);
return v___x_265_;
}
}
case 2:
{
lean_object* v_ctx_269_; lean_object* v_id_270_; lean_object* v_lctx_271_; lean_object* v_expectedType_x3f_272_; lean_object* v___x_273_; 
v_ctx_269_ = lean_ctor_get(v_fst_246_, 1);
v_id_270_ = lean_ctor_get(v_info_252_, 1);
v_lctx_271_ = lean_ctor_get(v_info_252_, 2);
v_expectedType_x3f_272_ = lean_ctor_get(v_info_252_, 3);
lean_inc(v_expectedType_x3f_272_);
lean_inc(v_id_270_);
lean_inc_ref(v_lctx_271_);
lean_inc_ref(v_ctx_269_);
lean_inc(v_snd_247_);
lean_inc_ref(v_pos_224_);
lean_inc_ref(v_uri_223_);
v___x_273_ = l_Lean_Server_Completion_dotIdCompletion(v_uri_223_, v_pos_224_, v_snd_247_, v_ctx_269_, v_lctx_271_, v_id_270_, v_expectedType_x3f_272_, v___y_230_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v_a_274_; 
v_a_274_ = lean_ctor_get(v___x_273_, 0);
lean_inc(v_a_274_);
lean_dec_ref_known(v___x_273_, 1);
if (lean_obj_tag(v_a_274_) == 0)
{
lean_object* v_a_275_; 
lean_dec_ref(v_b_229_);
lean_dec_ref(v_caps_225_);
lean_dec_ref(v_pos_224_);
lean_dec_ref(v_uri_223_);
v_a_275_ = lean_ctor_get(v_a_274_, 0);
lean_inc(v_a_275_);
lean_dec_ref_known(v_a_274_, 1);
v_a_233_ = v_a_275_;
goto v___jp_232_;
}
else
{
lean_object* v_a_276_; 
v_a_276_ = lean_ctor_get(v_a_274_, 0);
lean_inc(v_a_276_);
lean_dec_ref_known(v_a_274_, 1);
v_completions_237_ = v_a_276_;
goto v___jp_236_;
}
}
else
{
lean_dec_ref(v_b_229_);
lean_dec_ref(v_caps_225_);
lean_dec_ref(v_pos_224_);
lean_dec_ref(v_uri_223_);
return v___x_273_;
}
}
case 3:
{
lean_object* v_ctx_277_; lean_object* v_id_278_; lean_object* v_lctx_279_; lean_object* v_structName_280_; lean_object* v___x_281_; 
v_ctx_277_ = lean_ctor_get(v_fst_246_, 1);
v_id_278_ = lean_ctor_get(v_info_252_, 1);
v_lctx_279_ = lean_ctor_get(v_info_252_, 2);
v_structName_280_ = lean_ctor_get(v_info_252_, 3);
lean_inc(v_structName_280_);
lean_inc(v_id_278_);
lean_inc_ref(v_lctx_279_);
lean_inc_ref(v_ctx_277_);
lean_inc(v_snd_247_);
lean_inc_ref(v_pos_224_);
lean_inc_ref(v_uri_223_);
v___x_281_ = l_Lean_Server_Completion_fieldIdCompletion(v_uri_223_, v_pos_224_, v_snd_247_, v_ctx_277_, v_lctx_279_, v_id_278_, v_structName_280_, v___y_230_);
if (lean_obj_tag(v___x_281_) == 0)
{
lean_object* v_a_282_; 
v_a_282_ = lean_ctor_get(v___x_281_, 0);
lean_inc(v_a_282_);
lean_dec_ref_known(v___x_281_, 1);
if (lean_obj_tag(v_a_282_) == 0)
{
lean_object* v_a_283_; 
lean_dec_ref(v_b_229_);
lean_dec_ref(v_caps_225_);
lean_dec_ref(v_pos_224_);
lean_dec_ref(v_uri_223_);
v_a_283_ = lean_ctor_get(v_a_282_, 0);
lean_inc(v_a_283_);
lean_dec_ref_known(v_a_282_, 1);
v_a_233_ = v_a_283_;
goto v___jp_232_;
}
else
{
lean_object* v_a_284_; 
v_a_284_ = lean_ctor_get(v_a_282_, 0);
lean_inc(v_a_284_);
lean_dec_ref_known(v_a_282_, 1);
v_completions_237_ = v_a_284_;
goto v___jp_236_;
}
}
else
{
lean_dec_ref(v_b_229_);
lean_dec_ref(v_caps_225_);
lean_dec_ref(v_pos_224_);
lean_dec_ref(v_uri_223_);
return v___x_281_;
}
}
case 5:
{
lean_object* v_ctx_285_; lean_object* v_stx_286_; lean_object* v___x_287_; 
v_ctx_285_ = lean_ctor_get(v_fst_246_, 1);
v_stx_286_ = lean_ctor_get(v_info_252_, 0);
lean_inc_ref(v_caps_225_);
lean_inc(v_stx_286_);
lean_inc_ref(v_ctx_285_);
lean_inc(v_snd_247_);
lean_inc_ref(v_pos_224_);
lean_inc_ref(v_uri_223_);
v___x_287_ = l_Lean_Server_Completion_optionCompletion(v_uri_223_, v_pos_224_, v_snd_247_, v_ctx_285_, v_stx_286_, v_caps_225_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_object* v_a_288_; 
v_a_288_ = lean_ctor_get(v___x_287_, 0);
lean_inc(v_a_288_);
lean_dec_ref_known(v___x_287_, 1);
v_completions_237_ = v_a_288_;
goto v___jp_236_;
}
else
{
lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_296_; 
lean_dec_ref(v_b_229_);
lean_dec_ref(v_caps_225_);
lean_dec_ref(v_pos_224_);
lean_dec_ref(v_uri_223_);
v_a_289_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_296_ == 0)
{
v___x_291_ = v___x_287_;
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___x_287_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_294_; 
if (v_isShared_292_ == 0)
{
v___x_294_ = v___x_291_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_a_289_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
}
case 6:
{
lean_object* v_ctx_297_; lean_object* v_partialId_298_; lean_object* v___x_299_; 
v_ctx_297_ = lean_ctor_get(v_fst_246_, 1);
v_partialId_298_ = lean_ctor_get(v_info_252_, 1);
lean_inc_ref(v_caps_225_);
lean_inc(v_partialId_298_);
lean_inc_ref(v_ctx_297_);
lean_inc(v_snd_247_);
lean_inc_ref(v_pos_224_);
lean_inc_ref(v_uri_223_);
v___x_299_ = l_Lean_Server_Completion_errorNameCompletion(v_uri_223_, v_pos_224_, v_snd_247_, v_ctx_297_, v_partialId_298_, v_caps_225_);
if (lean_obj_tag(v___x_299_) == 0)
{
lean_object* v_a_300_; 
v_a_300_ = lean_ctor_get(v___x_299_, 0);
lean_inc(v_a_300_);
lean_dec_ref_known(v___x_299_, 1);
v_completions_237_ = v_a_300_;
goto v___jp_236_;
}
else
{
lean_object* v_a_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_308_; 
lean_dec_ref(v_b_229_);
lean_dec_ref(v_caps_225_);
lean_dec_ref(v_pos_224_);
lean_dec_ref(v_uri_223_);
v_a_301_ = lean_ctor_get(v___x_299_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_308_ == 0)
{
v___x_303_ = v___x_299_;
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_a_301_);
lean_dec(v___x_299_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_306_; 
if (v_isShared_304_ == 0)
{
v___x_306_ = v___x_303_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_a_301_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
}
}
case 7:
{
lean_object* v_id_x3f_309_; uint8_t v_danglingDot_310_; lean_object* v_scopeNames_311_; lean_object* v___x_312_; 
v_id_x3f_309_ = lean_ctor_get(v_info_252_, 1);
v_danglingDot_310_ = lean_ctor_get_uint8(v_info_252_, sizeof(void*)*3);
v_scopeNames_311_ = lean_ctor_get(v_info_252_, 2);
lean_inc(v_scopeNames_311_);
lean_inc(v_id_x3f_309_);
lean_inc(v_snd_247_);
lean_inc_ref(v_pos_224_);
lean_inc_ref(v_uri_223_);
v___x_312_ = l_Lean_Server_Completion_endSectionCompletion(v_uri_223_, v_pos_224_, v_snd_247_, v_id_x3f_309_, v_danglingDot_310_, v_scopeNames_311_);
if (lean_obj_tag(v___x_312_) == 0)
{
lean_object* v_a_313_; 
v_a_313_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_a_313_);
lean_dec_ref_known(v___x_312_, 1);
v_completions_237_ = v_a_313_;
goto v___jp_236_;
}
else
{
lean_object* v_a_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_321_; 
lean_dec_ref(v_b_229_);
lean_dec_ref(v_caps_225_);
lean_dec_ref(v_pos_224_);
lean_dec_ref(v_uri_223_);
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
case 8:
{
lean_object* v_ctx_322_; lean_object* v___x_323_; 
v_ctx_322_ = lean_ctor_get(v_fst_246_, 1);
lean_inc_ref(v_ctx_322_);
lean_inc(v_snd_247_);
lean_inc_ref(v_pos_224_);
lean_inc_ref(v_uri_223_);
v___x_323_ = l_Lean_Server_Completion_tacticCompletion(v_uri_223_, v_pos_224_, v_snd_247_, v_ctx_322_);
if (lean_obj_tag(v___x_323_) == 0)
{
lean_object* v_a_324_; 
v_a_324_ = lean_ctor_get(v___x_323_, 0);
lean_inc(v_a_324_);
lean_dec_ref_known(v___x_323_, 1);
v_completions_237_ = v_a_324_;
goto v___jp_236_;
}
else
{
lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_332_; 
lean_dec_ref(v_b_229_);
lean_dec_ref(v_caps_225_);
lean_dec_ref(v_pos_224_);
lean_dec_ref(v_uri_223_);
v_a_325_ = lean_ctor_get(v___x_323_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_323_);
if (v_isSharedCheck_332_ == 0)
{
v___x_327_ = v___x_323_;
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_323_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_330_; 
if (v_isShared_328_ == 0)
{
v___x_330_ = v___x_327_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_a_325_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
default: 
{
v_completions_237_ = v_allCompletions_248_;
goto v___jp_236_;
}
}
}
}
else
{
lean_object* v_a_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_340_; 
lean_dec_ref(v_b_229_);
lean_dec_ref(v_caps_225_);
lean_dec_ref(v_pos_224_);
lean_dec_ref(v_uri_223_);
v_a_333_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_340_ == 0)
{
v___x_335_ = v___x_249_;
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_a_333_);
lean_dec(v___x_249_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_338_; 
if (v_isShared_336_ == 0)
{
v___x_338_ = v___x_335_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_a_333_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
v___jp_232_:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_234_, 0, v_a_233_);
v___x_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
return v___x_235_;
}
v___jp_236_:
{
lean_object* v___x_238_; size_t v___x_239_; size_t v___x_240_; 
v___x_238_ = l_Array_append___redArg(v_b_229_, v_completions_237_);
lean_dec_ref(v_completions_237_);
v___x_239_ = ((size_t)1ULL);
v___x_240_ = lean_usize_add(v_i_228_, v___x_239_);
v_i_228_ = v___x_240_;
v_b_229_ = v___x_238_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_uri_223_ = stack[0].m_obj;
lean_object* v_pos_224_ = stack[1].m_obj;
lean_object* v_caps_225_ = stack[2].m_obj;
lean_object* v_as_226_ = stack[3].m_obj;
size_t v_sz_227_ = stack[4].m_num;
size_t v_i_228_ = stack[5].m_num;
lean_object* v_b_229_ = stack[6].m_obj;
lean_object* v___y_230_ = stack[7].m_obj;
lean_object* v_res_341_;
v_res_341_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__0(v_uri_223_, v_pos_224_, v_caps_225_, v_as_226_, v_sz_227_, v_i_228_, v_b_229_, v___y_230_);
stack->m_obj
 = v_res_341_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__0___boxed(lean_object* v_uri_342_, lean_object* v_pos_343_, lean_object* v_caps_344_, lean_object* v_as_345_, lean_object* v_sz_346_, lean_object* v_i_347_, lean_object* v_b_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
size_t v_sz_boxed_351_; size_t v_i_boxed_352_; lean_object* v_res_353_; 
v_sz_boxed_351_ = lean_unbox_usize(v_sz_346_);
lean_dec(v_sz_346_);
v_i_boxed_352_ = lean_unbox_usize(v_i_347_);
lean_dec(v_i_347_);
v_res_353_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__0(v_uri_342_, v_pos_343_, v_caps_344_, v_as_345_, v_sz_boxed_351_, v_i_boxed_352_, v_b_348_, v___y_349_);
lean_dec_ref(v___y_349_);
lean_dec_ref(v_as_345_);
return v_res_353_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__1(lean_object* v_uri_354_, lean_object* v_pos_355_, lean_object* v_caps_356_, lean_object* v_as_357_, size_t v_sz_358_, size_t v_i_359_, lean_object* v_b_360_, lean_object* v___y_361_){
_start:
{
uint8_t v___x_363_; 
v___x_363_ = lean_usize_dec_lt(v_i_359_, v_sz_358_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; lean_object* v___x_365_; 
lean_dec_ref(v_caps_356_);
lean_dec_ref(v_pos_355_);
lean_dec_ref(v_uri_354_);
v___x_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_364_, 0, v_b_360_);
v___x_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
return v___x_365_;
}
else
{
lean_object* v_a_366_; size_t v_sz_367_; size_t v___x_368_; lean_object* v___x_369_; 
v_a_366_ = lean_array_uget_borrowed(v_as_357_, v_i_359_);
v_sz_367_ = lean_array_size(v_a_366_);
v___x_368_ = ((size_t)0ULL);
lean_inc_ref(v_caps_356_);
lean_inc_ref(v_pos_355_);
lean_inc_ref(v_uri_354_);
v___x_369_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__0(v_uri_354_, v_pos_355_, v_caps_356_, v_a_366_, v_sz_367_, v___x_368_, v_b_360_, v___y_361_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v_a_370_; 
v_a_370_ = lean_ctor_get(v___x_369_, 0);
if (lean_obj_tag(v_a_370_) == 0)
{
lean_dec_ref(v_caps_356_);
lean_dec_ref(v_pos_355_);
lean_dec_ref(v_uri_354_);
return v___x_369_;
}
else
{
lean_object* v_a_371_; lean_object* v___x_372_; lean_object* v___x_373_; uint8_t v___x_374_; 
v_a_371_ = lean_ctor_get(v_a_370_, 0);
v___x_372_ = lean_array_get_size(v_a_371_);
v___x_373_ = lean_unsigned_to_nat(0u);
v___x_374_ = lean_nat_dec_eq(v___x_372_, v___x_373_);
if (v___x_374_ == 0)
{
lean_dec_ref(v_caps_356_);
lean_dec_ref(v_pos_355_);
lean_dec_ref(v_uri_354_);
return v___x_369_;
}
else
{
size_t v___x_375_; size_t v___x_376_; 
lean_inc(v_a_371_);
lean_dec_ref_known(v___x_369_, 1);
v___x_375_ = ((size_t)1ULL);
v___x_376_ = lean_usize_add(v_i_359_, v___x_375_);
v_i_359_ = v___x_376_;
v_b_360_ = v_a_371_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_caps_356_);
lean_dec_ref(v_pos_355_);
lean_dec_ref(v_uri_354_);
return v___x_369_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_uri_354_ = stack[0].m_obj;
lean_object* v_pos_355_ = stack[1].m_obj;
lean_object* v_caps_356_ = stack[2].m_obj;
lean_object* v_as_357_ = stack[3].m_obj;
size_t v_sz_358_ = stack[4].m_num;
size_t v_i_359_ = stack[5].m_num;
lean_object* v_b_360_ = stack[6].m_obj;
lean_object* v___y_361_ = stack[7].m_obj;
lean_object* v_res_378_;
v_res_378_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__1(v_uri_354_, v_pos_355_, v_caps_356_, v_as_357_, v_sz_358_, v_i_359_, v_b_360_, v___y_361_);
stack->m_obj
 = v_res_378_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__1___boxed(lean_object* v_uri_379_, lean_object* v_pos_380_, lean_object* v_caps_381_, lean_object* v_as_382_, lean_object* v_sz_383_, lean_object* v_i_384_, lean_object* v_b_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
size_t v_sz_boxed_388_; size_t v_i_boxed_389_; lean_object* v_res_390_; 
v_sz_boxed_388_ = lean_unbox_usize(v_sz_383_);
lean_dec(v_sz_383_);
v_i_boxed_389_ = lean_unbox_usize(v_i_384_);
lean_dec(v_i_384_);
v_res_390_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__1(v_uri_379_, v_pos_380_, v_caps_381_, v_as_382_, v_sz_boxed_388_, v_i_boxed_389_, v_b_385_, v___y_386_);
lean_dec_ref(v___y_386_);
lean_dec_ref(v_as_382_);
return v_res_390_;
}
}
lean_object* l_Lean_Server_Completion_find_x3f(lean_object* v_uri_391_, lean_object* v_pos_392_, lean_object* v_fileMap_393_, lean_object* v_hoverPos_394_, lean_object* v_cmdStx_395_, lean_object* v_infoTree_396_, lean_object* v_caps_397_, lean_object* v_a_398_){
_start:
{
lean_object* v___x_400_; lean_object* v_fst_401_; lean_object* v_snd_402_; lean_object* v_allCompletions_403_; size_t v_sz_404_; size_t v___x_405_; lean_object* v___x_406_; 
v___x_400_ = l_Lean_Server_Completion_findPrioritizedCompletionPartitionsAt(v_fileMap_393_, v_hoverPos_394_, v_cmdStx_395_, v_infoTree_396_);
v_fst_401_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_fst_401_);
v_snd_402_ = lean_ctor_get(v___x_400_, 1);
lean_inc(v_snd_402_);
lean_dec_ref(v___x_400_);
v_allCompletions_403_ = ((lean_object*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__0));
v_sz_404_ = lean_array_size(v_fst_401_);
v___x_405_ = ((size_t)0ULL);
v___x_406_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__1(v_uri_391_, v_pos_392_, v_caps_397_, v_fst_401_, v_sz_404_, v___x_405_, v_allCompletions_403_, v_a_398_);
lean_dec(v_fst_401_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_440_; 
v_a_407_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_440_ == 0)
{
v___x_409_ = v___x_406_;
v_isShared_410_ = v_isSharedCheck_440_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_406_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_440_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
if (lean_obj_tag(v_a_407_) == 0)
{
lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_421_; 
lean_dec(v_snd_402_);
v_a_411_ = lean_ctor_get(v_a_407_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v_a_407_);
if (v_isSharedCheck_421_ == 0)
{
v___x_413_ = v_a_407_;
v_isShared_414_ = v_isSharedCheck_421_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_dec(v_a_407_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_421_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_416_; 
if (v_isShared_414_ == 0)
{
v___x_416_ = v___x_413_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_a_411_);
v___x_416_ = v_reuseFailAlloc_420_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
lean_object* v___x_418_; 
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 0, v___x_416_);
v___x_418_ = v___x_409_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v___x_416_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
else
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_439_; 
v_a_422_ = lean_ctor_get(v_a_407_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v_a_407_);
if (v_isSharedCheck_439_ == 0)
{
v___x_424_ = v_a_407_;
v_isShared_425_ = v_isSharedCheck_439_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v_a_407_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_439_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_426_; uint8_t v___y_428_; uint8_t v___x_436_; 
v___x_426_ = l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems(v_a_422_);
lean_dec(v_a_422_);
v___x_436_ = lean_unbox(v_snd_402_);
lean_dec(v_snd_402_);
if (v___x_436_ == 0)
{
uint8_t v___x_437_; 
v___x_437_ = 1;
v___y_428_ = v___x_437_;
goto v___jp_427_;
}
else
{
uint8_t v___x_438_; 
v___x_438_ = 0;
v___y_428_ = v___x_438_;
goto v___jp_427_;
}
v___jp_427_:
{
lean_object* v___x_429_; lean_object* v___x_431_; 
v___x_429_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_429_, 0, v___x_426_);
lean_ctor_set_uint8(v___x_429_, sizeof(void*)*1, v___y_428_);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 0, v___x_429_);
v___x_431_ = v___x_424_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_429_);
v___x_431_ = v_reuseFailAlloc_435_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
lean_object* v___x_433_; 
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 0, v___x_431_);
v___x_433_ = v___x_409_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_431_);
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
}
}
else
{
lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_448_; 
lean_dec(v_snd_402_);
v_a_441_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_448_ == 0)
{
v___x_443_ = v___x_406_;
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___x_406_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_446_; 
if (v_isShared_444_ == 0)
{
v___x_446_ = v___x_443_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_a_441_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_Completion_find_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_uri_391_ = stack[0].m_obj;
lean_object* v_pos_392_ = stack[1].m_obj;
lean_object* v_fileMap_393_ = stack[2].m_obj;
lean_object* v_hoverPos_394_ = stack[3].m_obj;
lean_object* v_cmdStx_395_ = stack[4].m_obj;
lean_object* v_infoTree_396_ = stack[5].m_obj;
lean_object* v_caps_397_ = stack[6].m_obj;
lean_object* v_a_398_ = stack[7].m_obj;
lean_object* v_res_449_;
v_res_449_ = l_Lean_Server_Completion_find_x3f(v_uri_391_, v_pos_392_, v_fileMap_393_, v_hoverPos_394_, v_cmdStx_395_, v_infoTree_396_, v_caps_397_, v_a_398_);
stack->m_obj
 = v_res_449_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_find_x3f___boxed(lean_object* v_uri_450_, lean_object* v_pos_451_, lean_object* v_fileMap_452_, lean_object* v_hoverPos_453_, lean_object* v_cmdStx_454_, lean_object* v_infoTree_455_, lean_object* v_caps_456_, lean_object* v_a_457_, lean_object* v_a_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Lean_Server_Completion_find_x3f(v_uri_450_, v_pos_451_, v_fileMap_452_, v_hoverPos_453_, v_cmdStx_454_, v_infoTree_455_, v_caps_456_, v_a_457_);
lean_dec_ref(v_a_457_);
return v_res_459_;
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
