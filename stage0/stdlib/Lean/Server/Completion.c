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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_noption_get(lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Lsp_instBEqInsertReplaceEdit_beq(lean_object*, lean_object*);
uint64_t l_Lean_Lsp_instHashableInsertReplaceEdit_hash(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___boxed(lean_object*);
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
static lean_once_cell_t l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_find_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0_spec__1(lean_object* v_x_1_, lean_object* v_x_2_){
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
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0_spec__1___boxed(lean_object* v_x_9_, lean_object* v_x_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0_spec__1(v_x_9_, v_x_10_);
lean_dec(v_x_10_);
lean_dec(v_x_9_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0___redArg(lean_object* v_m_13_, lean_object* v_query_14_, lean_object* v_x_15_, lean_object* v_x_16_, lean_object* v_x_17_){
_start:
{
lean_object* v_zero_18_; uint8_t v_isZero_19_; 
v_zero_18_ = lean_unsigned_to_nat(0u);
v_isZero_19_ = lean_nat_dec_eq(v_x_16_, v_zero_18_);
if (v_isZero_19_ == 1)
{
lean_dec(v_x_17_);
lean_dec(v_x_16_);
if (lean_obj_tag(v_x_15_) == 0)
{
lean_object* v___x_20_; 
v___x_20_ = lean_box(2);
return v___x_20_;
}
else
{
lean_object* v_val_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_28_; 
v_val_21_ = lean_ctor_get(v_x_15_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v_x_15_);
if (v_isSharedCheck_28_ == 0)
{
v___x_23_ = v_x_15_;
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_val_21_);
lean_dec(v_x_15_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_26_; 
if (v_isShared_24_ == 0)
{
v___x_26_ = v___x_23_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_val_21_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
else
{
lean_object* v_keyArray_29_; lean_object* v_valueArray_30_; lean_object* v___x_31_; uint8_t v_isSome_32_; 
v_keyArray_29_ = lean_ctor_get(v_m_13_, 1);
v_valueArray_30_ = lean_ctor_get(v_m_13_, 2);
v___x_31_ = lean_array_fget_borrowed(v_keyArray_29_, v_x_17_);
v_isSome_32_ = lean_noption_is_some(v___x_31_);
if (v_isSome_32_ == 0)
{
lean_dec(v_x_16_);
if (lean_obj_tag(v_x_15_) == 0)
{
lean_object* v___x_33_; 
v___x_33_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_33_, 0, v_x_17_);
return v___x_33_;
}
else
{
lean_object* v_val_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_41_; 
lean_dec(v_x_17_);
v_val_34_ = lean_ctor_get(v_x_15_, 0);
v_isSharedCheck_41_ = !lean_is_exclusive(v_x_15_);
if (v_isSharedCheck_41_ == 0)
{
v___x_36_ = v_x_15_;
v_isShared_37_ = v_isSharedCheck_41_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_val_34_);
lean_dec(v_x_15_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_41_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v___x_39_; 
if (v_isShared_37_ == 0)
{
v___x_39_ = v___x_36_;
goto v_reusejp_38_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v_val_34_);
v___x_39_ = v_reuseFailAlloc_40_;
goto v_reusejp_38_;
}
v_reusejp_38_:
{
return v___x_39_;
}
}
}
}
else
{
lean_object* v_one_42_; lean_object* v_n_43_; lean_object* v___y_45_; 
v_one_42_ = lean_unsigned_to_nat(1u);
v_n_43_ = lean_nat_sub(v_x_16_, v_one_42_);
lean_dec(v_x_16_);
if (v_isSome_32_ == 0)
{
goto v___jp_51_;
}
else
{
lean_object* v___x_53_; uint8_t v_isSome_54_; 
v___x_53_ = lean_array_fget_borrowed(v_valueArray_30_, v_x_17_);
v_isSome_54_ = lean_noption_is_some(v___x_53_);
if (v_isSome_54_ == 0)
{
goto v___jp_51_;
}
else
{
lean_object* v_val_55_; lean_object* v_fst_56_; lean_object* v_snd_57_; lean_object* v_fst_58_; lean_object* v_snd_59_; lean_object* v_val_60_; uint8_t v___y_62_; uint8_t v___x_69_; 
lean_inc(v___x_31_);
v_val_55_ = lean_noption_get(v___x_31_);
v_fst_56_ = lean_ctor_get(v_val_55_, 0);
lean_inc(v_fst_56_);
v_snd_57_ = lean_ctor_get(v_val_55_, 1);
lean_inc(v_snd_57_);
v_fst_58_ = lean_ctor_get(v_query_14_, 0);
v_snd_59_ = lean_ctor_get(v_query_14_, 1);
lean_inc(v___x_53_);
v_val_60_ = lean_noption_get(v___x_53_);
v___x_69_ = lean_string_dec_eq(v_fst_56_, v_fst_58_);
lean_dec(v_fst_56_);
if (v___x_69_ == 0)
{
lean_dec(v_snd_57_);
v___y_62_ = v___x_69_;
goto v___jp_61_;
}
else
{
uint8_t v___x_70_; 
v___x_70_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0_spec__1(v_snd_57_, v_snd_59_);
lean_dec(v_snd_57_);
v___y_62_ = v___x_70_;
goto v___jp_61_;
}
v___jp_61_:
{
if (v___y_62_ == 0)
{
lean_object* v___x_63_; lean_object* v___x_64_; uint8_t v___x_65_; 
lean_dec(v_val_60_);
lean_dec(v_val_55_);
v___x_63_ = lean_array_get_size(v_keyArray_29_);
v___x_64_ = lean_nat_add(v_x_17_, v_one_42_);
lean_dec(v_x_17_);
v___x_65_ = lean_nat_dec_lt(v___x_64_, v___x_63_);
if (v___x_65_ == 0)
{
lean_dec(v___x_64_);
v_x_16_ = v_n_43_;
v_x_17_ = v_zero_18_;
goto _start;
}
else
{
v_x_16_ = v_n_43_;
v_x_17_ = v___x_64_;
goto _start;
}
}
else
{
lean_object* v___x_68_; 
lean_dec(v_n_43_);
lean_dec(v_x_15_);
v___x_68_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_68_, 0, v_x_17_);
lean_ctor_set(v___x_68_, 1, v_val_55_);
lean_ctor_set(v___x_68_, 2, v_val_60_);
return v___x_68_;
}
}
}
}
v___jp_44_:
{
lean_object* v___x_46_; lean_object* v___x_47_; uint8_t v___x_48_; 
v___x_46_ = lean_array_get_size(v_keyArray_29_);
v___x_47_ = lean_nat_add(v_x_17_, v_one_42_);
lean_dec(v_x_17_);
v___x_48_ = lean_nat_dec_lt(v___x_47_, v___x_46_);
if (v___x_48_ == 0)
{
lean_dec(v___x_47_);
v_x_15_ = v___y_45_;
v_x_16_ = v_n_43_;
v_x_17_ = v_zero_18_;
goto _start;
}
else
{
v_x_15_ = v___y_45_;
v_x_16_ = v_n_43_;
v_x_17_ = v___x_47_;
goto _start;
}
}
v___jp_51_:
{
if (lean_obj_tag(v_x_15_) == 0)
{
lean_object* v___x_52_; 
lean_inc(v_x_17_);
v___x_52_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_52_, 0, v_x_17_);
v___y_45_ = v___x_52_;
goto v___jp_44_;
}
else
{
v___y_45_ = v_x_15_;
goto v___jp_44_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0___redArg___boxed(lean_object* v_m_71_, lean_object* v_query_72_, lean_object* v_x_73_, lean_object* v_x_74_, lean_object* v_x_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0___redArg(v_m_71_, v_query_72_, v_x_73_, v_x_74_, v_x_75_);
lean_dec_ref(v_query_72_);
lean_dec_ref(v_m_71_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg(lean_object* v_m_77_, lean_object* v_query_78_){
_start:
{
lean_object* v_keyArray_79_; lean_object* v_fst_80_; lean_object* v_snd_81_; lean_object* v___x_82_; uint64_t v___x_83_; uint64_t v___y_85_; 
v_keyArray_79_ = lean_ctor_get(v_m_77_, 1);
v_fst_80_ = lean_ctor_get(v_query_78_, 0);
v_snd_81_ = lean_ctor_get(v_query_78_, 1);
v___x_82_ = lean_array_get_size(v_keyArray_79_);
v___x_83_ = lean_string_hash(v_fst_80_);
if (lean_obj_tag(v_snd_81_) == 0)
{
uint64_t v___x_101_; 
v___x_101_ = 11ULL;
v___y_85_ = v___x_101_;
goto v___jp_84_;
}
else
{
lean_object* v_val_102_; uint64_t v___x_103_; uint64_t v___x_104_; uint64_t v___x_105_; 
v_val_102_ = lean_ctor_get(v_snd_81_, 0);
v___x_103_ = l_Lean_Lsp_instHashableInsertReplaceEdit_hash(v_val_102_);
v___x_104_ = 13ULL;
v___x_105_ = lean_uint64_mix_hash(v___x_103_, v___x_104_);
v___y_85_ = v___x_105_;
goto v___jp_84_;
}
v___jp_84_:
{
uint64_t v___x_86_; uint64_t v___x_87_; uint64_t v___x_88_; uint64_t v_fold_89_; uint64_t v___x_90_; uint64_t v___x_91_; uint64_t v___x_92_; size_t v___x_93_; size_t v___x_94_; size_t v___x_95_; size_t v___x_96_; size_t v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_86_ = lean_uint64_mix_hash(v___x_83_, v___y_85_);
v___x_87_ = 32ULL;
v___x_88_ = lean_uint64_shift_right(v___x_86_, v___x_87_);
v_fold_89_ = lean_uint64_xor(v___x_86_, v___x_88_);
v___x_90_ = 16ULL;
v___x_91_ = lean_uint64_shift_right(v_fold_89_, v___x_90_);
v___x_92_ = lean_uint64_xor(v_fold_89_, v___x_91_);
v___x_93_ = lean_uint64_to_usize(v___x_92_);
v___x_94_ = lean_usize_of_nat(v___x_82_);
v___x_95_ = ((size_t)1ULL);
v___x_96_ = lean_usize_sub(v___x_94_, v___x_95_);
v___x_97_ = lean_usize_land(v___x_93_, v___x_96_);
v___x_98_ = lean_usize_to_nat(v___x_97_);
v___x_99_ = lean_box(0);
v___x_100_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0___redArg(v_m_77_, v_query_78_, v___x_99_, v___x_82_, v___x_98_);
return v___x_100_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg___boxed(lean_object* v_m_106_, lean_object* v_query_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg(v_m_106_, v_query_107_);
lean_dec_ref(v_query_107_);
lean_dec_ref(v_m_106_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__4___redArg(lean_object* v_b_109_, lean_object* v_acc_110_, lean_object* v_i_111_){
_start:
{
lean_object* v___y_113_; lean_object* v_keyArray_121_; lean_object* v_valueArray_122_; lean_object* v___x_123_; uint8_t v___x_124_; 
v_keyArray_121_ = lean_ctor_get(v_b_109_, 1);
v_valueArray_122_ = lean_ctor_get(v_b_109_, 2);
v___x_123_ = lean_array_get_size(v_keyArray_121_);
v___x_124_ = lean_nat_dec_lt(v_i_111_, v___x_123_);
if (v___x_124_ == 0)
{
lean_dec(v_i_111_);
return v_acc_110_;
}
else
{
lean_object* v___x_125_; uint8_t v_isSome_126_; 
v___x_125_ = lean_array_fget_borrowed(v_keyArray_121_, v_i_111_);
v_isSome_126_ = lean_noption_is_some(v___x_125_);
if (v_isSome_126_ == 0)
{
goto v___jp_117_;
}
else
{
lean_object* v___x_127_; uint8_t v_isSome_128_; 
v___x_127_ = lean_array_fget_borrowed(v_valueArray_122_, v_i_111_);
v_isSome_128_ = lean_noption_is_some(v___x_127_);
if (v_isSome_128_ == 0)
{
goto v___jp_117_;
}
else
{
lean_object* v_val_129_; lean_object* v_val_130_; lean_object* v_i_132_; lean_object* v___x_137_; 
lean_inc(v___x_125_);
v_val_129_ = lean_noption_get(v___x_125_);
lean_inc(v___x_127_);
v_val_130_ = lean_noption_get(v___x_127_);
v___x_137_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg(v_acc_110_, v_val_129_);
switch(lean_obj_tag(v___x_137_))
{
case 0:
{
lean_object* v_index_138_; lean_object* v_size_139_; lean_object* v___x_140_; 
v_index_138_ = lean_ctor_get(v___x_137_, 0);
lean_inc(v_index_138_);
lean_dec_ref_known(v___x_137_, 3);
v_size_139_ = lean_ctor_get(v_acc_110_, 0);
lean_inc(v_size_139_);
v___x_140_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_110_, v_size_139_, v_index_138_, v_val_129_, v_val_130_);
lean_dec(v_index_138_);
v___y_113_ = v___x_140_;
goto v___jp_112_;
}
case 1:
{
lean_object* v_index_141_; 
v_index_141_ = lean_ctor_get(v___x_137_, 0);
lean_inc(v_index_141_);
lean_dec_ref_known(v___x_137_, 1);
v_i_132_ = v_index_141_;
goto v___jp_131_;
}
default: 
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = lean_unsigned_to_nat(0u);
v___x_143_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_110_, v___x_142_);
if (lean_obj_tag(v___x_143_) == 0)
{
lean_object* v_index_144_; 
v_index_144_ = lean_ctor_get(v___x_143_, 0);
lean_inc(v_index_144_);
lean_dec_ref_known(v___x_143_, 1);
v_i_132_ = v_index_144_;
goto v___jp_131_;
}
else
{
lean_dec(v_val_130_);
lean_dec(v_val_129_);
v___y_113_ = v_acc_110_;
goto v___jp_112_;
}
}
}
v___jp_131_:
{
lean_object* v_size_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v_size_133_ = lean_ctor_get(v_acc_110_, 0);
v___x_134_ = lean_unsigned_to_nat(1u);
v___x_135_ = lean_nat_add(v_size_133_, v___x_134_);
v___x_136_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_110_, v___x_135_, v_i_132_, v_val_129_, v_val_130_);
lean_dec(v_i_132_);
v___y_113_ = v___x_136_;
goto v___jp_112_;
}
}
}
}
v___jp_112_:
{
lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_114_ = lean_unsigned_to_nat(1u);
v___x_115_ = lean_nat_add(v_i_111_, v___x_114_);
lean_dec(v_i_111_);
v_acc_110_ = v___y_113_;
v_i_111_ = v___x_115_;
goto _start;
}
v___jp_117_:
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = lean_unsigned_to_nat(1u);
v___x_119_ = lean_nat_add(v_i_111_, v___x_118_);
lean_dec(v_i_111_);
v_i_111_ = v___x_119_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_b_145_, lean_object* v_acc_146_, lean_object* v_i_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__4___redArg(v_b_145_, v_acc_146_, v_i_147_);
lean_dec_ref(v_b_145_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2___redArg(lean_object* v_init_149_, lean_object* v_b_150_){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = lean_unsigned_to_nat(0u);
v___x_152_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__4___redArg(v_b_150_, v_init_149_, v___x_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2___redArg___boxed(lean_object* v_init_153_, lean_object* v_b_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2___redArg(v_init_153_, v_b_154_);
lean_dec_ref(v_b_154_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg(lean_object* v_m_156_){
_start:
{
lean_object* v_keyArray_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v_cellCount_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v_target_164_; lean_object* v___x_165_; 
v_keyArray_157_ = lean_ctor_get(v_m_156_, 1);
v___x_158_ = lean_array_get_size(v_keyArray_157_);
v___x_159_ = lean_unsigned_to_nat(2u);
v_cellCount_160_ = lean_nat_mul(v___x_158_, v___x_159_);
v___x_161_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_160_);
v___x_162_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_160_);
v___x_163_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_160_);
v_target_164_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_164_, 0, v___x_161_);
lean_ctor_set(v_target_164_, 1, v___x_162_);
lean_ctor_set(v_target_164_, 2, v___x_163_);
v___x_165_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2___redArg(v_target_164_, v_m_156_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___boxed(lean_object* v_m_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg(v_m_166_);
lean_dec_ref(v_m_166_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__2(lean_object* v_as_168_, size_t v_sz_169_, size_t v_i_170_, lean_object* v_b_171_){
_start:
{
lean_object* v_a_173_; uint8_t v___x_177_; 
v___x_177_ = lean_usize_dec_lt(v_i_170_, v_sz_169_);
if (v___x_177_ == 0)
{
return v_b_171_;
}
else
{
lean_object* v_fst_178_; lean_object* v_snd_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_256_; 
v_fst_178_ = lean_ctor_get(v_b_171_, 0);
v_snd_179_ = lean_ctor_get(v_b_171_, 1);
v_isSharedCheck_256_ = !lean_is_exclusive(v_b_171_);
if (v_isSharedCheck_256_ == 0)
{
v___x_181_ = v_b_171_;
v_isShared_182_ = v_isSharedCheck_256_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_snd_179_);
lean_inc(v_fst_178_);
lean_dec(v_b_171_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_256_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v_a_183_; lean_object* v_snd_185_; lean_object* v_label_190_; lean_object* v_textEdit_x3f_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___y_195_; lean_object* v_i_196_; lean_object* v___y_202_; lean_object* v___y_212_; lean_object* v_i_213_; lean_object* v___x_228_; 
v_a_183_ = lean_array_uget_borrowed(v_as_168_, v_i_170_);
v_label_190_ = lean_ctor_get(v_a_183_, 0);
v_textEdit_x3f_191_ = lean_ctor_get(v_a_183_, 4);
lean_inc(v_textEdit_x3f_191_);
lean_inc_ref(v_label_190_);
v___x_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_192_, 0, v_label_190_);
lean_ctor_set(v___x_192_, 1, v_textEdit_x3f_191_);
v___x_193_ = lean_box(0);
v___x_228_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg(v_snd_179_, v___x_192_);
switch(lean_obj_tag(v___x_228_))
{
case 0:
{
lean_dec_ref_known(v___x_228_, 3);
lean_dec_ref_known(v___x_192_, 2);
if (v___x_177_ == 0)
{
v_snd_185_ = v_snd_179_;
goto v___jp_184_;
}
else
{
lean_object* v___x_229_; 
lean_del_object(v___x_181_);
v___x_229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_229_, 0, v_fst_178_);
lean_ctor_set(v___x_229_, 1, v_snd_179_);
v_a_173_ = v___x_229_;
goto v___jp_172_;
}
}
case 1:
{
lean_object* v_index_230_; lean_object* v_size_231_; lean_object* v_keyArray_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; uint8_t v___x_236_; 
v_index_230_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_index_230_);
lean_dec_ref_known(v___x_228_, 1);
v_size_231_ = lean_ctor_get(v_snd_179_, 0);
v_keyArray_232_ = lean_ctor_get(v_snd_179_, 1);
v___x_233_ = lean_unsigned_to_nat(1u);
v___x_234_ = lean_nat_add(v_size_231_, v___x_233_);
v___x_235_ = lean_array_get_size(v_keyArray_232_);
v___x_236_ = lean_nat_dec_lt(v___x_234_, v___x_235_);
if (v___x_236_ == 0)
{
lean_dec(v___x_234_);
lean_dec(v_index_230_);
goto v___jp_218_;
}
else
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; uint8_t v___x_241_; 
v___x_237_ = lean_unsigned_to_nat(4u);
v___x_238_ = lean_nat_mul(v___x_234_, v___x_237_);
v___x_239_ = lean_unsigned_to_nat(3u);
v___x_240_ = lean_nat_mul(v___x_235_, v___x_239_);
v___x_241_ = lean_nat_dec_le(v___x_238_, v___x_240_);
lean_dec(v___x_240_);
lean_dec(v___x_238_);
if (v___x_241_ == 0)
{
lean_dec(v___x_234_);
lean_dec(v_index_230_);
goto v___jp_218_;
}
else
{
lean_object* v___x_242_; 
v___x_242_ = l_Std_DHashMap_Raw_setEntry___redArg(v_snd_179_, v___x_234_, v_index_230_, v___x_192_, v___x_193_);
lean_dec(v_index_230_);
v_snd_185_ = v___x_242_;
goto v___jp_184_;
}
}
}
default: 
{
lean_object* v_size_243_; lean_object* v_keyArray_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; uint8_t v___x_248_; 
v_size_243_ = lean_ctor_get(v_snd_179_, 0);
v_keyArray_244_ = lean_ctor_get(v_snd_179_, 1);
v___x_245_ = lean_unsigned_to_nat(1u);
v___x_246_ = lean_nat_add(v_size_243_, v___x_245_);
v___x_247_ = lean_array_get_size(v_keyArray_244_);
v___x_248_ = lean_nat_dec_lt(v___x_246_, v___x_247_);
if (v___x_248_ == 0)
{
lean_object* v___x_249_; 
lean_dec(v___x_246_);
v___x_249_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg(v_snd_179_);
lean_dec(v_snd_179_);
v___y_202_ = v___x_249_;
goto v___jp_201_;
}
else
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; uint8_t v___x_254_; 
v___x_250_ = lean_unsigned_to_nat(4u);
v___x_251_ = lean_nat_mul(v___x_246_, v___x_250_);
lean_dec(v___x_246_);
v___x_252_ = lean_unsigned_to_nat(3u);
v___x_253_ = lean_nat_mul(v___x_247_, v___x_252_);
v___x_254_ = lean_nat_dec_le(v___x_251_, v___x_253_);
lean_dec(v___x_253_);
lean_dec(v___x_251_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; 
v___x_255_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg(v_snd_179_);
lean_dec(v_snd_179_);
v___y_202_ = v___x_255_;
goto v___jp_201_;
}
else
{
v___y_202_ = v_snd_179_;
goto v___jp_201_;
}
}
}
}
v___jp_184_:
{
lean_object* v___x_186_; lean_object* v___x_188_; 
lean_inc(v_a_183_);
v___x_186_ = lean_array_push(v_fst_178_, v_a_183_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 1, v_snd_185_);
lean_ctor_set(v___x_181_, 0, v___x_186_);
v___x_188_ = v___x_181_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v___x_186_);
lean_ctor_set(v_reuseFailAlloc_189_, 1, v_snd_185_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
v_a_173_ = v___x_188_;
goto v___jp_172_;
}
}
v___jp_194_:
{
lean_object* v_size_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v_size_197_ = lean_ctor_get(v___y_195_, 0);
v___x_198_ = lean_unsigned_to_nat(1u);
v___x_199_ = lean_nat_add(v_size_197_, v___x_198_);
v___x_200_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_195_, v___x_199_, v_i_196_, v___x_192_, v___x_193_);
lean_dec(v_i_196_);
v_snd_185_ = v___x_200_;
goto v___jp_184_;
}
v___jp_201_:
{
lean_object* v___x_203_; 
v___x_203_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg(v___y_202_, v___x_192_);
switch(lean_obj_tag(v___x_203_))
{
case 0:
{
lean_object* v_index_204_; lean_object* v_size_205_; lean_object* v___x_206_; 
v_index_204_ = lean_ctor_get(v___x_203_, 0);
lean_inc(v_index_204_);
lean_dec_ref_known(v___x_203_, 3);
v_size_205_ = lean_ctor_get(v___y_202_, 0);
lean_inc(v_size_205_);
v___x_206_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_202_, v_size_205_, v_index_204_, v___x_192_, v___x_193_);
lean_dec(v_index_204_);
v_snd_185_ = v___x_206_;
goto v___jp_184_;
}
case 1:
{
lean_object* v_index_207_; 
v_index_207_ = lean_ctor_get(v___x_203_, 0);
lean_inc(v_index_207_);
lean_dec_ref_known(v___x_203_, 1);
v___y_195_ = v___y_202_;
v_i_196_ = v_index_207_;
goto v___jp_194_;
}
default: 
{
lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_208_ = lean_unsigned_to_nat(0u);
v___x_209_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_202_, v___x_208_);
if (lean_obj_tag(v___x_209_) == 0)
{
lean_object* v_index_210_; 
v_index_210_ = lean_ctor_get(v___x_209_, 0);
lean_inc(v_index_210_);
lean_dec_ref_known(v___x_209_, 1);
v___y_195_ = v___y_202_;
v_i_196_ = v_index_210_;
goto v___jp_194_;
}
else
{
lean_dec_ref_known(v___x_192_, 2);
v_snd_185_ = v___y_202_;
goto v___jp_184_;
}
}
}
}
v___jp_211_:
{
lean_object* v_size_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v_size_214_ = lean_ctor_get(v___y_212_, 0);
v___x_215_ = lean_unsigned_to_nat(1u);
v___x_216_ = lean_nat_add(v_size_214_, v___x_215_);
v___x_217_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_212_, v___x_216_, v_i_213_, v___x_192_, v___x_193_);
lean_dec(v_i_213_);
v_snd_185_ = v___x_217_;
goto v___jp_184_;
}
v___jp_218_:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg(v_snd_179_);
lean_dec(v_snd_179_);
v___x_220_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg(v___x_219_, v___x_192_);
switch(lean_obj_tag(v___x_220_))
{
case 0:
{
lean_object* v_index_221_; lean_object* v_size_222_; lean_object* v___x_223_; 
v_index_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_index_221_);
lean_dec_ref_known(v___x_220_, 3);
v_size_222_ = lean_ctor_get(v___x_219_, 0);
lean_inc(v_size_222_);
v___x_223_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_219_, v_size_222_, v_index_221_, v___x_192_, v___x_193_);
lean_dec(v_index_221_);
v_snd_185_ = v___x_223_;
goto v___jp_184_;
}
case 1:
{
lean_object* v_index_224_; 
v_index_224_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_index_224_);
lean_dec_ref_known(v___x_220_, 1);
v___y_212_ = v___x_219_;
v_i_213_ = v_index_224_;
goto v___jp_211_;
}
default: 
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = lean_unsigned_to_nat(0u);
v___x_226_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_219_, v___x_225_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v_index_227_; 
v_index_227_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_index_227_);
lean_dec_ref_known(v___x_226_, 1);
v___y_212_ = v___x_219_;
v_i_213_ = v_index_227_;
goto v___jp_211_;
}
else
{
lean_dec_ref_known(v___x_192_, 2);
v_snd_185_ = v___x_219_;
goto v___jp_184_;
}
}
}
}
}
}
v___jp_172_:
{
size_t v___x_174_; size_t v___x_175_; 
v___x_174_ = ((size_t)1ULL);
v___x_175_ = lean_usize_add(v_i_170_, v___x_174_);
v_i_170_ = v___x_175_;
v_b_171_ = v_a_173_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__2___boxed(lean_object* v_as_257_, lean_object* v_sz_258_, lean_object* v_i_259_, lean_object* v_b_260_){
_start:
{
size_t v_sz_boxed_261_; size_t v_i_boxed_262_; lean_object* v_res_263_; 
v_sz_boxed_261_ = lean_unbox_usize(v_sz_258_);
lean_dec(v_sz_258_);
v_i_boxed_262_ = lean_unbox_usize(v_i_259_);
lean_dec(v_i_259_);
v_res_263_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__2(v_as_257_, v_sz_boxed_261_, v_i_boxed_262_, v_b_260_);
lean_dec_ref(v_as_257_);
return v_res_263_;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__1(void){
_start:
{
lean_object* v_cellCount_266_; lean_object* v___x_267_; 
v_cellCount_266_ = lean_unsigned_to_nat(16u);
v___x_267_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_266_);
return v___x_267_;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__2(void){
_start:
{
lean_object* v_cellCount_268_; lean_object* v___x_269_; 
v_cellCount_268_ = lean_unsigned_to_nat(16u);
v___x_269_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_268_);
return v___x_269_;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__3(void){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v_index_273_; 
v___x_270_ = lean_obj_once(&l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__2, &l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__2_once, _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__2);
v___x_271_ = lean_obj_once(&l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__1, &l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__1_once, _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__1);
v___x_272_ = lean_unsigned_to_nat(0u);
v_index_273_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_index_273_, 0, v___x_272_);
lean_ctor_set(v_index_273_, 1, v___x_271_);
lean_ctor_set(v_index_273_, 2, v___x_270_);
return v_index_273_;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__4(void){
_start:
{
lean_object* v_index_274_; lean_object* v_r_275_; lean_object* v___x_276_; 
v_index_274_ = lean_obj_once(&l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__3, &l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__3_once, _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__3);
v_r_275_ = ((lean_object*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__0));
v___x_276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_276_, 0, v_r_275_);
lean_ctor_set(v___x_276_, 1, v_index_274_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems(lean_object* v_items_277_){
_start:
{
lean_object* v___x_278_; size_t v_sz_279_; size_t v___x_280_; lean_object* v___x_281_; lean_object* v_fst_282_; 
v___x_278_ = lean_obj_once(&l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__4, &l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__4_once, _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__4);
v_sz_279_ = lean_array_size(v_items_277_);
v___x_280_ = ((size_t)0ULL);
v___x_281_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__2(v_items_277_, v_sz_279_, v___x_280_, v___x_278_);
v_fst_282_ = lean_ctor_get(v___x_281_, 0);
lean_inc(v_fst_282_);
lean_dec_ref(v___x_281_);
return v_fst_282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___boxed(lean_object* v_items_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems(v_items_283_);
lean_dec_ref(v_items_283_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0(lean_object* v_00_u03b2_285_, lean_object* v_m_286_, lean_object* v_query_287_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg(v_m_286_, v_query_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___boxed(lean_object* v_00_u03b2_289_, lean_object* v_m_290_, lean_object* v_query_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0(v_00_u03b2_289_, v_m_290_, v_query_291_);
lean_dec_ref(v_query_291_);
lean_dec_ref(v_m_290_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1(lean_object* v_00_u03b2_293_, lean_object* v_m_294_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg(v_m_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___boxed(lean_object* v_00_u03b2_296_, lean_object* v_m_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1(v_00_u03b2_296_, v_m_297_);
lean_dec_ref(v_m_297_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0(lean_object* v_00_u03b2_299_, lean_object* v_m_300_, lean_object* v_query_301_, lean_object* v_x_302_, lean_object* v_x_303_, lean_object* v_x_304_, lean_object* v_x_305_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0___redArg(v_m_300_, v_query_301_, v_x_302_, v_x_303_, v_x_304_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0___boxed(lean_object* v_00_u03b2_307_, lean_object* v_m_308_, lean_object* v_query_309_, lean_object* v_x_310_, lean_object* v_x_311_, lean_object* v_x_312_, lean_object* v_x_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0(v_00_u03b2_307_, v_m_308_, v_query_309_, v_x_310_, v_x_311_, v_x_312_, v_x_313_);
lean_dec_ref(v_query_309_);
lean_dec_ref(v_m_308_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2(lean_object* v_00_u03b2_315_, lean_object* v_init_316_, lean_object* v_b_317_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2___redArg(v_init_316_, v_b_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2___boxed(lean_object* v_00_u03b2_319_, lean_object* v_init_320_, lean_object* v_b_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2(v_00_u03b2_319_, v_init_320_, v_b_321_);
lean_dec_ref(v_b_321_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_323_, lean_object* v_b_324_, lean_object* v_acc_325_, lean_object* v_i_326_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__4___redArg(v_b_324_, v_acc_325_, v_i_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_328_, lean_object* v_b_329_, lean_object* v_acc_330_, lean_object* v_i_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__4(v_00_u03b2_328_, v_b_329_, v_acc_330_, v_i_331_);
lean_dec_ref(v_b_329_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__0(lean_object* v_uri_333_, lean_object* v_pos_334_, lean_object* v_caps_335_, lean_object* v_as_336_, size_t v_sz_337_, size_t v_i_338_, lean_object* v_b_339_, lean_object* v___y_340_){
_start:
{
lean_object* v_a_343_; lean_object* v_completions_347_; uint8_t v___x_352_; 
v___x_352_ = lean_usize_dec_lt(v_i_338_, v_sz_337_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; lean_object* v___x_354_; 
lean_dec_ref(v_caps_335_);
lean_dec_ref(v_pos_334_);
lean_dec_ref(v_uri_333_);
v___x_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_353_, 0, v_b_339_);
v___x_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
return v___x_354_;
}
else
{
lean_object* v_a_355_; lean_object* v_fst_356_; lean_object* v_snd_357_; lean_object* v___x_358_; 
v_a_355_ = lean_array_uget_borrowed(v_as_336_, v_i_338_);
v_fst_356_ = lean_ctor_get(v_a_355_, 0);
v_snd_357_ = lean_ctor_get(v_a_355_, 1);
v___x_358_ = l_Lean_Server_CancellableM_checkCancelled(v___y_340_);
if (lean_obj_tag(v___x_358_) == 0)
{
lean_object* v_a_359_; 
v_a_359_ = lean_ctor_get(v___x_358_, 0);
lean_inc(v_a_359_);
lean_dec_ref_known(v___x_358_, 1);
if (lean_obj_tag(v_a_359_) == 0)
{
lean_object* v_a_360_; 
lean_dec_ref(v_b_339_);
lean_dec_ref(v_caps_335_);
lean_dec_ref(v_pos_334_);
lean_dec_ref(v_uri_333_);
v_a_360_ = lean_ctor_get(v_a_359_, 0);
lean_inc(v_a_360_);
lean_dec_ref_known(v_a_359_, 1);
v_a_343_ = v_a_360_;
goto v___jp_342_;
}
else
{
lean_object* v_info_361_; 
lean_dec_ref_known(v_a_359_, 1);
v_info_361_ = lean_ctor_get(v_fst_356_, 2);
switch(lean_obj_tag(v_info_361_))
{
case 1:
{
lean_object* v_hoverInfo_362_; lean_object* v_ctx_363_; lean_object* v_stx_364_; lean_object* v_id_365_; uint8_t v_danglingDot_366_; lean_object* v_lctx_367_; lean_object* v___x_368_; 
v_hoverInfo_362_ = lean_ctor_get(v_fst_356_, 0);
v_ctx_363_ = lean_ctor_get(v_fst_356_, 1);
v_stx_364_ = lean_ctor_get(v_info_361_, 0);
v_id_365_ = lean_ctor_get(v_info_361_, 1);
v_danglingDot_366_ = lean_ctor_get_uint8(v_info_361_, sizeof(void*)*4);
v_lctx_367_ = lean_ctor_get(v_info_361_, 2);
lean_inc(v_hoverInfo_362_);
lean_inc(v_id_365_);
lean_inc(v_stx_364_);
lean_inc_ref(v_lctx_367_);
lean_inc_ref(v_ctx_363_);
lean_inc(v_snd_357_);
lean_inc_ref(v_pos_334_);
lean_inc_ref(v_uri_333_);
v___x_368_ = l_Lean_Server_Completion_idCompletion(v_uri_333_, v_pos_334_, v_snd_357_, v_ctx_363_, v_lctx_367_, v_stx_364_, v_id_365_, v_hoverInfo_362_, v_danglingDot_366_, v___y_340_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v_a_369_; 
v_a_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_a_369_);
lean_dec_ref_known(v___x_368_, 1);
if (lean_obj_tag(v_a_369_) == 0)
{
lean_object* v_a_370_; 
lean_dec_ref(v_b_339_);
lean_dec_ref(v_caps_335_);
lean_dec_ref(v_pos_334_);
lean_dec_ref(v_uri_333_);
v_a_370_ = lean_ctor_get(v_a_369_, 0);
lean_inc(v_a_370_);
lean_dec_ref_known(v_a_369_, 1);
v_a_343_ = v_a_370_;
goto v___jp_342_;
}
else
{
lean_object* v_a_371_; 
v_a_371_ = lean_ctor_get(v_a_369_, 0);
lean_inc(v_a_371_);
lean_dec_ref_known(v_a_369_, 1);
v_completions_347_ = v_a_371_;
goto v___jp_346_;
}
}
else
{
lean_dec_ref(v_b_339_);
lean_dec_ref(v_caps_335_);
lean_dec_ref(v_pos_334_);
lean_dec_ref(v_uri_333_);
return v___x_368_;
}
}
case 0:
{
lean_object* v_ctx_372_; lean_object* v_termInfo_373_; lean_object* v___x_374_; 
v_ctx_372_ = lean_ctor_get(v_fst_356_, 1);
v_termInfo_373_ = lean_ctor_get(v_info_361_, 0);
lean_inc_ref(v_termInfo_373_);
lean_inc_ref(v_ctx_372_);
lean_inc(v_snd_357_);
lean_inc_ref(v_pos_334_);
lean_inc_ref(v_uri_333_);
v___x_374_ = l_Lean_Server_Completion_dotCompletion(v_uri_333_, v_pos_334_, v_snd_357_, v_ctx_372_, v_termInfo_373_, v___y_340_);
if (lean_obj_tag(v___x_374_) == 0)
{
lean_object* v_a_375_; 
v_a_375_ = lean_ctor_get(v___x_374_, 0);
lean_inc(v_a_375_);
lean_dec_ref_known(v___x_374_, 1);
if (lean_obj_tag(v_a_375_) == 0)
{
lean_object* v_a_376_; 
lean_dec_ref(v_b_339_);
lean_dec_ref(v_caps_335_);
lean_dec_ref(v_pos_334_);
lean_dec_ref(v_uri_333_);
v_a_376_ = lean_ctor_get(v_a_375_, 0);
lean_inc(v_a_376_);
lean_dec_ref_known(v_a_375_, 1);
v_a_343_ = v_a_376_;
goto v___jp_342_;
}
else
{
lean_object* v_a_377_; 
v_a_377_ = lean_ctor_get(v_a_375_, 0);
lean_inc(v_a_377_);
lean_dec_ref_known(v_a_375_, 1);
v_completions_347_ = v_a_377_;
goto v___jp_346_;
}
}
else
{
lean_dec_ref(v_b_339_);
lean_dec_ref(v_caps_335_);
lean_dec_ref(v_pos_334_);
lean_dec_ref(v_uri_333_);
return v___x_374_;
}
}
case 2:
{
lean_object* v_ctx_378_; lean_object* v_id_379_; lean_object* v_lctx_380_; lean_object* v_expectedType_x3f_381_; lean_object* v___x_382_; 
v_ctx_378_ = lean_ctor_get(v_fst_356_, 1);
v_id_379_ = lean_ctor_get(v_info_361_, 1);
v_lctx_380_ = lean_ctor_get(v_info_361_, 2);
v_expectedType_x3f_381_ = lean_ctor_get(v_info_361_, 3);
lean_inc(v_expectedType_x3f_381_);
lean_inc(v_id_379_);
lean_inc_ref(v_lctx_380_);
lean_inc_ref(v_ctx_378_);
lean_inc(v_snd_357_);
lean_inc_ref(v_pos_334_);
lean_inc_ref(v_uri_333_);
v___x_382_ = l_Lean_Server_Completion_dotIdCompletion(v_uri_333_, v_pos_334_, v_snd_357_, v_ctx_378_, v_lctx_380_, v_id_379_, v_expectedType_x3f_381_, v___y_340_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_object* v_a_383_; 
v_a_383_ = lean_ctor_get(v___x_382_, 0);
lean_inc(v_a_383_);
lean_dec_ref_known(v___x_382_, 1);
if (lean_obj_tag(v_a_383_) == 0)
{
lean_object* v_a_384_; 
lean_dec_ref(v_b_339_);
lean_dec_ref(v_caps_335_);
lean_dec_ref(v_pos_334_);
lean_dec_ref(v_uri_333_);
v_a_384_ = lean_ctor_get(v_a_383_, 0);
lean_inc(v_a_384_);
lean_dec_ref_known(v_a_383_, 1);
v_a_343_ = v_a_384_;
goto v___jp_342_;
}
else
{
lean_object* v_a_385_; 
v_a_385_ = lean_ctor_get(v_a_383_, 0);
lean_inc(v_a_385_);
lean_dec_ref_known(v_a_383_, 1);
v_completions_347_ = v_a_385_;
goto v___jp_346_;
}
}
else
{
lean_dec_ref(v_b_339_);
lean_dec_ref(v_caps_335_);
lean_dec_ref(v_pos_334_);
lean_dec_ref(v_uri_333_);
return v___x_382_;
}
}
case 3:
{
lean_object* v_ctx_386_; lean_object* v_id_387_; lean_object* v_lctx_388_; lean_object* v_structName_389_; lean_object* v___x_390_; 
v_ctx_386_ = lean_ctor_get(v_fst_356_, 1);
v_id_387_ = lean_ctor_get(v_info_361_, 1);
v_lctx_388_ = lean_ctor_get(v_info_361_, 2);
v_structName_389_ = lean_ctor_get(v_info_361_, 3);
lean_inc(v_structName_389_);
lean_inc(v_id_387_);
lean_inc_ref(v_lctx_388_);
lean_inc_ref(v_ctx_386_);
lean_inc(v_snd_357_);
lean_inc_ref(v_pos_334_);
lean_inc_ref(v_uri_333_);
v___x_390_ = l_Lean_Server_Completion_fieldIdCompletion(v_uri_333_, v_pos_334_, v_snd_357_, v_ctx_386_, v_lctx_388_, v_id_387_, v_structName_389_, v___y_340_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v_a_391_; 
v_a_391_ = lean_ctor_get(v___x_390_, 0);
lean_inc(v_a_391_);
lean_dec_ref_known(v___x_390_, 1);
if (lean_obj_tag(v_a_391_) == 0)
{
lean_object* v_a_392_; 
lean_dec_ref(v_b_339_);
lean_dec_ref(v_caps_335_);
lean_dec_ref(v_pos_334_);
lean_dec_ref(v_uri_333_);
v_a_392_ = lean_ctor_get(v_a_391_, 0);
lean_inc(v_a_392_);
lean_dec_ref_known(v_a_391_, 1);
v_a_343_ = v_a_392_;
goto v___jp_342_;
}
else
{
lean_object* v_a_393_; 
v_a_393_ = lean_ctor_get(v_a_391_, 0);
lean_inc(v_a_393_);
lean_dec_ref_known(v_a_391_, 1);
v_completions_347_ = v_a_393_;
goto v___jp_346_;
}
}
else
{
lean_dec_ref(v_b_339_);
lean_dec_ref(v_caps_335_);
lean_dec_ref(v_pos_334_);
lean_dec_ref(v_uri_333_);
return v___x_390_;
}
}
case 5:
{
lean_object* v_ctx_394_; lean_object* v_stx_395_; lean_object* v___x_396_; 
v_ctx_394_ = lean_ctor_get(v_fst_356_, 1);
v_stx_395_ = lean_ctor_get(v_info_361_, 0);
lean_inc_ref(v_caps_335_);
lean_inc(v_stx_395_);
lean_inc_ref(v_ctx_394_);
lean_inc(v_snd_357_);
lean_inc_ref(v_pos_334_);
lean_inc_ref(v_uri_333_);
v___x_396_ = l_Lean_Server_Completion_optionCompletion(v_uri_333_, v_pos_334_, v_snd_357_, v_ctx_394_, v_stx_395_, v_caps_335_);
if (lean_obj_tag(v___x_396_) == 0)
{
lean_object* v_a_397_; 
v_a_397_ = lean_ctor_get(v___x_396_, 0);
lean_inc(v_a_397_);
lean_dec_ref_known(v___x_396_, 1);
v_completions_347_ = v_a_397_;
goto v___jp_346_;
}
else
{
lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_405_; 
lean_dec_ref(v_b_339_);
lean_dec_ref(v_caps_335_);
lean_dec_ref(v_pos_334_);
lean_dec_ref(v_uri_333_);
v_a_398_ = lean_ctor_get(v___x_396_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_405_ == 0)
{
v___x_400_ = v___x_396_;
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v___x_396_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_405_;
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
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_a_398_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
case 6:
{
lean_object* v_ctx_406_; lean_object* v_partialId_407_; lean_object* v___x_408_; 
v_ctx_406_ = lean_ctor_get(v_fst_356_, 1);
v_partialId_407_ = lean_ctor_get(v_info_361_, 1);
lean_inc_ref(v_caps_335_);
lean_inc(v_partialId_407_);
lean_inc_ref(v_ctx_406_);
lean_inc(v_snd_357_);
lean_inc_ref(v_pos_334_);
lean_inc_ref(v_uri_333_);
v___x_408_ = l_Lean_Server_Completion_errorNameCompletion(v_uri_333_, v_pos_334_, v_snd_357_, v_ctx_406_, v_partialId_407_, v_caps_335_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v_a_409_; 
v_a_409_ = lean_ctor_get(v___x_408_, 0);
lean_inc(v_a_409_);
lean_dec_ref_known(v___x_408_, 1);
v_completions_347_ = v_a_409_;
goto v___jp_346_;
}
else
{
lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_417_; 
lean_dec_ref(v_b_339_);
lean_dec_ref(v_caps_335_);
lean_dec_ref(v_pos_334_);
lean_dec_ref(v_uri_333_);
v_a_410_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_417_ == 0)
{
v___x_412_ = v___x_408_;
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___x_408_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_415_; 
if (v_isShared_413_ == 0)
{
v___x_415_ = v___x_412_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_a_410_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
case 7:
{
lean_object* v_id_x3f_418_; uint8_t v_danglingDot_419_; lean_object* v_scopeNames_420_; lean_object* v___x_421_; 
v_id_x3f_418_ = lean_ctor_get(v_info_361_, 1);
v_danglingDot_419_ = lean_ctor_get_uint8(v_info_361_, sizeof(void*)*3);
v_scopeNames_420_ = lean_ctor_get(v_info_361_, 2);
lean_inc(v_scopeNames_420_);
lean_inc(v_id_x3f_418_);
lean_inc(v_snd_357_);
lean_inc_ref(v_pos_334_);
lean_inc_ref(v_uri_333_);
v___x_421_ = l_Lean_Server_Completion_endSectionCompletion(v_uri_333_, v_pos_334_, v_snd_357_, v_id_x3f_418_, v_danglingDot_419_, v_scopeNames_420_);
if (lean_obj_tag(v___x_421_) == 0)
{
lean_object* v_a_422_; 
v_a_422_ = lean_ctor_get(v___x_421_, 0);
lean_inc(v_a_422_);
lean_dec_ref_known(v___x_421_, 1);
v_completions_347_ = v_a_422_;
goto v___jp_346_;
}
else
{
lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_430_; 
lean_dec_ref(v_b_339_);
lean_dec_ref(v_caps_335_);
lean_dec_ref(v_pos_334_);
lean_dec_ref(v_uri_333_);
v_a_423_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_430_ == 0)
{
v___x_425_ = v___x_421_;
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_421_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_428_; 
if (v_isShared_426_ == 0)
{
v___x_428_ = v___x_425_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_a_423_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
case 8:
{
lean_object* v_ctx_431_; lean_object* v___x_432_; 
v_ctx_431_ = lean_ctor_get(v_fst_356_, 1);
lean_inc_ref(v_ctx_431_);
lean_inc(v_snd_357_);
lean_inc_ref(v_pos_334_);
lean_inc_ref(v_uri_333_);
v___x_432_ = l_Lean_Server_Completion_tacticCompletion(v_uri_333_, v_pos_334_, v_snd_357_, v_ctx_431_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v_a_433_; 
v_a_433_ = lean_ctor_get(v___x_432_, 0);
lean_inc(v_a_433_);
lean_dec_ref_known(v___x_432_, 1);
v_completions_347_ = v_a_433_;
goto v___jp_346_;
}
else
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_441_; 
lean_dec_ref(v_b_339_);
lean_dec_ref(v_caps_335_);
lean_dec_ref(v_pos_334_);
lean_dec_ref(v_uri_333_);
v_a_434_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_441_ == 0)
{
v___x_436_ = v___x_432_;
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_432_);
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
default: 
{
lean_object* v_allCompletions_442_; 
v_allCompletions_442_ = ((lean_object*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__0));
v_completions_347_ = v_allCompletions_442_;
goto v___jp_346_;
}
}
}
}
else
{
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_450_; 
lean_dec_ref(v_b_339_);
lean_dec_ref(v_caps_335_);
lean_dec_ref(v_pos_334_);
lean_dec_ref(v_uri_333_);
v_a_443_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_450_ == 0)
{
v___x_445_ = v___x_358_;
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_358_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_448_; 
if (v_isShared_446_ == 0)
{
v___x_448_ = v___x_445_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_a_443_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
}
v___jp_342_:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_344_, 0, v_a_343_);
v___x_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
return v___x_345_;
}
v___jp_346_:
{
lean_object* v___x_348_; size_t v___x_349_; size_t v___x_350_; 
v___x_348_ = l_Array_append___redArg(v_b_339_, v_completions_347_);
lean_dec_ref(v_completions_347_);
v___x_349_ = ((size_t)1ULL);
v___x_350_ = lean_usize_add(v_i_338_, v___x_349_);
v_i_338_ = v___x_350_;
v_b_339_ = v___x_348_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__0___boxed(lean_object* v_uri_451_, lean_object* v_pos_452_, lean_object* v_caps_453_, lean_object* v_as_454_, lean_object* v_sz_455_, lean_object* v_i_456_, lean_object* v_b_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
size_t v_sz_boxed_460_; size_t v_i_boxed_461_; lean_object* v_res_462_; 
v_sz_boxed_460_ = lean_unbox_usize(v_sz_455_);
lean_dec(v_sz_455_);
v_i_boxed_461_ = lean_unbox_usize(v_i_456_);
lean_dec(v_i_456_);
v_res_462_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__0(v_uri_451_, v_pos_452_, v_caps_453_, v_as_454_, v_sz_boxed_460_, v_i_boxed_461_, v_b_457_, v___y_458_);
lean_dec_ref(v___y_458_);
lean_dec_ref(v_as_454_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__1(lean_object* v_uri_463_, lean_object* v_pos_464_, lean_object* v_caps_465_, lean_object* v_as_466_, size_t v_sz_467_, size_t v_i_468_, lean_object* v_b_469_, lean_object* v___y_470_){
_start:
{
uint8_t v___x_472_; 
v___x_472_ = lean_usize_dec_lt(v_i_468_, v_sz_467_);
if (v___x_472_ == 0)
{
lean_object* v___x_473_; lean_object* v___x_474_; 
lean_dec_ref(v_caps_465_);
lean_dec_ref(v_pos_464_);
lean_dec_ref(v_uri_463_);
v___x_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_473_, 0, v_b_469_);
v___x_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
return v___x_474_;
}
else
{
lean_object* v_a_475_; size_t v_sz_476_; size_t v___x_477_; lean_object* v___x_478_; 
v_a_475_ = lean_array_uget_borrowed(v_as_466_, v_i_468_);
v_sz_476_ = lean_array_size(v_a_475_);
v___x_477_ = ((size_t)0ULL);
lean_inc_ref(v_caps_465_);
lean_inc_ref(v_pos_464_);
lean_inc_ref(v_uri_463_);
v___x_478_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__0(v_uri_463_, v_pos_464_, v_caps_465_, v_a_475_, v_sz_476_, v___x_477_, v_b_469_, v___y_470_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_a_479_; 
v_a_479_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_a_479_);
if (lean_obj_tag(v_a_479_) == 0)
{
lean_dec_ref_known(v_a_479_, 1);
lean_dec_ref(v_caps_465_);
lean_dec_ref(v_pos_464_);
lean_dec_ref(v_uri_463_);
return v___x_478_;
}
else
{
lean_object* v_a_480_; lean_object* v___x_481_; lean_object* v___x_482_; uint8_t v___x_483_; 
v_a_480_ = lean_ctor_get(v_a_479_, 0);
lean_inc(v_a_480_);
lean_dec_ref_known(v_a_479_, 1);
v___x_481_ = lean_array_get_size(v_a_480_);
v___x_482_ = lean_unsigned_to_nat(0u);
v___x_483_ = lean_nat_dec_eq(v___x_481_, v___x_482_);
if (v___x_483_ == 0)
{
lean_dec(v_a_480_);
lean_dec_ref(v_caps_465_);
lean_dec_ref(v_pos_464_);
lean_dec_ref(v_uri_463_);
return v___x_478_;
}
else
{
size_t v___x_484_; size_t v___x_485_; 
lean_dec_ref_known(v___x_478_, 1);
v___x_484_ = ((size_t)1ULL);
v___x_485_ = lean_usize_add(v_i_468_, v___x_484_);
v_i_468_ = v___x_485_;
v_b_469_ = v_a_480_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_caps_465_);
lean_dec_ref(v_pos_464_);
lean_dec_ref(v_uri_463_);
return v___x_478_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__1___boxed(lean_object* v_uri_487_, lean_object* v_pos_488_, lean_object* v_caps_489_, lean_object* v_as_490_, lean_object* v_sz_491_, lean_object* v_i_492_, lean_object* v_b_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
size_t v_sz_boxed_496_; size_t v_i_boxed_497_; lean_object* v_res_498_; 
v_sz_boxed_496_ = lean_unbox_usize(v_sz_491_);
lean_dec(v_sz_491_);
v_i_boxed_497_ = lean_unbox_usize(v_i_492_);
lean_dec(v_i_492_);
v_res_498_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__1(v_uri_487_, v_pos_488_, v_caps_489_, v_as_490_, v_sz_boxed_496_, v_i_boxed_497_, v_b_493_, v___y_494_);
lean_dec_ref(v___y_494_);
lean_dec_ref(v_as_490_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_find_x3f(lean_object* v_uri_499_, lean_object* v_pos_500_, lean_object* v_fileMap_501_, lean_object* v_hoverPos_502_, lean_object* v_cmdStx_503_, lean_object* v_infoTree_504_, lean_object* v_caps_505_, lean_object* v_a_506_){
_start:
{
lean_object* v___x_508_; lean_object* v_fst_509_; lean_object* v_snd_510_; lean_object* v_allCompletions_511_; size_t v_sz_512_; size_t v___x_513_; lean_object* v___x_514_; 
v___x_508_ = l_Lean_Server_Completion_findPrioritizedCompletionPartitionsAt(v_fileMap_501_, v_hoverPos_502_, v_cmdStx_503_, v_infoTree_504_);
v_fst_509_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_fst_509_);
v_snd_510_ = lean_ctor_get(v___x_508_, 1);
lean_inc(v_snd_510_);
lean_dec_ref(v___x_508_);
v_allCompletions_511_ = ((lean_object*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__0));
v_sz_512_ = lean_array_size(v_fst_509_);
v___x_513_ = ((size_t)0ULL);
v___x_514_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__1(v_uri_499_, v_pos_500_, v_caps_505_, v_fst_509_, v_sz_512_, v___x_513_, v_allCompletions_511_, v_a_506_);
lean_dec(v_fst_509_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_548_; 
v_a_515_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_548_ == 0)
{
v___x_517_ = v___x_514_;
v_isShared_518_ = v_isSharedCheck_548_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_514_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_548_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
if (lean_obj_tag(v_a_515_) == 0)
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_529_; 
lean_dec(v_snd_510_);
v_a_519_ = lean_ctor_get(v_a_515_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v_a_515_);
if (v_isSharedCheck_529_ == 0)
{
v___x_521_ = v_a_515_;
v_isShared_522_ = v_isSharedCheck_529_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v_a_515_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_529_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_524_; 
if (v_isShared_522_ == 0)
{
v___x_524_ = v___x_521_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_a_519_);
v___x_524_ = v_reuseFailAlloc_528_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
lean_object* v___x_526_; 
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 0, v___x_524_);
v___x_526_ = v___x_517_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_524_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
}
else
{
lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_547_; 
v_a_530_ = lean_ctor_get(v_a_515_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v_a_515_);
if (v_isSharedCheck_547_ == 0)
{
v___x_532_ = v_a_515_;
v_isShared_533_ = v_isSharedCheck_547_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v_a_515_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_547_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_534_; uint8_t v___y_536_; uint8_t v___x_544_; 
v___x_534_ = l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems(v_a_530_);
lean_dec(v_a_530_);
v___x_544_ = lean_unbox(v_snd_510_);
lean_dec(v_snd_510_);
if (v___x_544_ == 0)
{
uint8_t v___x_545_; 
v___x_545_ = 1;
v___y_536_ = v___x_545_;
goto v___jp_535_;
}
else
{
uint8_t v___x_546_; 
v___x_546_ = 0;
v___y_536_ = v___x_546_;
goto v___jp_535_;
}
v___jp_535_:
{
lean_object* v___x_537_; lean_object* v___x_539_; 
v___x_537_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_537_, 0, v___x_534_);
lean_ctor_set_uint8(v___x_537_, sizeof(void*)*1, v___y_536_);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 0, v___x_537_);
v___x_539_ = v___x_532_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_537_);
v___x_539_ = v_reuseFailAlloc_543_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
lean_object* v___x_541_; 
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 0, v___x_539_);
v___x_541_ = v___x_517_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v___x_539_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_556_; 
lean_dec(v_snd_510_);
v_a_549_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_556_ == 0)
{
v___x_551_ = v___x_514_;
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___x_514_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_554_; 
if (v_isShared_552_ == 0)
{
v___x_554_ = v___x_551_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_a_549_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_find_x3f___boxed(lean_object* v_uri_557_, lean_object* v_pos_558_, lean_object* v_fileMap_559_, lean_object* v_hoverPos_560_, lean_object* v_cmdStx_561_, lean_object* v_infoTree_562_, lean_object* v_caps_563_, lean_object* v_a_564_, lean_object* v_a_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lean_Server_Completion_find_x3f(v_uri_557_, v_pos_558_, v_fileMap_559_, v_hoverPos_560_, v_cmdStx_561_, v_infoTree_562_, v_caps_563_, v_a_564_);
lean_dec_ref(v_a_564_);
return v_res_566_;
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
