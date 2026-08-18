// Lean compiler output
// Module: Lean.Linter.Extra.UnnecessarySeqFocus
// Imports: public import Lean.Elab.Command public import Lean.Linter.Basic
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
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_instOrdNat___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instOrdInt___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_lexOrd___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Syntax_instHashableRange_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t l_Lean_Syntax_instBEqRange_beq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Raw_clearCell___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedInfoTree_default;
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_linterSetsExt;
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
extern lean_object* l_Lean_Linter_linterMessageTag;
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_instMonadST(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_instBEqRange_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_instHashableRange_hash___boxed(lean_object*);
lean_object* l_runST___redArg(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_withSetOptionIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addLinter(lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "extra"};
static const lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "unnecessarySeqFocus"};
static const lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(33, 183, 205, 183, 92, 15, 88, 116)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(117, 28, 30, 68, 103, 193, 126, 138)}};
static const lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "enable the 'unnecessary <;>' linter"};
static const lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__5_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__5_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__5_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__7_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__7_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__7_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__8_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Extra"};
static const lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__8_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__8_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__7_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__8_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(179, 148, 165, 15, 81, 68, 12, 199)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(98, 33, 172, 180, 73, 123, 191, 116)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(105, 61, 181, 137, 182, 231, 65, 137)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value_aux_4),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(221, 177, 69, 1, 132, 178, 174, 219)}};
static const lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_linter_extra_unnecessarySeqFocus;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_3107221289____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_3107221289____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_multigoalKindsRef;
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_addBuiltinMultigoalKind(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_addBuiltinMultigoalKind___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnnecessarySeqFocus_addBuiltinMultigoalKinds_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnnecessarySeqFocus_addBuiltinMultigoalKinds_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_addBuiltinMultigoalKinds(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_addBuiltinMultigoalKinds___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__2_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "tacticNext_=>_"};
static const lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__2_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__2_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__3_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__3_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__3_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__3_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__3_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__3_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__3_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__2_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 21, 53, 2, 17, 158, 67, 66)}};
static const lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__3_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__3_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__4_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "allGoals"};
static const lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__4_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__4_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__5_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__5_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__5_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__5_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__5_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__5_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__5_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__4_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(105, 66, 138, 83, 251, 171, 29, 196)}};
static const lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__5_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__5_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "anyGoals"};
static const lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__7_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__7_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__7_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__7_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__7_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__7_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__7_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(168, 19, 163, 3, 232, 106, 175, 32)}};
static const lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__7_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__7_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__8_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "case"};
static const lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__8_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__8_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__8_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(216, 244, 120, 128, 139, 198, 139, 51)}};
static const lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__10_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "case'"};
static const lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__10_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__10_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__11_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__11_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__11_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__11_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__11_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__11_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__11_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__10_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(134, 21, 185, 205, 238, 88, 7, 106)}};
static const lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__11_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__11_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__12_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Conv"};
static const lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__12_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__12_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__13_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "convNext__=>_"};
static const lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__13_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__13_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__14_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__14_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__14_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__14_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__14_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__14_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__14_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__12_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__14_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__14_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__13_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(141, 255, 234, 0, 142, 69, 158, 51)}};
static const lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__14_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__14_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__15_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__15_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__15_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__15_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__15_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__15_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__15_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__12_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__15_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__15_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__4_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(80, 55, 182, 70, 128, 26, 115, 15)}};
static const lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__15_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__15_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__16_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__16_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__16_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__16_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__16_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__16_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__16_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__12_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__16_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__16_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(97, 41, 143, 75, 238, 57, 26, 246)}};
static const lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__16_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__16_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__17_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__17_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__17_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__17_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__17_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__17_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__17_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__12_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__17_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__17_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__8_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(241, 23, 91, 126, 214, 77, 25, 163)}};
static const lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__17_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__17_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__18_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__18_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__18_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__18_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__18_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__18_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__18_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__12_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__18_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__18_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__10_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(151, 157, 98, 160, 189, 128, 94, 31)}};
static const lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__18_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__18_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__19_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "rotateLeft"};
static const lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__19_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__19_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__20_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__20_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__20_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__20_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__20_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__20_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__20_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__19_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(63, 201, 198, 124, 10, 198, 250, 123)}};
static const lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__20_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__20_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__21_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "rotateRight"};
static const lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__21_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__21_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__22_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__22_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__22_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__22_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__22_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__22_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__22_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__21_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(98, 177, 153, 112, 69, 167, 66, 136)}};
static const lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__22_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__22_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__23_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "show"};
static const lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__23_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__23_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__24_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__24_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__24_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__24_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__24_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__24_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__24_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__23_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(151, 147, 62, 103, 130, 224, 84, 63)}};
static const lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__24_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__24_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__25_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "tacticStop_"};
static const lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__25_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__25_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__26_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__26_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__26_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__26_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__26_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__26_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__26_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__25_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(186, 187, 217, 116, 133, 153, 2, 108)}};
static const lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__26_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__26_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_array_object l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__27_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*14, .m_other = 0, .m_tag = 246}, .m_size = 14, .m_capacity = 14, .m_data = {((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__3_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__5_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__7_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__11_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__14_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__15_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__16_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__17_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__18_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__20_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__22_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__24_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__26_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__27_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__27_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Linter_Extra_UnnecessarySeqFocus_isMultigoalKind(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_isMultigoalKind___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "tactic_<;>_"};
static const lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__0 = (const lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__0_value;
static const lean_ctor_object l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__1_value_aux_2),((lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__0_value),LEAN_SCALAR_PTR_LITERAL(31, 118, 44, 159, 195, 11, 47, 176)}};
static const lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__1 = (const lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__1_value;
static const lean_string_object l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "conv_<;>_"};
static const lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__2 = (const lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__2_value;
static const lean_ctor_object l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__12_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__3_value_aux_3),((lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__2_value),LEAN_SCALAR_PTR_LITERAL(139, 57, 152, 10, 187, 180, 111, 39)}};
static const lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__3 = (const lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__3_value;
LEAN_EXPORT uint8_t l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___boxed(lean_object*);
static lean_once_cell_t l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___closed__0;
static lean_once_cell_t l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_instBEqRange_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___closed__2 = (const lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___closed__2_value;
static const lean_closure_object l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_instHashableRange_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___closed__3 = (const lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_getPath(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_getPath___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__5_spec__10_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__5_spec__10_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__5_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__5_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__5___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__4;
static lean_once_cell_t l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__5;
static lean_once_cell_t l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__6;
static lean_once_cell_t l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__0;
static lean_once_cell_t l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1;
static lean_once_cell_t l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__7;
static lean_once_cell_t l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__2;
static lean_once_cell_t l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__3;
static lean_once_cell_t l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__8;
static lean_once_cell_t l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__9;
static const lean_ctor_object l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__10 = (const lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__10_value;
static lean_once_cell_t l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__11;
static lean_once_cell_t l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__12;
static lean_once_cell_t l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__13;
static lean_once_cell_t l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__14;
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__5_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__5_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__5_spec__10_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__5_spec__10_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__0;
static lean_once_cell_t l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__1;
static lean_once_cell_t l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__13(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__13___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "This linter can be disabled with `set_option "};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__0 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__0_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__1;
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " false`"};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__2 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__2_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4_spec__6(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6___redArg___lam__0(lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instOrdNat___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6___redArg___lam__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6___redArg___lam__1___closed__0_value;
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instOrdInt___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6___redArg___lam__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6___redArg___lam__1___closed__1_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1___closed__0 = (const lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1___closed__1 = (const lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__0 = (const lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__0_value;
static const lean_closure_object l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_withSetOptionIn___boxed, .m_arity = 6, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__0_value)} };
static const lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__1 = (const lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__1_value;
static const lean_string_object l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "UnnecessarySeqFocus"};
static const lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__2 = (const lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__2_value;
static const lean_string_object l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "unnecessarySeqFocusLinter"};
static const lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__3 = (const lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__3_value;
static const lean_ctor_object l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__7_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__8_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(179, 148, 165, 15, 81, 68, 12, 199)}};
static const lean_ctor_object l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__4_value_aux_2),((lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__2_value),LEAN_SCALAR_PTR_LITERAL(115, 158, 167, 49, 144, 57, 132, 153)}};
static const lean_ctor_object l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__4_value_aux_3),((lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__3_value),LEAN_SCALAR_PTR_LITERAL(91, 176, 195, 221, 155, 62, 224, 143)}};
static const lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__4 = (const lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__4_value;
static const lean_ctor_object l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__1_value),((lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__4_value)}};
static const lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__5 = (const lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter = (const lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_3917858151____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_3917858151____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v_deprecation_x3f_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_deprecation_x3f_7_ = lean_ctor_get(v_decl_2_, 2);
v___x_8_ = lean_alloc_ctor(1, 0, 1);
v___x_9_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_8_, 0, v___x_9_);
lean_inc(v_deprecation_x3f_7_);
lean_inc_ref(v_descr_6_);
lean_inc_n(v_name_1_, 2);
v___x_10_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_10_, 0, v_name_1_);
lean_ctor_set(v___x_10_, 1, v_ref_3_);
lean_ctor_set(v___x_10_, 2, v___x_8_);
lean_ctor_set(v___x_10_, 3, v_descr_6_);
lean_ctor_set(v___x_10_, 4, v_deprecation_x3f_7_);
v___x_11_ = lean_register_option(v_name_1_, v___x_10_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_19_; 
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; 
v_unused_20_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_20_);
v___x_13_ = v___x_11_;
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
else
{
lean_dec(v___x_11_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
lean_inc(v_defValue_5_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_name_1_);
lean_ctor_set(v___x_15_, 1, v_defValue_5_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_28_; 
lean_dec(v_name_1_);
v_a_21_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_28_ == 0)
{
v___x_23_ = v___x_11_;
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_11_);
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
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_a_21_);
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
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_58_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4_));
v___x_59_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__5_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4_));
v___x_60_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4_));
v___x_61_ = l_Lean_Option_register___at___00__private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__spec__0(v___x_58_, v___x_59_, v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4____boxed(lean_object* v_a_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4_();
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_3107221289____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_65_ = l_Lean_NameSet_empty;
v___x_66_ = lean_st_mk_ref(v___x_65_);
v___x_67_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_67_, 0, v___x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_3107221289____hygCtx___hyg_2____boxed(lean_object* v_a_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_3107221289____hygCtx___hyg_2_();
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_addBuiltinMultigoalKind(lean_object* v_k_70_){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_72_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_multigoalKindsRef;
v___x_73_ = lean_st_ref_take(v___x_72_);
v___x_74_ = l_Lean_NameSet_insert(v___x_73_, v_k_70_);
v___x_75_ = lean_st_ref_put(v___x_72_, v___x_74_);
v___x_76_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_addBuiltinMultigoalKind___boxed(lean_object* v_k_77_, lean_object* v_a_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_addBuiltinMultigoalKind(v_k_77_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnnecessarySeqFocus_addBuiltinMultigoalKinds_spec__0(lean_object* v_as_80_, size_t v_i_81_, size_t v_stop_82_, lean_object* v_b_83_){
_start:
{
uint8_t v___x_84_; 
v___x_84_ = lean_usize_dec_eq(v_i_81_, v_stop_82_);
if (v___x_84_ == 0)
{
lean_object* v___x_85_; lean_object* v___x_86_; size_t v___x_87_; size_t v___x_88_; 
v___x_85_ = lean_array_uget_borrowed(v_as_80_, v_i_81_);
lean_inc(v___x_85_);
v___x_86_ = l_Lean_NameSet_insert(v_b_83_, v___x_85_);
v___x_87_ = ((size_t)1ULL);
v___x_88_ = lean_usize_add(v_i_81_, v___x_87_);
v_i_81_ = v___x_88_;
v_b_83_ = v___x_86_;
goto _start;
}
else
{
return v_b_83_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnnecessarySeqFocus_addBuiltinMultigoalKinds_spec__0___boxed(lean_object* v_as_90_, lean_object* v_i_91_, lean_object* v_stop_92_, lean_object* v_b_93_){
_start:
{
size_t v_i_boxed_94_; size_t v_stop_boxed_95_; lean_object* v_res_96_; 
v_i_boxed_94_ = lean_unbox_usize(v_i_91_);
lean_dec(v_i_91_);
v_stop_boxed_95_ = lean_unbox_usize(v_stop_92_);
lean_dec(v_stop_92_);
v_res_96_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnnecessarySeqFocus_addBuiltinMultigoalKinds_spec__0(v_as_90_, v_i_boxed_94_, v_stop_boxed_95_, v_b_93_);
lean_dec_ref(v_as_90_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_addBuiltinMultigoalKinds(lean_object* v_ks_97_){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___y_102_; lean_object* v___x_105_; lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_99_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_multigoalKindsRef;
v___x_100_ = lean_st_ref_take(v___x_99_);
v___x_105_ = lean_unsigned_to_nat(0u);
v___x_106_ = lean_array_get_size(v_ks_97_);
v___x_107_ = lean_nat_dec_lt(v___x_105_, v___x_106_);
if (v___x_107_ == 0)
{
v___y_102_ = v___x_100_;
goto v___jp_101_;
}
else
{
uint8_t v___x_108_; 
v___x_108_ = lean_nat_dec_le(v___x_106_, v___x_106_);
if (v___x_108_ == 0)
{
if (v___x_107_ == 0)
{
v___y_102_ = v___x_100_;
goto v___jp_101_;
}
else
{
size_t v___x_109_; size_t v___x_110_; lean_object* v___x_111_; 
v___x_109_ = ((size_t)0ULL);
v___x_110_ = lean_usize_of_nat(v___x_106_);
v___x_111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnnecessarySeqFocus_addBuiltinMultigoalKinds_spec__0(v_ks_97_, v___x_109_, v___x_110_, v___x_100_);
v___y_102_ = v___x_111_;
goto v___jp_101_;
}
}
else
{
size_t v___x_112_; size_t v___x_113_; lean_object* v___x_114_; 
v___x_112_ = ((size_t)0ULL);
v___x_113_ = lean_usize_of_nat(v___x_106_);
v___x_114_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnnecessarySeqFocus_addBuiltinMultigoalKinds_spec__0(v_ks_97_, v___x_112_, v___x_113_, v___x_100_);
v___y_102_ = v___x_114_;
goto v___jp_101_;
}
}
v___jp_101_:
{
lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_103_ = lean_st_ref_put(v___x_99_, v___y_102_);
v___x_104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
return v___x_104_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_addBuiltinMultigoalKinds___boxed(lean_object* v_ks_115_, lean_object* v_a_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_addBuiltinMultigoalKinds(v_ks_115_);
lean_dec_ref(v_ks_115_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_237_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__27_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_));
v___x_238_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_addBuiltinMultigoalKinds(v___x_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2____boxed(lean_object* v_a_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_();
return v_res_240_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_Extra_UnnecessarySeqFocus_isMultigoalKind(lean_object* v_k_241_){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_243_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_multigoalKindsRef;
v___x_244_ = lean_st_ref_get(v___x_243_);
v___x_245_ = l_Lean_NameSet_contains(v___x_244_, v_k_241_);
lean_dec(v___x_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_isMultigoalKind___boxed(lean_object* v_k_246_, lean_object* v_a_247_){
_start:
{
uint8_t v_res_248_; lean_object* v_r_249_; 
v_res_248_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_isMultigoalKind(v_k_246_);
lean_dec(v_k_246_);
v_r_249_ = lean_box(v_res_248_);
return v_r_249_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus(lean_object* v_k_263_){
_start:
{
lean_object* v___x_264_; uint8_t v___x_265_; 
v___x_264_ = ((lean_object*)(l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__1));
v___x_265_ = lean_name_eq(v_k_263_, v___x_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; uint8_t v___x_267_; 
v___x_266_ = ((lean_object*)(l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__3));
v___x_267_ = lean_name_eq(v_k_263_, v___x_266_);
return v___x_267_;
}
else
{
return v___x_265_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___boxed(lean_object* v_k_268_){
_start:
{
uint8_t v_res_269_; lean_object* v_r_270_; 
v_res_269_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus(v_k_268_);
lean_dec(v_k_268_);
v_r_270_ = lean_box(v_res_269_);
return v_r_270_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___closed__0(void){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l_instMonadST(lean_box(0));
return v___x_271_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___closed__1(void){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___closed__0, &l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___closed__0_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___closed__0);
v___x_273_ = l_StateRefT_x27_instMonad___redArg(v___x_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___lam__0___boxed(lean_object* v_x_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___lam__0(v_x_274_, v___y_275_, v___y_276_);
lean_dec(v___y_276_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg(lean_object* v_stx_281_, lean_object* v_a_282_){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___closed__1, &l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___closed__1_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___closed__1);
if (lean_obj_tag(v_stx_281_) == 1)
{
lean_object* v_kind_285_; lean_object* v_args_286_; lean_object* v___f_287_; lean_object* v___y_289_; lean_object* v___y_304_; lean_object* v___y_307_; lean_object* v___y_308_; lean_object* v___y_309_; lean_object* v_i_310_; lean_object* v___y_316_; lean_object* v___y_317_; lean_object* v___y_318_; lean_object* v___y_319_; lean_object* v___y_320_; lean_object* v___y_330_; lean_object* v___y_331_; lean_object* v___y_332_; lean_object* v_i_333_; lean_object* v___y_339_; lean_object* v___y_340_; lean_object* v___y_341_; lean_object* v___y_342_; lean_object* v___y_343_; uint8_t v___y_354_; lean_object* v___x_392_; uint8_t v___x_393_; 
v_kind_285_ = lean_ctor_get(v_stx_281_, 1);
v_args_286_ = lean_ctor_get(v_stx_281_, 2);
lean_inc_ref(v_args_286_);
v___f_287_ = lean_alloc_closure((void*)(l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___lam__0___boxed), 4, 0);
v___x_392_ = ((lean_object*)(l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__1));
v___x_393_ = lean_name_eq(v_kind_285_, v___x_392_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; uint8_t v___x_395_; 
v___x_394_ = ((lean_object*)(l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__3));
v___x_395_ = lean_name_eq(v_kind_285_, v___x_394_);
v___y_354_ = v___x_395_;
goto v___jp_353_;
}
else
{
v___y_354_ = v___x_393_;
goto v___jp_353_;
}
v___jp_288_:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; uint8_t v___x_293_; 
v___x_290_ = lean_unsigned_to_nat(0u);
v___x_291_ = lean_array_get_size(v_args_286_);
v___x_292_ = lean_box(0);
v___x_293_ = lean_nat_dec_lt(v___x_290_, v___x_291_);
if (v___x_293_ == 0)
{
lean_dec_ref(v___f_287_);
lean_dec_ref(v_args_286_);
return v___x_292_;
}
else
{
uint8_t v___x_294_; 
v___x_294_ = lean_nat_dec_le(v___x_291_, v___x_291_);
if (v___x_294_ == 0)
{
if (v___x_293_ == 0)
{
lean_dec_ref(v___f_287_);
lean_dec_ref(v_args_286_);
return v___x_292_;
}
else
{
size_t v___x_295_; size_t v___x_296_; lean_object* v___x_1031__overap_297_; lean_object* v___x_298_; 
v___x_295_ = ((size_t)0ULL);
v___x_296_ = lean_usize_of_nat(v___x_291_);
v___x_1031__overap_297_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_284_, v___f_287_, v_args_286_, v___x_295_, v___x_296_, v___x_292_);
lean_inc(v___y_289_);
v___x_298_ = lean_apply_2(v___x_1031__overap_297_, v___y_289_, lean_box(0));
return v___x_298_;
}
}
else
{
size_t v___x_299_; size_t v___x_300_; lean_object* v___x_1036__overap_301_; lean_object* v___x_302_; 
v___x_299_ = ((size_t)0ULL);
v___x_300_ = lean_usize_of_nat(v___x_291_);
v___x_1036__overap_301_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_284_, v___f_287_, v_args_286_, v___x_299_, v___x_300_, v___x_292_);
lean_inc(v___y_289_);
v___x_302_ = lean_apply_2(v___x_1036__overap_301_, v___y_289_, lean_box(0));
return v___x_302_;
}
}
}
v___jp_303_:
{
lean_object* v___x_305_; 
v___x_305_ = lean_st_ref_put(v_a_282_, v___y_304_);
v___y_289_ = v_a_282_;
goto v___jp_288_;
}
v___jp_306_:
{
lean_object* v_size_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v_size_311_ = lean_ctor_get(v___y_308_, 0);
v___x_312_ = lean_unsigned_to_nat(1u);
v___x_313_ = lean_nat_add(v_size_311_, v___x_312_);
v___x_314_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_308_, v___x_313_, v_i_310_, v___y_309_, v___y_307_);
lean_dec(v_i_310_);
v___y_304_ = v___x_314_;
goto v___jp_303_;
}
v___jp_315_:
{
lean_object* v___x_321_; 
lean_inc_ref(v___y_317_);
v___x_321_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___y_318_, v___y_319_, v___y_320_, v___y_317_);
switch(lean_obj_tag(v___x_321_))
{
case 0:
{
lean_object* v_index_322_; lean_object* v_size_323_; lean_object* v___x_324_; 
v_index_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_index_322_);
lean_dec_ref_known(v___x_321_, 3);
v_size_323_ = lean_ctor_get(v___y_320_, 0);
lean_inc(v_size_323_);
v___x_324_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_320_, v_size_323_, v_index_322_, v___y_317_, v___y_316_);
lean_dec(v_index_322_);
v___y_304_ = v___x_324_;
goto v___jp_303_;
}
case 1:
{
lean_object* v_index_325_; 
v_index_325_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_index_325_);
lean_dec_ref_known(v___x_321_, 1);
v___y_307_ = v___y_316_;
v___y_308_ = v___y_320_;
v___y_309_ = v___y_317_;
v_i_310_ = v_index_325_;
goto v___jp_306_;
}
default: 
{
lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_326_ = lean_unsigned_to_nat(0u);
v___x_327_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_320_, v___x_326_);
if (lean_obj_tag(v___x_327_) == 0)
{
lean_object* v_index_328_; 
v_index_328_ = lean_ctor_get(v___x_327_, 0);
lean_inc(v_index_328_);
lean_dec_ref_known(v___x_327_, 1);
v___y_307_ = v___y_316_;
v___y_308_ = v___y_320_;
v___y_309_ = v___y_317_;
v_i_310_ = v_index_328_;
goto v___jp_306_;
}
else
{
lean_dec_ref(v___y_317_);
lean_dec_ref(v___y_316_);
v___y_304_ = v___y_320_;
goto v___jp_303_;
}
}
}
}
v___jp_329_:
{
lean_object* v_size_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v_size_334_ = lean_ctor_get(v___y_332_, 0);
v___x_335_ = lean_unsigned_to_nat(1u);
v___x_336_ = lean_nat_add(v_size_334_, v___x_335_);
v___x_337_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_332_, v___x_336_, v_i_333_, v___y_331_, v___y_330_);
lean_dec(v_i_333_);
v___y_304_ = v___x_337_;
goto v___jp_303_;
}
v___jp_338_:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
lean_inc_ref(v___y_343_);
lean_inc_ref(v___y_342_);
v___x_344_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___y_342_, v___y_343_, v___y_341_);
lean_inc_ref(v___y_340_);
v___x_345_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___y_342_, v___y_343_, v___x_344_, v___y_340_);
switch(lean_obj_tag(v___x_345_))
{
case 0:
{
lean_object* v_index_346_; lean_object* v_size_347_; lean_object* v___x_348_; 
v_index_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_index_346_);
lean_dec_ref_known(v___x_345_, 3);
v_size_347_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_size_347_);
v___x_348_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_344_, v_size_347_, v_index_346_, v___y_340_, v___y_339_);
lean_dec(v_index_346_);
v___y_304_ = v___x_348_;
goto v___jp_303_;
}
case 1:
{
lean_object* v_index_349_; 
v_index_349_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_index_349_);
lean_dec_ref_known(v___x_345_, 1);
v___y_330_ = v___y_339_;
v___y_331_ = v___y_340_;
v___y_332_ = v___x_344_;
v_i_333_ = v_index_349_;
goto v___jp_329_;
}
default: 
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = lean_unsigned_to_nat(0u);
v___x_351_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_344_, v___x_350_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v_index_352_; 
v_index_352_ = lean_ctor_get(v___x_351_, 0);
lean_inc(v_index_352_);
lean_dec_ref_known(v___x_351_, 1);
v___y_330_ = v___y_339_;
v___y_331_ = v___y_340_;
v___y_332_ = v___x_344_;
v_i_333_ = v_index_352_;
goto v___jp_329_;
}
else
{
lean_dec_ref(v___y_340_);
lean_dec_ref(v___y_339_);
v___y_304_ = v___x_344_;
goto v___jp_303_;
}
}
}
}
v___jp_353_:
{
if (v___y_354_ == 0)
{
lean_dec_ref_known(v_stx_281_, 3);
v___y_289_ = v_a_282_;
goto v___jp_288_;
}
else
{
lean_object* v___x_355_; 
v___x_355_ = l_Lean_Syntax_getRange_x3f(v_stx_281_, v___y_354_);
if (lean_obj_tag(v___x_355_) == 1)
{
lean_object* v_val_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; uint8_t v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v_val_356_ = lean_ctor_get(v___x_355_, 0);
lean_inc_n(v_val_356_, 2);
lean_dec_ref_known(v___x_355_, 1);
v___x_357_ = lean_st_ref_take(v_a_282_);
v___x_358_ = ((lean_object*)(l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___closed__2));
v___x_359_ = ((lean_object*)(l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___closed__3));
v___x_360_ = 0;
v___x_361_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_361_, 0, v_stx_281_);
lean_ctor_set_uint8(v___x_361_, sizeof(void*)*1, v___x_360_);
v___x_362_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_358_, v___x_359_, v___x_357_, v_val_356_);
switch(lean_obj_tag(v___x_362_))
{
case 0:
{
lean_object* v_index_363_; lean_object* v_size_364_; lean_object* v___x_365_; 
v_index_363_ = lean_ctor_get(v___x_362_, 0);
lean_inc(v_index_363_);
lean_dec_ref_known(v___x_362_, 3);
v_size_364_ = lean_ctor_get(v___x_357_, 0);
lean_inc(v_size_364_);
v___x_365_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_357_, v_size_364_, v_index_363_, v_val_356_, v___x_361_);
lean_dec(v_index_363_);
v___y_304_ = v___x_365_;
goto v___jp_303_;
}
case 1:
{
lean_object* v_index_366_; lean_object* v_size_367_; lean_object* v_keyArray_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; uint8_t v___x_372_; 
v_index_366_ = lean_ctor_get(v___x_362_, 0);
lean_inc(v_index_366_);
lean_dec_ref_known(v___x_362_, 1);
v_size_367_ = lean_ctor_get(v___x_357_, 0);
lean_inc(v_size_367_);
v_keyArray_368_ = lean_ctor_get(v___x_357_, 1);
lean_inc_ref(v_keyArray_368_);
v___x_369_ = lean_unsigned_to_nat(1u);
v___x_370_ = lean_nat_add(v_size_367_, v___x_369_);
lean_dec(v_size_367_);
v___x_371_ = lean_array_get_size(v_keyArray_368_);
lean_dec_ref(v_keyArray_368_);
v___x_372_ = lean_nat_dec_lt(v___x_370_, v___x_371_);
if (v___x_372_ == 0)
{
lean_dec(v___x_370_);
lean_dec(v_index_366_);
v___y_339_ = v___x_361_;
v___y_340_ = v_val_356_;
v___y_341_ = v___x_357_;
v___y_342_ = v___x_358_;
v___y_343_ = v___x_359_;
goto v___jp_338_;
}
else
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; uint8_t v___x_377_; 
v___x_373_ = lean_unsigned_to_nat(4u);
v___x_374_ = lean_nat_mul(v___x_370_, v___x_373_);
v___x_375_ = lean_unsigned_to_nat(3u);
v___x_376_ = lean_nat_mul(v___x_371_, v___x_375_);
v___x_377_ = lean_nat_dec_le(v___x_374_, v___x_376_);
lean_dec(v___x_376_);
lean_dec(v___x_374_);
if (v___x_377_ == 0)
{
lean_dec(v___x_370_);
lean_dec(v_index_366_);
v___y_339_ = v___x_361_;
v___y_340_ = v_val_356_;
v___y_341_ = v___x_357_;
v___y_342_ = v___x_358_;
v___y_343_ = v___x_359_;
goto v___jp_338_;
}
else
{
lean_object* v___x_378_; 
v___x_378_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_357_, v___x_370_, v_index_366_, v_val_356_, v___x_361_);
lean_dec(v_index_366_);
v___y_304_ = v___x_378_;
goto v___jp_303_;
}
}
}
default: 
{
lean_object* v_size_379_; lean_object* v_keyArray_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; uint8_t v___x_384_; 
v_size_379_ = lean_ctor_get(v___x_357_, 0);
lean_inc(v_size_379_);
v_keyArray_380_ = lean_ctor_get(v___x_357_, 1);
lean_inc_ref(v_keyArray_380_);
v___x_381_ = lean_unsigned_to_nat(1u);
v___x_382_ = lean_nat_add(v_size_379_, v___x_381_);
lean_dec(v_size_379_);
v___x_383_ = lean_array_get_size(v_keyArray_380_);
lean_dec_ref(v_keyArray_380_);
v___x_384_ = lean_nat_dec_lt(v___x_382_, v___x_383_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; 
lean_dec(v___x_382_);
v___x_385_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_358_, v___x_359_, v___x_357_);
v___y_316_ = v___x_361_;
v___y_317_ = v_val_356_;
v___y_318_ = v___x_358_;
v___y_319_ = v___x_359_;
v___y_320_ = v___x_385_;
goto v___jp_315_;
}
else
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_386_ = lean_unsigned_to_nat(4u);
v___x_387_ = lean_nat_mul(v___x_382_, v___x_386_);
lean_dec(v___x_382_);
v___x_388_ = lean_unsigned_to_nat(3u);
v___x_389_ = lean_nat_mul(v___x_383_, v___x_388_);
v___x_390_ = lean_nat_dec_le(v___x_387_, v___x_389_);
lean_dec(v___x_389_);
lean_dec(v___x_387_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; 
v___x_391_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_358_, v___x_359_, v___x_357_);
v___y_316_ = v___x_361_;
v___y_317_ = v_val_356_;
v___y_318_ = v___x_358_;
v___y_319_ = v___x_359_;
v___y_320_ = v___x_391_;
goto v___jp_315_;
}
else
{
v___y_316_ = v___x_361_;
v___y_317_ = v_val_356_;
v___y_318_ = v___x_358_;
v___y_319_ = v___x_359_;
v___y_320_ = v___x_357_;
goto v___jp_315_;
}
}
}
}
}
else
{
lean_dec(v___x_355_);
lean_dec_ref_known(v_stx_281_, 3);
v___y_289_ = v_a_282_;
goto v___jp_288_;
}
}
}
}
else
{
lean_object* v___x_396_; 
lean_dec(v_stx_281_);
v___x_396_ = lean_box(0);
return v___x_396_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___lam__0(lean_object* v_x_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg(v___y_398_, v___y_399_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___boxed(lean_object* v_stx_402_, lean_object* v_a_403_, lean_object* v_a_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg(v_stx_402_, v_a_403_);
lean_dec(v_a_403_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics(lean_object* v_00_u03c9_406_, lean_object* v_stx_407_, lean_object* v_a_408_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg(v_stx_407_, v_a_408_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___boxed(lean_object* v_00_u03c9_411_, lean_object* v_stx_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics(v_00_u03c9_411_, v_stx_412_, v_a_413_);
lean_dec(v_a_413_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_getPath(lean_object* v_x_416_, lean_object* v_x_417_, lean_object* v_x_418_){
_start:
{
if (lean_obj_tag(v_x_418_) == 0)
{
lean_object* v___x_419_; 
lean_dec_ref(v_x_417_);
v___x_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_419_, 0, v_x_416_);
return v___x_419_;
}
else
{
lean_object* v_head_420_; lean_object* v_tail_421_; lean_object* v_fst_422_; lean_object* v_snd_423_; lean_object* v_size_424_; uint8_t v___x_425_; 
lean_dec_ref(v_x_416_);
v_head_420_ = lean_ctor_get(v_x_418_, 0);
v_tail_421_ = lean_ctor_get(v_x_418_, 1);
v_fst_422_ = lean_ctor_get(v_head_420_, 0);
v_snd_423_ = lean_ctor_get(v_head_420_, 1);
v_size_424_ = lean_ctor_get(v_x_417_, 2);
v___x_425_ = lean_nat_dec_eq(v_size_424_, v_fst_422_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; 
lean_dec_ref(v_x_417_);
v___x_426_ = lean_box(0);
return v___x_426_;
}
else
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_428_ = l_Lean_PersistentArray_get_x21___redArg(v___x_427_, v_x_417_, v_snd_423_);
lean_dec_ref(v_x_417_);
if (lean_obj_tag(v___x_428_) == 1)
{
lean_object* v_i_429_; lean_object* v_children_430_; 
v_i_429_ = lean_ctor_get(v___x_428_, 0);
lean_inc_ref(v_i_429_);
v_children_430_ = lean_ctor_get(v___x_428_, 1);
lean_inc_ref(v_children_430_);
lean_dec_ref_known(v___x_428_, 2);
v_x_416_ = v_i_429_;
v_x_417_ = v_children_430_;
v_x_418_ = v_tail_421_;
goto _start;
}
else
{
lean_object* v___x_432_; 
lean_dec(v___x_428_);
v___x_432_ = lean_box(0);
return v___x_432_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_getPath___boxed(lean_object* v_x_433_, lean_object* v_x_434_, lean_object* v_x_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_getPath(v_x_433_, v_x_434_, v_x_435_);
lean_dec(v_x_435_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__8___redArg(lean_object* v_m_437_, lean_object* v_query_438_, lean_object* v_x_439_, lean_object* v_x_440_, lean_object* v_x_441_){
_start:
{
lean_object* v_zero_442_; uint8_t v_isZero_443_; 
v_zero_442_ = lean_unsigned_to_nat(0u);
v_isZero_443_ = lean_nat_dec_eq(v_x_440_, v_zero_442_);
if (v_isZero_443_ == 1)
{
lean_dec(v_x_441_);
lean_dec(v_x_440_);
if (lean_obj_tag(v_x_439_) == 0)
{
lean_object* v___x_444_; 
v___x_444_ = lean_box(2);
return v___x_444_;
}
else
{
lean_object* v_val_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_452_; 
v_val_445_ = lean_ctor_get(v_x_439_, 0);
v_isSharedCheck_452_ = !lean_is_exclusive(v_x_439_);
if (v_isSharedCheck_452_ == 0)
{
v___x_447_ = v_x_439_;
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_val_445_);
lean_dec(v_x_439_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_450_; 
if (v_isShared_448_ == 0)
{
v___x_450_ = v___x_447_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_val_445_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
}
else
{
lean_object* v_keyArray_453_; lean_object* v_valueArray_454_; lean_object* v___x_455_; uint8_t v_isSome_456_; 
v_keyArray_453_ = lean_ctor_get(v_m_437_, 1);
v_valueArray_454_ = lean_ctor_get(v_m_437_, 2);
v___x_455_ = lean_array_fget_borrowed(v_keyArray_453_, v_x_441_);
v_isSome_456_ = lean_noption_is_some(v___x_455_);
if (v_isSome_456_ == 0)
{
lean_dec(v_x_440_);
if (lean_obj_tag(v_x_439_) == 0)
{
lean_object* v___x_457_; 
v___x_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_457_, 0, v_x_441_);
return v___x_457_;
}
else
{
lean_object* v_val_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_465_; 
lean_dec(v_x_441_);
v_val_458_ = lean_ctor_get(v_x_439_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v_x_439_);
if (v_isSharedCheck_465_ == 0)
{
v___x_460_ = v_x_439_;
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_val_458_);
lean_dec(v_x_439_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_463_; 
if (v_isShared_461_ == 0)
{
v___x_463_ = v___x_460_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_val_458_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
else
{
lean_object* v_one_466_; lean_object* v_n_467_; lean_object* v___y_469_; 
v_one_466_ = lean_unsigned_to_nat(1u);
v_n_467_ = lean_nat_sub(v_x_440_, v_one_466_);
lean_dec(v_x_440_);
if (v_isSome_456_ == 0)
{
goto v___jp_475_;
}
else
{
lean_object* v___x_477_; uint8_t v_isSome_478_; 
v___x_477_ = lean_array_fget_borrowed(v_valueArray_454_, v_x_441_);
v_isSome_478_ = lean_noption_is_some(v___x_477_);
if (v_isSome_478_ == 0)
{
goto v___jp_475_;
}
else
{
lean_object* v_val_479_; uint8_t v___x_480_; 
lean_inc(v___x_455_);
v_val_479_ = lean_noption_get(v___x_455_);
v___x_480_ = l_Lean_Syntax_instBEqRange_beq(v_val_479_, v_query_438_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; lean_object* v___x_482_; uint8_t v___x_483_; 
lean_dec(v_val_479_);
v___x_481_ = lean_array_get_size(v_keyArray_453_);
v___x_482_ = lean_nat_add(v_x_441_, v_one_466_);
lean_dec(v_x_441_);
v___x_483_ = lean_nat_dec_lt(v___x_482_, v___x_481_);
if (v___x_483_ == 0)
{
lean_dec(v___x_482_);
v_x_440_ = v_n_467_;
v_x_441_ = v_zero_442_;
goto _start;
}
else
{
v_x_440_ = v_n_467_;
v_x_441_ = v___x_482_;
goto _start;
}
}
else
{
lean_object* v_val_486_; lean_object* v___x_487_; 
lean_dec(v_n_467_);
lean_dec(v_x_439_);
lean_inc(v___x_477_);
v_val_486_ = lean_noption_get(v___x_477_);
v___x_487_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_487_, 0, v_x_441_);
lean_ctor_set(v___x_487_, 1, v_val_479_);
lean_ctor_set(v___x_487_, 2, v_val_486_);
return v___x_487_;
}
}
}
v___jp_468_:
{
lean_object* v___x_470_; lean_object* v___x_471_; uint8_t v___x_472_; 
v___x_470_ = lean_array_get_size(v_keyArray_453_);
v___x_471_ = lean_nat_add(v_x_441_, v_one_466_);
lean_dec(v_x_441_);
v___x_472_ = lean_nat_dec_lt(v___x_471_, v___x_470_);
if (v___x_472_ == 0)
{
lean_dec(v___x_471_);
v_x_439_ = v___y_469_;
v_x_440_ = v_n_467_;
v_x_441_ = v_zero_442_;
goto _start;
}
else
{
v_x_439_ = v___y_469_;
v_x_440_ = v_n_467_;
v_x_441_ = v___x_471_;
goto _start;
}
}
v___jp_475_:
{
if (lean_obj_tag(v_x_439_) == 0)
{
lean_object* v___x_476_; 
lean_inc(v_x_441_);
v___x_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_476_, 0, v_x_441_);
v___y_469_ = v___x_476_;
goto v___jp_468_;
}
else
{
v___y_469_ = v_x_439_;
goto v___jp_468_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__8___redArg___boxed(lean_object* v_m_488_, lean_object* v_query_489_, lean_object* v_x_490_, lean_object* v_x_491_, lean_object* v_x_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__8___redArg(v_m_488_, v_query_489_, v_x_490_, v_x_491_, v_x_492_);
lean_dec_ref(v_query_489_);
lean_dec_ref(v_m_488_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4___redArg(lean_object* v_m_494_, lean_object* v_query_495_){
_start:
{
lean_object* v_keyArray_496_; lean_object* v___x_497_; uint64_t v___x_498_; uint64_t v___x_499_; uint64_t v___x_500_; uint64_t v_fold_501_; uint64_t v___x_502_; uint64_t v___x_503_; uint64_t v___x_504_; size_t v___x_505_; size_t v___x_506_; size_t v___x_507_; size_t v___x_508_; size_t v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v_keyArray_496_ = lean_ctor_get(v_m_494_, 1);
v___x_497_ = lean_array_get_size(v_keyArray_496_);
v___x_498_ = l_Lean_Syntax_instHashableRange_hash(v_query_495_);
v___x_499_ = 32ULL;
v___x_500_ = lean_uint64_shift_right(v___x_498_, v___x_499_);
v_fold_501_ = lean_uint64_xor(v___x_498_, v___x_500_);
v___x_502_ = 16ULL;
v___x_503_ = lean_uint64_shift_right(v_fold_501_, v___x_502_);
v___x_504_ = lean_uint64_xor(v_fold_501_, v___x_503_);
v___x_505_ = lean_uint64_to_usize(v___x_504_);
v___x_506_ = lean_usize_of_nat(v___x_497_);
v___x_507_ = ((size_t)1ULL);
v___x_508_ = lean_usize_sub(v___x_506_, v___x_507_);
v___x_509_ = lean_usize_land(v___x_505_, v___x_508_);
v___x_510_ = lean_usize_to_nat(v___x_509_);
v___x_511_ = lean_box(0);
v___x_512_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__8___redArg(v_m_494_, v_query_495_, v___x_511_, v___x_497_, v___x_510_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4___redArg___boxed(lean_object* v_m_513_, lean_object* v_query_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4___redArg(v_m_513_, v_query_514_);
lean_dec_ref(v_query_514_);
lean_dec_ref(v_m_513_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5___redArg(lean_object* v_m_516_, lean_object* v_query_517_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4___redArg(v_m_516_, v_query_517_);
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v_index_519_; lean_object* v_key_520_; lean_object* v_value_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_528_; 
v_index_519_ = lean_ctor_get(v___x_518_, 0);
v_key_520_ = lean_ctor_get(v___x_518_, 1);
v_value_521_ = lean_ctor_get(v___x_518_, 2);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_528_ == 0)
{
v___x_523_ = v___x_518_;
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_value_521_);
lean_inc(v_key_520_);
lean_inc(v_index_519_);
lean_dec(v___x_518_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_526_; 
if (v_isShared_524_ == 0)
{
v___x_526_ = v___x_523_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_index_519_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v_key_520_);
lean_ctor_set(v_reuseFailAlloc_527_, 2, v_value_521_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
else
{
lean_object* v___x_529_; 
lean_dec(v___x_518_);
v___x_529_ = lean_box(1);
return v___x_529_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5___redArg___boxed(lean_object* v_m_530_, lean_object* v_query_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5___redArg(v_m_530_, v_query_531_);
lean_dec_ref(v_query_531_);
lean_dec_ref(v_m_530_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3___redArg(lean_object* v_m_533_, lean_object* v_a_534_){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5___redArg(v_m_533_, v_a_534_);
if (lean_obj_tag(v___x_535_) == 0)
{
lean_object* v_index_536_; lean_object* v_size_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v_index_536_ = lean_ctor_get(v___x_535_, 0);
lean_inc(v_index_536_);
lean_dec_ref_known(v___x_535_, 3);
v_size_537_ = lean_ctor_get(v_m_533_, 0);
v___x_538_ = lean_unsigned_to_nat(1u);
v___x_539_ = lean_nat_sub(v_size_537_, v___x_538_);
v___x_540_ = l_Std_DHashMap_Raw_clearCell___redArg(v_m_533_, v___x_539_, v_index_536_);
lean_dec(v_index_536_);
return v___x_540_;
}
else
{
return v_m_533_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3___redArg___boxed(lean_object* v_m_541_, lean_object* v_a_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3___redArg(v_m_541_, v_a_542_);
lean_dec_ref(v_a_542_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__5_spec__10_spec__13___redArg(lean_object* v_b_544_, lean_object* v_acc_545_, lean_object* v_i_546_){
_start:
{
lean_object* v___y_548_; lean_object* v_keyArray_556_; lean_object* v_valueArray_557_; lean_object* v___x_558_; uint8_t v___x_559_; 
v_keyArray_556_ = lean_ctor_get(v_b_544_, 1);
v_valueArray_557_ = lean_ctor_get(v_b_544_, 2);
v___x_558_ = lean_array_get_size(v_keyArray_556_);
v___x_559_ = lean_nat_dec_lt(v_i_546_, v___x_558_);
if (v___x_559_ == 0)
{
lean_dec(v_i_546_);
return v_acc_545_;
}
else
{
lean_object* v___x_560_; uint8_t v_isSome_561_; 
v___x_560_ = lean_array_fget_borrowed(v_keyArray_556_, v_i_546_);
v_isSome_561_ = lean_noption_is_some(v___x_560_);
if (v_isSome_561_ == 0)
{
goto v___jp_552_;
}
else
{
lean_object* v___x_562_; uint8_t v_isSome_563_; 
v___x_562_ = lean_array_fget_borrowed(v_valueArray_557_, v_i_546_);
v_isSome_563_ = lean_noption_is_some(v___x_562_);
if (v_isSome_563_ == 0)
{
goto v___jp_552_;
}
else
{
lean_object* v_val_564_; lean_object* v_val_565_; lean_object* v_i_567_; lean_object* v___x_572_; 
lean_inc(v___x_560_);
v_val_564_ = lean_noption_get(v___x_560_);
lean_inc(v___x_562_);
v_val_565_ = lean_noption_get(v___x_562_);
v___x_572_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4___redArg(v_acc_545_, v_val_564_);
switch(lean_obj_tag(v___x_572_))
{
case 0:
{
lean_object* v_index_573_; lean_object* v_size_574_; lean_object* v___x_575_; 
v_index_573_ = lean_ctor_get(v___x_572_, 0);
lean_inc(v_index_573_);
lean_dec_ref_known(v___x_572_, 3);
v_size_574_ = lean_ctor_get(v_acc_545_, 0);
lean_inc(v_size_574_);
v___x_575_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_545_, v_size_574_, v_index_573_, v_val_564_, v_val_565_);
lean_dec(v_index_573_);
v___y_548_ = v___x_575_;
goto v___jp_547_;
}
case 1:
{
lean_object* v_index_576_; 
v_index_576_ = lean_ctor_get(v___x_572_, 0);
lean_inc(v_index_576_);
lean_dec_ref_known(v___x_572_, 1);
v_i_567_ = v_index_576_;
goto v___jp_566_;
}
default: 
{
lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_577_ = lean_unsigned_to_nat(0u);
v___x_578_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_545_, v___x_577_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v_index_579_; 
v_index_579_ = lean_ctor_get(v___x_578_, 0);
lean_inc(v_index_579_);
lean_dec_ref_known(v___x_578_, 1);
v_i_567_ = v_index_579_;
goto v___jp_566_;
}
else
{
lean_dec(v_val_565_);
lean_dec(v_val_564_);
v___y_548_ = v_acc_545_;
goto v___jp_547_;
}
}
}
v___jp_566_:
{
lean_object* v_size_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v_size_568_ = lean_ctor_get(v_acc_545_, 0);
v___x_569_ = lean_unsigned_to_nat(1u);
v___x_570_ = lean_nat_add(v_size_568_, v___x_569_);
v___x_571_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_545_, v___x_570_, v_i_567_, v_val_564_, v_val_565_);
lean_dec(v_i_567_);
v___y_548_ = v___x_571_;
goto v___jp_547_;
}
}
}
}
v___jp_547_:
{
lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_549_ = lean_unsigned_to_nat(1u);
v___x_550_ = lean_nat_add(v_i_546_, v___x_549_);
lean_dec(v_i_546_);
v_acc_545_ = v___y_548_;
v_i_546_ = v___x_550_;
goto _start;
}
v___jp_552_:
{
lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_553_ = lean_unsigned_to_nat(1u);
v___x_554_ = lean_nat_add(v_i_546_, v___x_553_);
lean_dec(v_i_546_);
v_i_546_ = v___x_554_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__5_spec__10_spec__13___redArg___boxed(lean_object* v_b_580_, lean_object* v_acc_581_, lean_object* v_i_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__5_spec__10_spec__13___redArg(v_b_580_, v_acc_581_, v_i_582_);
lean_dec_ref(v_b_580_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__5_spec__10___redArg(lean_object* v_init_584_, lean_object* v_b_585_){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = lean_unsigned_to_nat(0u);
v___x_587_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__5_spec__10_spec__13___redArg(v_b_585_, v_init_584_, v___x_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__5_spec__10___redArg___boxed(lean_object* v_init_588_, lean_object* v_b_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__5_spec__10___redArg(v_init_588_, v_b_589_);
lean_dec_ref(v_b_589_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__5___redArg(lean_object* v_m_591_){
_start:
{
lean_object* v_keyArray_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v_cellCount_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v_target_599_; lean_object* v___x_600_; 
v_keyArray_592_ = lean_ctor_get(v_m_591_, 1);
v___x_593_ = lean_array_get_size(v_keyArray_592_);
v___x_594_ = lean_unsigned_to_nat(2u);
v_cellCount_595_ = lean_nat_mul(v___x_593_, v___x_594_);
v___x_596_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_595_);
v___x_597_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_595_);
v___x_598_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_595_);
v_target_599_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_599_, 0, v___x_596_);
lean_ctor_set(v_target_599_, 1, v___x_597_);
lean_ctor_set(v_target_599_, 2, v___x_598_);
v___x_600_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__5_spec__10___redArg(v_target_599_, v_m_591_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__5___redArg___boxed(lean_object* v_m_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__5___redArg(v_m_601_);
lean_dec_ref(v_m_601_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2___redArg(lean_object* v_m_603_, lean_object* v_a_604_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5___redArg(v_m_603_, v_a_604_);
if (lean_obj_tag(v___x_605_) == 0)
{
lean_object* v_value_606_; lean_object* v___x_607_; 
v_value_606_ = lean_ctor_get(v___x_605_, 2);
lean_inc(v_value_606_);
lean_dec_ref_known(v___x_605_, 3);
v___x_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_607_, 0, v_value_606_);
return v___x_607_;
}
else
{
lean_object* v___x_608_; 
v___x_608_ = lean_box(0);
return v___x_608_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2___redArg___boxed(lean_object* v_m_609_, lean_object* v_a_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2___redArg(v_m_609_, v_a_610_);
lean_dec_ref(v_a_610_);
lean_dec_ref(v_m_609_);
return v_res_611_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_612_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__4(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_613_ = lean_unsigned_to_nat(5u);
v___x_614_ = lean_unsigned_to_nat(0u);
v___x_615_ = lean_nat_mod(v___x_614_, v___x_613_);
return v___x_615_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__5(void){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_616_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__4, &l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__4_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__4);
v___x_617_ = lean_unsigned_to_nat(5u);
v___x_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_618_, 0, v___x_617_);
lean_ctor_set(v___x_618_, 1, v___x_616_);
return v___x_618_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__6(void){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_619_ = lean_box(0);
v___x_620_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__5, &l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__5_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__5);
v___x_621_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
lean_ctor_set(v___x_621_, 1, v___x_619_);
return v___x_621_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__0(void){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_622_ = lean_unsigned_to_nat(1u);
v___x_623_ = lean_unsigned_to_nat(0u);
v___x_624_ = lean_nat_mod(v___x_623_, v___x_622_);
return v___x_624_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1(void){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_625_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__0, &l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__0_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__0);
v___x_626_ = lean_unsigned_to_nat(1u);
v___x_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
lean_ctor_set(v___x_627_, 1, v___x_625_);
return v___x_627_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__7(void){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_628_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__6, &l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__6_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__6);
v___x_629_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1, &l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1);
v___x_630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
lean_ctor_set(v___x_630_, 1, v___x_628_);
return v___x_630_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__2(void){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_631_ = lean_unsigned_to_nat(2u);
v___x_632_ = lean_unsigned_to_nat(1u);
v___x_633_ = lean_nat_mod(v___x_632_, v___x_631_);
return v___x_633_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__3(void){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_634_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__2, &l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__2_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__2);
v___x_635_ = lean_unsigned_to_nat(2u);
v___x_636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
lean_ctor_set(v___x_636_, 1, v___x_634_);
return v___x_636_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__8(void){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_637_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__7, &l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__7_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__7);
v___x_638_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__3, &l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__3_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__3);
v___x_639_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
lean_ctor_set(v___x_639_, 1, v___x_637_);
return v___x_639_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__9(void){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_640_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__8, &l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__8_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__8);
v___x_641_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1, &l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1);
v___x_642_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_641_);
lean_ctor_set(v___x_642_, 1, v___x_640_);
return v___x_642_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__11(void){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_645_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__9, &l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__9_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__9);
v___x_646_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1, &l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1);
v___x_647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_647_, 0, v___x_646_);
lean_ctor_set(v___x_647_, 1, v___x_645_);
return v___x_647_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__12(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_648_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__11, &l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__11_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__11);
v___x_649_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1, &l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1);
v___x_650_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_650_, 0, v___x_649_);
lean_ctor_set(v___x_650_, 1, v___x_648_);
return v___x_650_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__13(void){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_651_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__12, &l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__12_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__12);
v___x_652_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1, &l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1);
v___x_653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_653_, 0, v___x_652_);
lean_ctor_set(v___x_653_, 1, v___x_651_);
return v___x_653_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__14(void){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_654_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__13, &l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__13_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__13);
v___x_655_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1, &l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1);
v___x_656_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
lean_ctor_set(v___x_656_, 1, v___x_654_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg(lean_object* v_multigoals_657_, lean_object* v_x_658_, lean_object* v_a_659_){
_start:
{
switch(lean_obj_tag(v_x_658_))
{
case 0:
{
lean_object* v_t_661_; 
v_t_661_ = lean_ctor_get(v_x_658_, 1);
lean_inc_ref(v_t_661_);
lean_dec_ref_known(v_x_658_, 2);
v_x_658_ = v_t_661_;
goto _start;
}
case 1:
{
lean_object* v_i_663_; lean_object* v_children_664_; lean_object* v_snd_666_; lean_object* v_snd_670_; 
v_i_663_ = lean_ctor_get(v_x_658_, 0);
lean_inc_ref(v_i_663_);
v_children_664_ = lean_ctor_get(v_x_658_, 1);
lean_inc_ref(v_children_664_);
lean_dec_ref_known(v_x_658_, 2);
if (lean_obj_tag(v_i_663_) == 0)
{
lean_object* v_i_673_; lean_object* v_toElabInfo_674_; lean_object* v_goalsBefore_675_; lean_object* v_stx_676_; uint8_t v___x_677_; lean_object* v___x_678_; 
v_i_673_ = lean_ctor_get(v_i_663_, 0);
v_toElabInfo_674_ = lean_ctor_get(v_i_673_, 0);
v_goalsBefore_675_ = lean_ctor_get(v_i_673_, 2);
v_stx_676_ = lean_ctor_get(v_toElabInfo_674_, 1);
v___x_677_ = 1;
v___x_678_ = l_Lean_Syntax_getRange_x3f(v_stx_676_, v___x_677_);
if (lean_obj_tag(v___x_678_) == 1)
{
lean_object* v_val_679_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v_i_683_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v_i_702_; lean_object* v___y_708_; lean_object* v___y_709_; lean_object* v___y_720_; lean_object* v___y_723_; lean_object* v___y_724_; lean_object* v_i_725_; lean_object* v___y_731_; lean_object* v___y_732_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v_i_744_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___x_761_; lean_object* v___x_762_; 
v_val_679_ = lean_ctor_get(v___x_678_, 0);
lean_inc(v_val_679_);
lean_dec_ref_known(v___x_678_, 1);
v___x_761_ = lean_st_ref_get(v_a_659_);
v___x_762_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2___redArg(v___x_761_, v_val_679_);
lean_dec(v___x_761_);
if (lean_obj_tag(v___x_762_) == 1)
{
lean_object* v_val_763_; lean_object* v___y_765_; uint8_t v___y_766_; lean_object* v___x_806_; lean_object* v___x_807_; uint8_t v___x_808_; lean_object* v___y_810_; uint8_t v___y_864_; 
v_val_763_ = lean_ctor_get(v___x_762_, 0);
lean_inc(v_val_763_);
lean_dec_ref_known(v___x_762_, 1);
lean_inc(v_stx_676_);
v___x_806_ = l_Lean_Syntax_getKind(v_stx_676_);
v___x_807_ = ((lean_object*)(l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__1));
v___x_808_ = lean_name_eq(v___x_806_, v___x_807_);
if (v___x_808_ == 0)
{
lean_object* v___x_866_; uint8_t v___x_867_; lean_object* v___y_869_; uint8_t v___y_885_; 
v___x_866_ = ((lean_object*)(l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__3));
v___x_867_ = lean_name_eq(v___x_806_, v___x_866_);
lean_dec(v___x_806_);
if (v___x_867_ == 0)
{
lean_object* v___x_887_; 
lean_dec(v_val_763_);
lean_dec(v_val_679_);
lean_dec_ref_known(v_i_663_, 1);
v___x_887_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___redArg(v_multigoals_657_, v_children_664_, v_a_659_);
lean_dec_ref(v_children_664_);
return v___x_887_;
}
else
{
lean_object* v___x_888_; lean_object* v___x_889_; uint8_t v___x_890_; 
v___x_888_ = l_List_lengthTR___redArg(v_goalsBefore_675_);
v___x_889_ = lean_unsigned_to_nat(1u);
v___x_890_ = lean_nat_dec_eq(v___x_888_, v___x_889_);
lean_dec(v___x_888_);
if (v___x_890_ == 0)
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; uint8_t v___x_894_; 
v___x_891_ = lean_unsigned_to_nat(0u);
v___x_892_ = l_Lean_Syntax_getArg(v_stx_676_, v___x_891_);
v___x_893_ = l_Lean_Syntax_getKind(v___x_892_);
v___x_894_ = l_Lean_NameSet_contains(v_multigoals_657_, v___x_893_);
lean_dec(v___x_893_);
if (v___x_894_ == 0)
{
v___y_885_ = v___x_867_;
goto v___jp_884_;
}
else
{
v___y_885_ = v___x_890_;
goto v___jp_884_;
}
}
else
{
goto v___jp_871_;
}
}
v___jp_868_:
{
lean_object* v___x_870_; 
v___x_870_ = lean_st_ref_take(v_a_659_);
if (lean_obj_tag(v___y_869_) == 0)
{
v___y_765_ = v___x_870_;
v___y_766_ = v___x_808_;
goto v___jp_764_;
}
else
{
v___y_765_ = v___x_870_;
v___y_766_ = v___x_867_;
goto v___jp_764_;
}
}
v___jp_871_:
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_872_ = lean_unsigned_to_nat(1u);
v___x_873_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__14, &l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__14_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__14);
lean_inc_ref(v_children_664_);
v___x_874_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_getPath(v_i_663_, v_children_664_, v___x_873_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v___x_875_; 
v___x_875_ = lean_box(0);
v___y_869_ = v___x_875_;
goto v___jp_868_;
}
else
{
lean_object* v_val_876_; 
v_val_876_ = lean_ctor_get(v___x_874_, 0);
lean_inc(v_val_876_);
lean_dec_ref_known(v___x_874_, 1);
if (lean_obj_tag(v_val_876_) == 0)
{
lean_object* v_i_877_; lean_object* v_goalsAfter_878_; lean_object* v___x_879_; uint8_t v___x_880_; 
v_i_877_ = lean_ctor_get(v_val_876_, 0);
lean_inc_ref(v_i_877_);
lean_dec_ref_known(v_val_876_, 1);
v_goalsAfter_878_ = lean_ctor_get(v_i_877_, 4);
lean_inc(v_goalsAfter_878_);
lean_dec_ref(v_i_877_);
v___x_879_ = l_List_lengthTR___redArg(v_goalsAfter_878_);
lean_dec(v_goalsAfter_878_);
v___x_880_ = lean_nat_dec_eq(v___x_879_, v___x_872_);
lean_dec(v___x_879_);
if (v___x_880_ == 0)
{
lean_object* v___x_881_; 
v___x_881_ = lean_box(0);
v___y_869_ = v___x_881_;
goto v___jp_868_;
}
else
{
lean_object* v___x_882_; 
v___x_882_ = ((lean_object*)(l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__10));
v___y_869_ = v___x_882_;
goto v___jp_868_;
}
}
else
{
lean_object* v___x_883_; 
lean_dec(v_val_876_);
v___x_883_ = lean_box(0);
v___y_869_ = v___x_883_;
goto v___jp_868_;
}
}
}
v___jp_884_:
{
if (v___y_885_ == 0)
{
lean_object* v___x_886_; 
lean_dec_ref_known(v_i_663_, 1);
v___x_886_ = lean_box(0);
v___y_869_ = v___x_886_;
goto v___jp_868_;
}
else
{
goto v___jp_871_;
}
}
}
else
{
lean_object* v___x_895_; lean_object* v___x_896_; uint8_t v___x_897_; 
lean_dec(v___x_806_);
v___x_895_ = l_List_lengthTR___redArg(v_goalsBefore_675_);
v___x_896_ = lean_unsigned_to_nat(1u);
v___x_897_ = lean_nat_dec_eq(v___x_895_, v___x_896_);
lean_dec(v___x_895_);
if (v___x_897_ == 0)
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; uint8_t v___x_901_; 
v___x_898_ = lean_unsigned_to_nat(0u);
v___x_899_ = l_Lean_Syntax_getArg(v_stx_676_, v___x_898_);
v___x_900_ = l_Lean_Syntax_getKind(v___x_899_);
v___x_901_ = l_Lean_NameSet_contains(v_multigoals_657_, v___x_900_);
lean_dec(v___x_900_);
if (v___x_901_ == 0)
{
v___y_864_ = v___x_808_;
goto v___jp_863_;
}
else
{
v___y_864_ = v___x_897_;
goto v___jp_863_;
}
}
else
{
goto v___jp_850_;
}
}
v___jp_764_:
{
if (v___y_766_ == 0)
{
lean_object* v___x_767_; 
lean_dec(v_val_763_);
v___x_767_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3___redArg(v___y_765_, v_val_679_);
lean_dec(v_val_679_);
v_snd_670_ = v___x_767_;
goto v___jp_669_;
}
else
{
lean_object* v_stx_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_805_; 
v_stx_768_ = lean_ctor_get(v_val_763_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v_val_763_);
if (v_isSharedCheck_805_ == 0)
{
v___x_770_ = v_val_763_;
v_isShared_771_ = v_isSharedCheck_805_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_stx_768_);
lean_dec(v_val_763_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_805_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
if (v_isShared_771_ == 0)
{
v___x_773_ = v___x_770_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_stx_768_);
v___x_773_ = v_reuseFailAlloc_804_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
lean_object* v___x_774_; 
lean_ctor_set_uint8(v___x_773_, sizeof(void*)*1, v___x_677_);
v___x_774_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4___redArg(v___y_765_, v_val_679_);
switch(lean_obj_tag(v___x_774_))
{
case 0:
{
lean_object* v_index_775_; lean_object* v_size_776_; lean_object* v___x_777_; 
v_index_775_ = lean_ctor_get(v___x_774_, 0);
lean_inc(v_index_775_);
lean_dec_ref_known(v___x_774_, 3);
v_size_776_ = lean_ctor_get(v___y_765_, 0);
lean_inc(v_size_776_);
v___x_777_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_765_, v_size_776_, v_index_775_, v_val_679_, v___x_773_);
lean_dec(v_index_775_);
v_snd_670_ = v___x_777_;
goto v___jp_669_;
}
case 1:
{
lean_object* v_index_778_; lean_object* v_size_779_; lean_object* v_keyArray_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; uint8_t v___x_784_; 
v_index_778_ = lean_ctor_get(v___x_774_, 0);
lean_inc(v_index_778_);
lean_dec_ref_known(v___x_774_, 1);
v_size_779_ = lean_ctor_get(v___y_765_, 0);
v_keyArray_780_ = lean_ctor_get(v___y_765_, 1);
v___x_781_ = lean_unsigned_to_nat(1u);
v___x_782_ = lean_nat_add(v_size_779_, v___x_781_);
v___x_783_ = lean_array_get_size(v_keyArray_780_);
v___x_784_ = lean_nat_dec_lt(v___x_782_, v___x_783_);
if (v___x_784_ == 0)
{
lean_dec(v___x_782_);
lean_dec(v_index_778_);
v___y_708_ = v___y_765_;
v___y_709_ = v___x_773_;
goto v___jp_707_;
}
else
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; uint8_t v___x_789_; 
v___x_785_ = lean_unsigned_to_nat(4u);
v___x_786_ = lean_nat_mul(v___x_782_, v___x_785_);
v___x_787_ = lean_unsigned_to_nat(3u);
v___x_788_ = lean_nat_mul(v___x_783_, v___x_787_);
v___x_789_ = lean_nat_dec_le(v___x_786_, v___x_788_);
lean_dec(v___x_788_);
lean_dec(v___x_786_);
if (v___x_789_ == 0)
{
lean_dec(v___x_782_);
lean_dec(v_index_778_);
v___y_708_ = v___y_765_;
v___y_709_ = v___x_773_;
goto v___jp_707_;
}
else
{
lean_object* v___x_790_; 
v___x_790_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_765_, v___x_782_, v_index_778_, v_val_679_, v___x_773_);
lean_dec(v_index_778_);
v_snd_670_ = v___x_790_;
goto v___jp_669_;
}
}
}
default: 
{
lean_object* v_size_791_; lean_object* v_keyArray_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; uint8_t v___x_796_; 
v_size_791_ = lean_ctor_get(v___y_765_, 0);
v_keyArray_792_ = lean_ctor_get(v___y_765_, 1);
v___x_793_ = lean_unsigned_to_nat(1u);
v___x_794_ = lean_nat_add(v_size_791_, v___x_793_);
v___x_795_ = lean_array_get_size(v_keyArray_792_);
v___x_796_ = lean_nat_dec_lt(v___x_794_, v___x_795_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; 
lean_dec(v___x_794_);
v___x_797_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__5___redArg(v___y_765_);
lean_dec_ref(v___y_765_);
v___y_689_ = v___x_773_;
v___y_690_ = v___x_797_;
goto v___jp_688_;
}
else
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; uint8_t v___x_802_; 
v___x_798_ = lean_unsigned_to_nat(4u);
v___x_799_ = lean_nat_mul(v___x_794_, v___x_798_);
lean_dec(v___x_794_);
v___x_800_ = lean_unsigned_to_nat(3u);
v___x_801_ = lean_nat_mul(v___x_795_, v___x_800_);
v___x_802_ = lean_nat_dec_le(v___x_799_, v___x_801_);
lean_dec(v___x_801_);
lean_dec(v___x_799_);
if (v___x_802_ == 0)
{
lean_object* v___x_803_; 
v___x_803_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__5___redArg(v___y_765_);
lean_dec_ref(v___y_765_);
v___y_689_ = v___x_773_;
v___y_690_ = v___x_803_;
goto v___jp_688_;
}
else
{
v___y_689_ = v___x_773_;
v___y_690_ = v___y_765_;
goto v___jp_688_;
}
}
}
}
}
}
}
}
v___jp_809_:
{
lean_object* v___x_811_; 
v___x_811_ = lean_st_ref_take(v_a_659_);
if (lean_obj_tag(v___y_810_) == 0)
{
lean_dec(v_val_763_);
v___y_720_ = v___x_811_;
goto v___jp_719_;
}
else
{
if (v___x_808_ == 0)
{
lean_dec(v_val_763_);
v___y_720_ = v___x_811_;
goto v___jp_719_;
}
else
{
lean_object* v_stx_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_849_; 
v_stx_812_ = lean_ctor_get(v_val_763_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v_val_763_);
if (v_isSharedCheck_849_ == 0)
{
v___x_814_ = v_val_763_;
v_isShared_815_ = v_isSharedCheck_849_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_stx_812_);
lean_dec(v_val_763_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_849_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_stx_812_);
v___x_817_ = v_reuseFailAlloc_848_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
lean_object* v___x_818_; 
lean_ctor_set_uint8(v___x_817_, sizeof(void*)*1, v___x_677_);
v___x_818_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4___redArg(v___x_811_, v_val_679_);
switch(lean_obj_tag(v___x_818_))
{
case 0:
{
lean_object* v_index_819_; lean_object* v_size_820_; lean_object* v___x_821_; 
v_index_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc(v_index_819_);
lean_dec_ref_known(v___x_818_, 3);
v_size_820_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_size_820_);
v___x_821_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_811_, v_size_820_, v_index_819_, v_val_679_, v___x_817_);
lean_dec(v_index_819_);
v_snd_666_ = v___x_821_;
goto v___jp_665_;
}
case 1:
{
lean_object* v_index_822_; lean_object* v_size_823_; lean_object* v_keyArray_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; uint8_t v___x_828_; 
v_index_822_ = lean_ctor_get(v___x_818_, 0);
lean_inc(v_index_822_);
lean_dec_ref_known(v___x_818_, 1);
v_size_823_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_size_823_);
v_keyArray_824_ = lean_ctor_get(v___x_811_, 1);
lean_inc_ref(v_keyArray_824_);
v___x_825_ = lean_unsigned_to_nat(1u);
v___x_826_ = lean_nat_add(v_size_823_, v___x_825_);
lean_dec(v_size_823_);
v___x_827_ = lean_array_get_size(v_keyArray_824_);
lean_dec_ref(v_keyArray_824_);
v___x_828_ = lean_nat_dec_lt(v___x_826_, v___x_827_);
if (v___x_828_ == 0)
{
lean_dec(v___x_826_);
lean_dec(v_index_822_);
v___y_750_ = v___x_817_;
v___y_751_ = v___x_811_;
goto v___jp_749_;
}
else
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; uint8_t v___x_833_; 
v___x_829_ = lean_unsigned_to_nat(4u);
v___x_830_ = lean_nat_mul(v___x_826_, v___x_829_);
v___x_831_ = lean_unsigned_to_nat(3u);
v___x_832_ = lean_nat_mul(v___x_827_, v___x_831_);
v___x_833_ = lean_nat_dec_le(v___x_830_, v___x_832_);
lean_dec(v___x_832_);
lean_dec(v___x_830_);
if (v___x_833_ == 0)
{
lean_dec(v___x_826_);
lean_dec(v_index_822_);
v___y_750_ = v___x_817_;
v___y_751_ = v___x_811_;
goto v___jp_749_;
}
else
{
lean_object* v___x_834_; 
v___x_834_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_811_, v___x_826_, v_index_822_, v_val_679_, v___x_817_);
lean_dec(v_index_822_);
v_snd_666_ = v___x_834_;
goto v___jp_665_;
}
}
}
default: 
{
lean_object* v_size_835_; lean_object* v_keyArray_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; uint8_t v___x_840_; 
v_size_835_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_size_835_);
v_keyArray_836_ = lean_ctor_get(v___x_811_, 1);
lean_inc_ref(v_keyArray_836_);
v___x_837_ = lean_unsigned_to_nat(1u);
v___x_838_ = lean_nat_add(v_size_835_, v___x_837_);
lean_dec(v_size_835_);
v___x_839_ = lean_array_get_size(v_keyArray_836_);
lean_dec_ref(v_keyArray_836_);
v___x_840_ = lean_nat_dec_lt(v___x_838_, v___x_839_);
if (v___x_840_ == 0)
{
lean_object* v___x_841_; 
lean_dec(v___x_838_);
v___x_841_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__5___redArg(v___x_811_);
lean_dec(v___x_811_);
v___y_731_ = v___x_817_;
v___y_732_ = v___x_841_;
goto v___jp_730_;
}
else
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; uint8_t v___x_846_; 
v___x_842_ = lean_unsigned_to_nat(4u);
v___x_843_ = lean_nat_mul(v___x_838_, v___x_842_);
lean_dec(v___x_838_);
v___x_844_ = lean_unsigned_to_nat(3u);
v___x_845_ = lean_nat_mul(v___x_839_, v___x_844_);
v___x_846_ = lean_nat_dec_le(v___x_843_, v___x_845_);
lean_dec(v___x_845_);
lean_dec(v___x_843_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; 
v___x_847_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__5___redArg(v___x_811_);
lean_dec(v___x_811_);
v___y_731_ = v___x_817_;
v___y_732_ = v___x_847_;
goto v___jp_730_;
}
else
{
v___y_731_ = v___x_817_;
v___y_732_ = v___x_811_;
goto v___jp_730_;
}
}
}
}
}
}
}
}
}
v___jp_850_:
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_851_ = lean_unsigned_to_nat(1u);
v___x_852_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__9, &l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__9_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__9);
lean_inc_ref(v_children_664_);
v___x_853_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_getPath(v_i_663_, v_children_664_, v___x_852_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v___x_854_; 
v___x_854_ = lean_box(0);
v___y_810_ = v___x_854_;
goto v___jp_809_;
}
else
{
lean_object* v_val_855_; 
v_val_855_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_val_855_);
lean_dec_ref_known(v___x_853_, 1);
if (lean_obj_tag(v_val_855_) == 0)
{
lean_object* v_i_856_; lean_object* v_goalsAfter_857_; lean_object* v___x_858_; uint8_t v___x_859_; 
v_i_856_ = lean_ctor_get(v_val_855_, 0);
lean_inc_ref(v_i_856_);
lean_dec_ref_known(v_val_855_, 1);
v_goalsAfter_857_ = lean_ctor_get(v_i_856_, 4);
lean_inc(v_goalsAfter_857_);
lean_dec_ref(v_i_856_);
v___x_858_ = l_List_lengthTR___redArg(v_goalsAfter_857_);
lean_dec(v_goalsAfter_857_);
v___x_859_ = lean_nat_dec_eq(v___x_858_, v___x_851_);
lean_dec(v___x_858_);
if (v___x_859_ == 0)
{
lean_object* v___x_860_; 
v___x_860_ = lean_box(0);
v___y_810_ = v___x_860_;
goto v___jp_809_;
}
else
{
lean_object* v___x_861_; 
v___x_861_ = ((lean_object*)(l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__10));
v___y_810_ = v___x_861_;
goto v___jp_809_;
}
}
else
{
lean_object* v___x_862_; 
lean_dec(v_val_855_);
v___x_862_ = lean_box(0);
v___y_810_ = v___x_862_;
goto v___jp_809_;
}
}
}
v___jp_863_:
{
if (v___y_864_ == 0)
{
lean_object* v___x_865_; 
lean_dec_ref_known(v_i_663_, 1);
v___x_865_ = lean_box(0);
v___y_810_ = v___x_865_;
goto v___jp_809_;
}
else
{
goto v___jp_850_;
}
}
}
else
{
lean_object* v___x_902_; 
lean_dec(v___x_762_);
lean_dec(v_val_679_);
lean_dec_ref_known(v_i_663_, 1);
v___x_902_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___redArg(v_multigoals_657_, v_children_664_, v_a_659_);
lean_dec_ref(v_children_664_);
return v___x_902_;
}
v___jp_680_:
{
lean_object* v_size_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v_size_684_ = lean_ctor_get(v___y_681_, 0);
v___x_685_ = lean_unsigned_to_nat(1u);
v___x_686_ = lean_nat_add(v_size_684_, v___x_685_);
v___x_687_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_681_, v___x_686_, v_i_683_, v_val_679_, v___y_682_);
lean_dec(v_i_683_);
v_snd_670_ = v___x_687_;
goto v___jp_669_;
}
v___jp_688_:
{
lean_object* v___x_691_; 
v___x_691_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4___redArg(v___y_690_, v_val_679_);
switch(lean_obj_tag(v___x_691_))
{
case 0:
{
lean_object* v_index_692_; lean_object* v_size_693_; lean_object* v___x_694_; 
v_index_692_ = lean_ctor_get(v___x_691_, 0);
lean_inc(v_index_692_);
lean_dec_ref_known(v___x_691_, 3);
v_size_693_ = lean_ctor_get(v___y_690_, 0);
lean_inc(v_size_693_);
v___x_694_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_690_, v_size_693_, v_index_692_, v_val_679_, v___y_689_);
lean_dec(v_index_692_);
v_snd_670_ = v___x_694_;
goto v___jp_669_;
}
case 1:
{
lean_object* v_index_695_; 
v_index_695_ = lean_ctor_get(v___x_691_, 0);
lean_inc(v_index_695_);
lean_dec_ref_known(v___x_691_, 1);
v___y_681_ = v___y_690_;
v___y_682_ = v___y_689_;
v_i_683_ = v_index_695_;
goto v___jp_680_;
}
default: 
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = lean_unsigned_to_nat(0u);
v___x_697_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_690_, v___x_696_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v_index_698_; 
v_index_698_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_index_698_);
lean_dec_ref_known(v___x_697_, 1);
v___y_681_ = v___y_690_;
v___y_682_ = v___y_689_;
v_i_683_ = v_index_698_;
goto v___jp_680_;
}
else
{
lean_dec_ref(v___y_689_);
lean_dec(v_val_679_);
v_snd_670_ = v___y_690_;
goto v___jp_669_;
}
}
}
}
v___jp_699_:
{
lean_object* v_size_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v_size_703_ = lean_ctor_get(v___y_700_, 0);
v___x_704_ = lean_unsigned_to_nat(1u);
v___x_705_ = lean_nat_add(v_size_703_, v___x_704_);
v___x_706_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_700_, v___x_705_, v_i_702_, v_val_679_, v___y_701_);
lean_dec(v_i_702_);
v_snd_670_ = v___x_706_;
goto v___jp_669_;
}
v___jp_707_:
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__5___redArg(v___y_708_);
lean_dec_ref(v___y_708_);
v___x_711_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4___redArg(v___x_710_, v_val_679_);
switch(lean_obj_tag(v___x_711_))
{
case 0:
{
lean_object* v_index_712_; lean_object* v_size_713_; lean_object* v___x_714_; 
v_index_712_ = lean_ctor_get(v___x_711_, 0);
lean_inc(v_index_712_);
lean_dec_ref_known(v___x_711_, 3);
v_size_713_ = lean_ctor_get(v___x_710_, 0);
lean_inc(v_size_713_);
v___x_714_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_710_, v_size_713_, v_index_712_, v_val_679_, v___y_709_);
lean_dec(v_index_712_);
v_snd_670_ = v___x_714_;
goto v___jp_669_;
}
case 1:
{
lean_object* v_index_715_; 
v_index_715_ = lean_ctor_get(v___x_711_, 0);
lean_inc(v_index_715_);
lean_dec_ref_known(v___x_711_, 1);
v___y_700_ = v___x_710_;
v___y_701_ = v___y_709_;
v_i_702_ = v_index_715_;
goto v___jp_699_;
}
default: 
{
lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_716_ = lean_unsigned_to_nat(0u);
v___x_717_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_710_, v___x_716_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_index_718_; 
v_index_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_index_718_);
lean_dec_ref_known(v___x_717_, 1);
v___y_700_ = v___x_710_;
v___y_701_ = v___y_709_;
v_i_702_ = v_index_718_;
goto v___jp_699_;
}
else
{
lean_dec_ref(v___y_709_);
lean_dec(v_val_679_);
v_snd_670_ = v___x_710_;
goto v___jp_669_;
}
}
}
}
v___jp_719_:
{
lean_object* v___x_721_; 
v___x_721_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3___redArg(v___y_720_, v_val_679_);
lean_dec(v_val_679_);
v_snd_666_ = v___x_721_;
goto v___jp_665_;
}
v___jp_722_:
{
lean_object* v_size_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v_size_726_ = lean_ctor_get(v___y_723_, 0);
v___x_727_ = lean_unsigned_to_nat(1u);
v___x_728_ = lean_nat_add(v_size_726_, v___x_727_);
v___x_729_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_723_, v___x_728_, v_i_725_, v_val_679_, v___y_724_);
lean_dec(v_i_725_);
v_snd_666_ = v___x_729_;
goto v___jp_665_;
}
v___jp_730_:
{
lean_object* v___x_733_; 
v___x_733_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4___redArg(v___y_732_, v_val_679_);
switch(lean_obj_tag(v___x_733_))
{
case 0:
{
lean_object* v_index_734_; lean_object* v_size_735_; lean_object* v___x_736_; 
v_index_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_index_734_);
lean_dec_ref_known(v___x_733_, 3);
v_size_735_ = lean_ctor_get(v___y_732_, 0);
lean_inc(v_size_735_);
v___x_736_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_732_, v_size_735_, v_index_734_, v_val_679_, v___y_731_);
lean_dec(v_index_734_);
v_snd_666_ = v___x_736_;
goto v___jp_665_;
}
case 1:
{
lean_object* v_index_737_; 
v_index_737_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_index_737_);
lean_dec_ref_known(v___x_733_, 1);
v___y_723_ = v___y_732_;
v___y_724_ = v___y_731_;
v_i_725_ = v_index_737_;
goto v___jp_722_;
}
default: 
{
lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_738_ = lean_unsigned_to_nat(0u);
v___x_739_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_732_, v___x_738_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_index_740_; 
v_index_740_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_index_740_);
lean_dec_ref_known(v___x_739_, 1);
v___y_723_ = v___y_732_;
v___y_724_ = v___y_731_;
v_i_725_ = v_index_740_;
goto v___jp_722_;
}
else
{
lean_dec_ref(v___y_731_);
lean_dec(v_val_679_);
v_snd_666_ = v___y_732_;
goto v___jp_665_;
}
}
}
}
v___jp_741_:
{
lean_object* v_size_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v_size_745_ = lean_ctor_get(v___y_742_, 0);
v___x_746_ = lean_unsigned_to_nat(1u);
v___x_747_ = lean_nat_add(v_size_745_, v___x_746_);
v___x_748_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_742_, v___x_747_, v_i_744_, v_val_679_, v___y_743_);
lean_dec(v_i_744_);
v_snd_666_ = v___x_748_;
goto v___jp_665_;
}
v___jp_749_:
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__5___redArg(v___y_751_);
lean_dec_ref(v___y_751_);
v___x_753_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4___redArg(v___x_752_, v_val_679_);
switch(lean_obj_tag(v___x_753_))
{
case 0:
{
lean_object* v_index_754_; lean_object* v_size_755_; lean_object* v___x_756_; 
v_index_754_ = lean_ctor_get(v___x_753_, 0);
lean_inc(v_index_754_);
lean_dec_ref_known(v___x_753_, 3);
v_size_755_ = lean_ctor_get(v___x_752_, 0);
lean_inc(v_size_755_);
v___x_756_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_752_, v_size_755_, v_index_754_, v_val_679_, v___y_750_);
lean_dec(v_index_754_);
v_snd_666_ = v___x_756_;
goto v___jp_665_;
}
case 1:
{
lean_object* v_index_757_; 
v_index_757_ = lean_ctor_get(v___x_753_, 0);
lean_inc(v_index_757_);
lean_dec_ref_known(v___x_753_, 1);
v___y_742_ = v___x_752_;
v___y_743_ = v___y_750_;
v_i_744_ = v_index_757_;
goto v___jp_741_;
}
default: 
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = lean_unsigned_to_nat(0u);
v___x_759_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_752_, v___x_758_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_index_760_; 
v_index_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_index_760_);
lean_dec_ref_known(v___x_759_, 1);
v___y_742_ = v___x_752_;
v___y_743_ = v___y_750_;
v_i_744_ = v_index_760_;
goto v___jp_741_;
}
else
{
lean_dec_ref(v___y_750_);
lean_dec(v_val_679_);
v_snd_666_ = v___x_752_;
goto v___jp_665_;
}
}
}
}
}
else
{
lean_object* v___x_903_; 
lean_dec(v___x_678_);
lean_dec_ref_known(v_i_663_, 1);
v___x_903_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___redArg(v_multigoals_657_, v_children_664_, v_a_659_);
lean_dec_ref(v_children_664_);
return v___x_903_;
}
}
else
{
lean_object* v___x_904_; 
lean_dec_ref(v_i_663_);
v___x_904_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___redArg(v_multigoals_657_, v_children_664_, v_a_659_);
lean_dec_ref(v_children_664_);
return v___x_904_;
}
v___jp_665_:
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = lean_st_ref_put(v_a_659_, v_snd_666_);
v___x_668_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___redArg(v_multigoals_657_, v_children_664_, v_a_659_);
lean_dec_ref(v_children_664_);
return v___x_668_;
}
v___jp_669_:
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = lean_st_ref_put(v_a_659_, v_snd_670_);
v___x_672_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___redArg(v_multigoals_657_, v_children_664_, v_a_659_);
lean_dec_ref(v_children_664_);
return v___x_672_;
}
}
default: 
{
lean_object* v___x_905_; 
lean_dec_ref_known(v_x_658_, 1);
v___x_905_ = lean_box(0);
return v___x_905_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(lean_object* v_multigoals_906_, lean_object* v_as_907_, size_t v_i_908_, size_t v_stop_909_, lean_object* v_b_910_, lean_object* v___y_911_){
_start:
{
uint8_t v___x_913_; 
v___x_913_ = lean_usize_dec_eq(v_i_908_, v_stop_909_);
if (v___x_913_ == 0)
{
lean_object* v___x_914_; lean_object* v___x_915_; size_t v___x_916_; size_t v___x_917_; 
v___x_914_ = lean_array_uget_borrowed(v_as_907_, v_i_908_);
lean_inc(v___x_914_);
v___x_915_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg(v_multigoals_906_, v___x_914_, v___y_911_);
v___x_916_ = ((size_t)1ULL);
v___x_917_ = lean_usize_add(v_i_908_, v___x_916_);
v_i_908_ = v___x_917_;
v_b_910_ = v___x_915_;
goto _start;
}
else
{
return v_b_910_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2___redArg(lean_object* v_multigoals_919_, lean_object* v_x_920_, lean_object* v___y_921_){
_start:
{
if (lean_obj_tag(v_x_920_) == 0)
{
lean_object* v_cs_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; uint8_t v___x_927_; 
v_cs_923_ = lean_ctor_get(v_x_920_, 0);
v___x_924_ = lean_unsigned_to_nat(0u);
v___x_925_ = lean_array_get_size(v_cs_923_);
v___x_926_ = lean_box(0);
v___x_927_ = lean_nat_dec_lt(v___x_924_, v___x_925_);
if (v___x_927_ == 0)
{
return v___x_926_;
}
else
{
uint8_t v___x_928_; 
v___x_928_ = lean_nat_dec_le(v___x_925_, v___x_925_);
if (v___x_928_ == 0)
{
if (v___x_927_ == 0)
{
return v___x_926_;
}
else
{
size_t v___x_929_; size_t v___x_930_; lean_object* v___x_931_; 
v___x_929_ = ((size_t)0ULL);
v___x_930_ = lean_usize_of_nat(v___x_925_);
v___x_931_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___redArg(v_multigoals_919_, v_cs_923_, v___x_929_, v___x_930_, v___x_926_, v___y_921_);
return v___x_931_;
}
}
else
{
size_t v___x_932_; size_t v___x_933_; lean_object* v___x_934_; 
v___x_932_ = ((size_t)0ULL);
v___x_933_ = lean_usize_of_nat(v___x_925_);
v___x_934_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___redArg(v_multigoals_919_, v_cs_923_, v___x_932_, v___x_933_, v___x_926_, v___y_921_);
return v___x_934_;
}
}
}
else
{
lean_object* v_vs_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; uint8_t v___x_939_; 
v_vs_935_ = lean_ctor_get(v_x_920_, 0);
v___x_936_ = lean_unsigned_to_nat(0u);
v___x_937_ = lean_array_get_size(v_vs_935_);
v___x_938_ = lean_box(0);
v___x_939_ = lean_nat_dec_lt(v___x_936_, v___x_937_);
if (v___x_939_ == 0)
{
return v___x_938_;
}
else
{
uint8_t v___x_940_; 
v___x_940_ = lean_nat_dec_le(v___x_937_, v___x_937_);
if (v___x_940_ == 0)
{
if (v___x_939_ == 0)
{
return v___x_938_;
}
else
{
size_t v___x_941_; size_t v___x_942_; lean_object* v___x_943_; 
v___x_941_ = ((size_t)0ULL);
v___x_942_ = lean_usize_of_nat(v___x_937_);
v___x_943_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_919_, v_vs_935_, v___x_941_, v___x_942_, v___x_938_, v___y_921_);
return v___x_943_;
}
}
else
{
size_t v___x_944_; size_t v___x_945_; lean_object* v___x_946_; 
v___x_944_ = ((size_t)0ULL);
v___x_945_ = lean_usize_of_nat(v___x_937_);
v___x_946_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_919_, v_vs_935_, v___x_944_, v___x_945_, v___x_938_, v___y_921_);
return v___x_946_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___redArg(lean_object* v_multigoals_947_, lean_object* v_as_948_, size_t v_i_949_, size_t v_stop_950_, lean_object* v_b_951_, lean_object* v___y_952_){
_start:
{
uint8_t v___x_954_; 
v___x_954_ = lean_usize_dec_eq(v_i_949_, v_stop_950_);
if (v___x_954_ == 0)
{
lean_object* v___x_955_; lean_object* v___x_956_; size_t v___x_957_; size_t v___x_958_; 
v___x_955_ = lean_array_uget_borrowed(v_as_948_, v_i_949_);
v___x_956_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2___redArg(v_multigoals_947_, v___x_955_, v___y_952_);
v___x_957_ = ((size_t)1ULL);
v___x_958_ = lean_usize_add(v_i_949_, v___x_957_);
v_i_949_ = v___x_958_;
v_b_951_ = v___x_956_;
goto _start;
}
else
{
return v_b_951_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg(lean_object* v_multigoals_960_, lean_object* v_x_961_, size_t v_x_962_, size_t v_x_963_, lean_object* v___y_964_){
_start:
{
if (lean_obj_tag(v_x_961_) == 0)
{
lean_object* v_cs_966_; lean_object* v___x_967_; size_t v___x_968_; lean_object* v_j_969_; lean_object* v___x_970_; size_t v___x_971_; size_t v___x_972_; size_t v___x_973_; size_t v___x_974_; size_t v___x_975_; size_t v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; uint8_t v___x_982_; 
v_cs_966_ = lean_ctor_get(v_x_961_, 0);
v___x_967_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg___closed__0);
v___x_968_ = lean_usize_shift_right(v_x_962_, v_x_963_);
v_j_969_ = lean_usize_to_nat(v___x_968_);
v___x_970_ = lean_array_get_borrowed(v___x_967_, v_cs_966_, v_j_969_);
v___x_971_ = ((size_t)1ULL);
v___x_972_ = lean_usize_shift_left(v___x_971_, v_x_963_);
v___x_973_ = lean_usize_sub(v___x_972_, v___x_971_);
v___x_974_ = lean_usize_land(v_x_962_, v___x_973_);
v___x_975_ = ((size_t)5ULL);
v___x_976_ = lean_usize_sub(v_x_963_, v___x_975_);
v___x_977_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg(v_multigoals_960_, v___x_970_, v___x_974_, v___x_976_, v___y_964_);
v___x_978_ = lean_unsigned_to_nat(1u);
v___x_979_ = lean_nat_add(v_j_969_, v___x_978_);
lean_dec(v_j_969_);
v___x_980_ = lean_array_get_size(v_cs_966_);
v___x_981_ = lean_box(0);
v___x_982_ = lean_nat_dec_lt(v___x_979_, v___x_980_);
if (v___x_982_ == 0)
{
lean_dec(v___x_979_);
return v___x_981_;
}
else
{
uint8_t v___x_983_; 
v___x_983_ = lean_nat_dec_le(v___x_980_, v___x_980_);
if (v___x_983_ == 0)
{
if (v___x_982_ == 0)
{
lean_dec(v___x_979_);
return v___x_981_;
}
else
{
size_t v___x_984_; size_t v___x_985_; lean_object* v___x_986_; 
v___x_984_ = lean_usize_of_nat(v___x_979_);
lean_dec(v___x_979_);
v___x_985_ = lean_usize_of_nat(v___x_980_);
v___x_986_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___redArg(v_multigoals_960_, v_cs_966_, v___x_984_, v___x_985_, v___x_981_, v___y_964_);
return v___x_986_;
}
}
else
{
size_t v___x_987_; size_t v___x_988_; lean_object* v___x_989_; 
v___x_987_ = lean_usize_of_nat(v___x_979_);
lean_dec(v___x_979_);
v___x_988_ = lean_usize_of_nat(v___x_980_);
v___x_989_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___redArg(v_multigoals_960_, v_cs_966_, v___x_987_, v___x_988_, v___x_981_, v___y_964_);
return v___x_989_;
}
}
}
else
{
lean_object* v_vs_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; uint8_t v___x_994_; 
v_vs_990_ = lean_ctor_get(v_x_961_, 0);
v___x_991_ = lean_usize_to_nat(v_x_962_);
v___x_992_ = lean_array_get_size(v_vs_990_);
v___x_993_ = lean_box(0);
v___x_994_ = lean_nat_dec_lt(v___x_991_, v___x_992_);
if (v___x_994_ == 0)
{
lean_dec(v___x_991_);
return v___x_993_;
}
else
{
uint8_t v___x_995_; 
v___x_995_ = lean_nat_dec_le(v___x_992_, v___x_992_);
if (v___x_995_ == 0)
{
if (v___x_994_ == 0)
{
lean_dec(v___x_991_);
return v___x_993_;
}
else
{
size_t v___x_996_; size_t v___x_997_; lean_object* v___x_998_; 
v___x_996_ = lean_usize_of_nat(v___x_991_);
lean_dec(v___x_991_);
v___x_997_ = lean_usize_of_nat(v___x_992_);
v___x_998_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_960_, v_vs_990_, v___x_996_, v___x_997_, v___x_993_, v___y_964_);
return v___x_998_;
}
}
else
{
size_t v___x_999_; size_t v___x_1000_; lean_object* v___x_1001_; 
v___x_999_ = lean_usize_of_nat(v___x_991_);
lean_dec(v___x_991_);
v___x_1000_ = lean_usize_of_nat(v___x_992_);
v___x_1001_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_960_, v_vs_990_, v___x_999_, v___x_1000_, v___x_993_, v___y_964_);
return v___x_1001_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2___redArg(lean_object* v_multigoals_1002_, lean_object* v_t_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v_root_1006_; lean_object* v_tail_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; uint8_t v___x_1012_; 
v_root_1006_ = lean_ctor_get(v_t_1003_, 0);
v_tail_1007_ = lean_ctor_get(v_t_1003_, 1);
v___x_1008_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2___redArg(v_multigoals_1002_, v_root_1006_, v___y_1004_);
v___x_1009_ = lean_unsigned_to_nat(0u);
v___x_1010_ = lean_array_get_size(v_tail_1007_);
v___x_1011_ = lean_box(0);
v___x_1012_ = lean_nat_dec_lt(v___x_1009_, v___x_1010_);
if (v___x_1012_ == 0)
{
return v___x_1011_;
}
else
{
uint8_t v___x_1013_; 
v___x_1013_ = lean_nat_dec_le(v___x_1010_, v___x_1010_);
if (v___x_1013_ == 0)
{
if (v___x_1012_ == 0)
{
return v___x_1011_;
}
else
{
size_t v___x_1014_; size_t v___x_1015_; lean_object* v___x_1016_; 
v___x_1014_ = ((size_t)0ULL);
v___x_1015_ = lean_usize_of_nat(v___x_1010_);
v___x_1016_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_1002_, v_tail_1007_, v___x_1014_, v___x_1015_, v___x_1011_, v___y_1004_);
return v___x_1016_;
}
}
else
{
size_t v___x_1017_; size_t v___x_1018_; lean_object* v___x_1019_; 
v___x_1017_ = ((size_t)0ULL);
v___x_1018_ = lean_usize_of_nat(v___x_1010_);
v___x_1019_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_1002_, v_tail_1007_, v___x_1017_, v___x_1018_, v___x_1011_, v___y_1004_);
return v___x_1019_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0___redArg(lean_object* v_multigoals_1020_, lean_object* v_t_1021_, lean_object* v_start_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v___x_1025_; uint8_t v___x_1026_; 
v___x_1025_ = lean_unsigned_to_nat(0u);
v___x_1026_ = lean_nat_dec_eq(v_start_1022_, v___x_1025_);
if (v___x_1026_ == 0)
{
lean_object* v_root_1027_; lean_object* v_tail_1028_; size_t v_shift_1029_; lean_object* v_tailOff_1030_; uint8_t v___x_1031_; 
v_root_1027_ = lean_ctor_get(v_t_1021_, 0);
v_tail_1028_ = lean_ctor_get(v_t_1021_, 1);
v_shift_1029_ = lean_ctor_get_usize(v_t_1021_, 4);
v_tailOff_1030_ = lean_ctor_get(v_t_1021_, 3);
v___x_1031_ = lean_nat_dec_le(v_tailOff_1030_, v_start_1022_);
if (v___x_1031_ == 0)
{
size_t v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; uint8_t v___x_1036_; 
v___x_1032_ = lean_usize_of_nat(v_start_1022_);
v___x_1033_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg(v_multigoals_1020_, v_root_1027_, v___x_1032_, v_shift_1029_, v___y_1023_);
v___x_1034_ = lean_array_get_size(v_tail_1028_);
v___x_1035_ = lean_box(0);
v___x_1036_ = lean_nat_dec_lt(v___x_1025_, v___x_1034_);
if (v___x_1036_ == 0)
{
return v___x_1035_;
}
else
{
uint8_t v___x_1037_; 
v___x_1037_ = lean_nat_dec_le(v___x_1034_, v___x_1034_);
if (v___x_1037_ == 0)
{
if (v___x_1036_ == 0)
{
return v___x_1035_;
}
else
{
size_t v___x_1038_; size_t v___x_1039_; lean_object* v___x_1040_; 
v___x_1038_ = ((size_t)0ULL);
v___x_1039_ = lean_usize_of_nat(v___x_1034_);
v___x_1040_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_1020_, v_tail_1028_, v___x_1038_, v___x_1039_, v___x_1035_, v___y_1023_);
return v___x_1040_;
}
}
else
{
size_t v___x_1041_; size_t v___x_1042_; lean_object* v___x_1043_; 
v___x_1041_ = ((size_t)0ULL);
v___x_1042_ = lean_usize_of_nat(v___x_1034_);
v___x_1043_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_1020_, v_tail_1028_, v___x_1041_, v___x_1042_, v___x_1035_, v___y_1023_);
return v___x_1043_;
}
}
}
else
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; uint8_t v___x_1047_; 
v___x_1044_ = lean_nat_sub(v_start_1022_, v_tailOff_1030_);
v___x_1045_ = lean_array_get_size(v_tail_1028_);
v___x_1046_ = lean_box(0);
v___x_1047_ = lean_nat_dec_lt(v___x_1044_, v___x_1045_);
if (v___x_1047_ == 0)
{
lean_dec(v___x_1044_);
return v___x_1046_;
}
else
{
uint8_t v___x_1048_; 
v___x_1048_ = lean_nat_dec_le(v___x_1045_, v___x_1045_);
if (v___x_1048_ == 0)
{
if (v___x_1047_ == 0)
{
lean_dec(v___x_1044_);
return v___x_1046_;
}
else
{
size_t v___x_1049_; size_t v___x_1050_; lean_object* v___x_1051_; 
v___x_1049_ = lean_usize_of_nat(v___x_1044_);
lean_dec(v___x_1044_);
v___x_1050_ = lean_usize_of_nat(v___x_1045_);
v___x_1051_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_1020_, v_tail_1028_, v___x_1049_, v___x_1050_, v___x_1046_, v___y_1023_);
return v___x_1051_;
}
}
else
{
size_t v___x_1052_; size_t v___x_1053_; lean_object* v___x_1054_; 
v___x_1052_ = lean_usize_of_nat(v___x_1044_);
lean_dec(v___x_1044_);
v___x_1053_ = lean_usize_of_nat(v___x_1045_);
v___x_1054_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_1020_, v_tail_1028_, v___x_1052_, v___x_1053_, v___x_1046_, v___y_1023_);
return v___x_1054_;
}
}
}
}
else
{
lean_object* v___x_1055_; 
v___x_1055_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2___redArg(v_multigoals_1020_, v_t_1021_, v___y_1023_);
return v___x_1055_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___redArg(lean_object* v_multigoals_1056_, lean_object* v_trees_1057_, lean_object* v_a_1058_){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = lean_unsigned_to_nat(0u);
v___x_1061_ = l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0___redArg(v_multigoals_1056_, v_trees_1057_, v___x_1060_, v_a_1058_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___redArg___boxed(lean_object* v_multigoals_1062_, lean_object* v_trees_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___redArg(v_multigoals_1062_, v_trees_1063_, v_a_1064_);
lean_dec(v_a_1064_);
lean_dec_ref(v_trees_1063_);
lean_dec(v_multigoals_1062_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg___boxed(lean_object* v_multigoals_1067_, lean_object* v_as_1068_, lean_object* v_i_1069_, lean_object* v_stop_1070_, lean_object* v_b_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
size_t v_i_boxed_1074_; size_t v_stop_boxed_1075_; lean_object* v_res_1076_; 
v_i_boxed_1074_ = lean_unbox_usize(v_i_1069_);
lean_dec(v_i_1069_);
v_stop_boxed_1075_ = lean_unbox_usize(v_stop_1070_);
lean_dec(v_stop_1070_);
v_res_1076_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_1067_, v_as_1068_, v_i_boxed_1074_, v_stop_boxed_1075_, v_b_1071_, v___y_1072_);
lean_dec(v___y_1072_);
lean_dec_ref(v_as_1068_);
lean_dec(v_multigoals_1067_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_multigoals_1077_, lean_object* v_as_1078_, lean_object* v_i_1079_, lean_object* v_stop_1080_, lean_object* v_b_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
size_t v_i_boxed_1084_; size_t v_stop_boxed_1085_; lean_object* v_res_1086_; 
v_i_boxed_1084_ = lean_unbox_usize(v_i_1079_);
lean_dec(v_i_1079_);
v_stop_boxed_1085_ = lean_unbox_usize(v_stop_1080_);
lean_dec(v_stop_1080_);
v_res_1086_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___redArg(v_multigoals_1077_, v_as_1078_, v_i_boxed_1084_, v_stop_boxed_1085_, v_b_1081_, v___y_1082_);
lean_dec(v___y_1082_);
lean_dec_ref(v_as_1078_);
lean_dec(v_multigoals_1077_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2___redArg___boxed(lean_object* v_multigoals_1087_, lean_object* v_t_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2___redArg(v_multigoals_1087_, v_t_1088_, v___y_1089_);
lean_dec(v___y_1089_);
lean_dec_ref(v_t_1088_);
lean_dec(v_multigoals_1087_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_multigoals_1092_, lean_object* v_x_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2___redArg(v_multigoals_1092_, v_x_1093_, v___y_1094_);
lean_dec(v___y_1094_);
lean_dec_ref(v_x_1093_);
lean_dec(v_multigoals_1092_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0___redArg___boxed(lean_object* v_multigoals_1097_, lean_object* v_t_1098_, lean_object* v_start_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0___redArg(v_multigoals_1097_, v_t_1098_, v_start_1099_, v___y_1100_);
lean_dec(v___y_1100_);
lean_dec(v_start_1099_);
lean_dec_ref(v_t_1098_);
lean_dec(v_multigoals_1097_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg___boxed(lean_object* v_multigoals_1103_, lean_object* v_x_1104_, lean_object* v_x_1105_, lean_object* v_x_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
size_t v_x_14496__boxed_1109_; size_t v_x_14497__boxed_1110_; lean_object* v_res_1111_; 
v_x_14496__boxed_1109_ = lean_unbox_usize(v_x_1105_);
lean_dec(v_x_1105_);
v_x_14497__boxed_1110_ = lean_unbox_usize(v_x_1106_);
lean_dec(v_x_1106_);
v_res_1111_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg(v_multigoals_1103_, v_x_1104_, v_x_14496__boxed_1109_, v_x_14497__boxed_1110_, v___y_1107_);
lean_dec(v___y_1107_);
lean_dec_ref(v_x_1104_);
lean_dec(v_multigoals_1103_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___boxed(lean_object* v_multigoals_1112_, lean_object* v_x_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg(v_multigoals_1112_, v_x_1113_, v_a_1114_);
lean_dec(v_a_1114_);
lean_dec(v_multigoals_1112_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList(lean_object* v_multigoals_1117_, lean_object* v_00_u03c9_1118_, lean_object* v_trees_1119_, lean_object* v_a_1120_){
_start:
{
lean_object* v___x_1122_; 
v___x_1122_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___redArg(v_multigoals_1117_, v_trees_1119_, v_a_1120_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___boxed(lean_object* v_multigoals_1123_, lean_object* v_00_u03c9_1124_, lean_object* v_trees_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList(v_multigoals_1123_, v_00_u03c9_1124_, v_trees_1125_, v_a_1126_);
lean_dec(v_a_1126_);
lean_dec_ref(v_trees_1125_);
lean_dec(v_multigoals_1123_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics(lean_object* v_multigoals_1129_, lean_object* v_00_u03c9_1130_, lean_object* v_x_1131_, lean_object* v_a_1132_){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg(v_multigoals_1129_, v_x_1131_, v_a_1132_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___boxed(lean_object* v_multigoals_1135_, lean_object* v_00_u03c9_1136_, lean_object* v_x_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics(v_multigoals_1135_, v_00_u03c9_1136_, v_x_1137_, v_a_1138_);
lean_dec(v_a_1138_);
lean_dec(v_multigoals_1135_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0(lean_object* v_00_u03c9_1141_, lean_object* v_multigoals_1142_, lean_object* v_t_1143_, lean_object* v_start_1144_, lean_object* v___y_1145_){
_start:
{
lean_object* v___x_1147_; 
v___x_1147_ = l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0___redArg(v_multigoals_1142_, v_t_1143_, v_start_1144_, v___y_1145_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0___boxed(lean_object* v_00_u03c9_1148_, lean_object* v_multigoals_1149_, lean_object* v_t_1150_, lean_object* v_start_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
lean_object* v_res_1154_; 
v_res_1154_ = l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0(v_00_u03c9_1148_, v_multigoals_1149_, v_t_1150_, v_start_1151_, v___y_1152_);
lean_dec(v___y_1152_);
lean_dec(v_start_1151_);
lean_dec_ref(v_t_1150_);
lean_dec(v_multigoals_1149_);
return v_res_1154_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2(lean_object* v_00_u03b2_1155_, lean_object* v_m_1156_, lean_object* v_a_1157_){
_start:
{
lean_object* v___x_1158_; 
v___x_1158_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2___redArg(v_m_1156_, v_a_1157_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2___boxed(lean_object* v_00_u03b2_1159_, lean_object* v_m_1160_, lean_object* v_a_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2(v_00_u03b2_1159_, v_m_1160_, v_a_1161_);
lean_dec_ref(v_a_1161_);
lean_dec_ref(v_m_1160_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3(lean_object* v_00_u03b2_1163_, lean_object* v_m_1164_, lean_object* v_a_1165_){
_start:
{
lean_object* v___x_1166_; 
v___x_1166_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3___redArg(v_m_1164_, v_a_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3___boxed(lean_object* v_00_u03b2_1167_, lean_object* v_m_1168_, lean_object* v_a_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3(v_00_u03b2_1167_, v_m_1168_, v_a_1169_);
lean_dec_ref(v_a_1169_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4(lean_object* v_00_u03b2_1171_, lean_object* v_m_1172_, lean_object* v_query_1173_){
_start:
{
lean_object* v___x_1174_; 
v___x_1174_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4___redArg(v_m_1172_, v_query_1173_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4___boxed(lean_object* v_00_u03b2_1175_, lean_object* v_m_1176_, lean_object* v_query_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4(v_00_u03b2_1175_, v_m_1176_, v_query_1177_);
lean_dec_ref(v_query_1177_);
lean_dec_ref(v_m_1176_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__5(lean_object* v_00_u03b2_1179_, lean_object* v_m_1180_){
_start:
{
lean_object* v___x_1181_; 
v___x_1181_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__5___redArg(v_m_1180_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__5___boxed(lean_object* v_00_u03b2_1182_, lean_object* v_m_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__5(v_00_u03b2_1182_, v_m_1183_);
lean_dec_ref(v_m_1183_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0(lean_object* v_00_u03c9_1185_, lean_object* v_multigoals_1186_, lean_object* v_x_1187_, size_t v_x_1188_, size_t v_x_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v___x_1192_; 
v___x_1192_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg(v_multigoals_1186_, v_x_1187_, v_x_1188_, v_x_1189_, v___y_1190_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___boxed(lean_object* v_00_u03c9_1193_, lean_object* v_multigoals_1194_, lean_object* v_x_1195_, lean_object* v_x_1196_, lean_object* v_x_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
size_t v_x_15241__boxed_1200_; size_t v_x_15242__boxed_1201_; lean_object* v_res_1202_; 
v_x_15241__boxed_1200_ = lean_unbox_usize(v_x_1196_);
lean_dec(v_x_1196_);
v_x_15242__boxed_1201_ = lean_unbox_usize(v_x_1197_);
lean_dec(v_x_1197_);
v_res_1202_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0(v_00_u03c9_1193_, v_multigoals_1194_, v_x_1195_, v_x_15241__boxed_1200_, v_x_15242__boxed_1201_, v___y_1198_);
lean_dec(v___y_1198_);
lean_dec_ref(v_x_1195_);
lean_dec(v_multigoals_1194_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1(lean_object* v_00_u03c9_1203_, lean_object* v_multigoals_1204_, lean_object* v_as_1205_, size_t v_i_1206_, size_t v_stop_1207_, lean_object* v_b_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v___x_1211_; 
v___x_1211_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_1204_, v_as_1205_, v_i_1206_, v_stop_1207_, v_b_1208_, v___y_1209_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___boxed(lean_object* v_00_u03c9_1212_, lean_object* v_multigoals_1213_, lean_object* v_as_1214_, lean_object* v_i_1215_, lean_object* v_stop_1216_, lean_object* v_b_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
size_t v_i_boxed_1220_; size_t v_stop_boxed_1221_; lean_object* v_res_1222_; 
v_i_boxed_1220_ = lean_unbox_usize(v_i_1215_);
lean_dec(v_i_1215_);
v_stop_boxed_1221_ = lean_unbox_usize(v_stop_1216_);
lean_dec(v_stop_1216_);
v_res_1222_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1(v_00_u03c9_1212_, v_multigoals_1213_, v_as_1214_, v_i_boxed_1220_, v_stop_boxed_1221_, v_b_1217_, v___y_1218_);
lean_dec(v___y_1218_);
lean_dec_ref(v_as_1214_);
lean_dec(v_multigoals_1213_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2(lean_object* v_00_u03c9_1223_, lean_object* v_multigoals_1224_, lean_object* v_t_1225_, lean_object* v___y_1226_){
_start:
{
lean_object* v___x_1228_; 
v___x_1228_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2___redArg(v_multigoals_1224_, v_t_1225_, v___y_1226_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2___boxed(lean_object* v_00_u03c9_1229_, lean_object* v_multigoals_1230_, lean_object* v_t_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2(v_00_u03c9_1229_, v_multigoals_1230_, v_t_1231_, v___y_1232_);
lean_dec(v___y_1232_);
lean_dec_ref(v_t_1231_);
lean_dec(v_multigoals_1230_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5(lean_object* v_00_u03b2_1235_, lean_object* v_m_1236_, lean_object* v_query_1237_){
_start:
{
lean_object* v___x_1238_; 
v___x_1238_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5___redArg(v_m_1236_, v_query_1237_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1239_, lean_object* v_m_1240_, lean_object* v_query_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5(v_00_u03b2_1239_, v_m_1240_, v_query_1241_);
lean_dec_ref(v_query_1241_);
lean_dec_ref(v_m_1240_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__8(lean_object* v_00_u03b2_1243_, lean_object* v_m_1244_, lean_object* v_query_1245_, lean_object* v_x_1246_, lean_object* v_x_1247_, lean_object* v_x_1248_, lean_object* v_x_1249_){
_start:
{
lean_object* v___x_1250_; 
v___x_1250_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__8___redArg(v_m_1244_, v_query_1245_, v_x_1246_, v_x_1247_, v_x_1248_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__8___boxed(lean_object* v_00_u03b2_1251_, lean_object* v_m_1252_, lean_object* v_query_1253_, lean_object* v_x_1254_, lean_object* v_x_1255_, lean_object* v_x_1256_, lean_object* v_x_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__8(v_00_u03b2_1251_, v_m_1252_, v_query_1253_, v_x_1254_, v_x_1255_, v_x_1256_, v_x_1257_);
lean_dec_ref(v_query_1253_);
lean_dec_ref(v_m_1252_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__5_spec__10(lean_object* v_00_u03b2_1259_, lean_object* v_init_1260_, lean_object* v_b_1261_){
_start:
{
lean_object* v___x_1262_; 
v___x_1262_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__5_spec__10___redArg(v_init_1260_, v_b_1261_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__5_spec__10___boxed(lean_object* v_00_u03b2_1263_, lean_object* v_init_1264_, lean_object* v_b_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__5_spec__10(v_00_u03b2_1263_, v_init_1264_, v_b_1265_);
lean_dec_ref(v_b_1265_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2(lean_object* v_00_u03c9_1267_, lean_object* v_multigoals_1268_, lean_object* v_x_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v___x_1272_; 
v___x_1272_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2___redArg(v_multigoals_1268_, v_x_1269_, v___y_1270_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03c9_1273_, lean_object* v_multigoals_1274_, lean_object* v_x_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2(v_00_u03c9_1273_, v_multigoals_1274_, v_x_1275_, v___y_1276_);
lean_dec(v___y_1276_);
lean_dec_ref(v_x_1275_);
lean_dec(v_multigoals_1274_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3(lean_object* v_00_u03c9_1279_, lean_object* v_multigoals_1280_, lean_object* v_as_1281_, size_t v_i_1282_, size_t v_stop_1283_, lean_object* v_b_1284_, lean_object* v___y_1285_){
_start:
{
lean_object* v___x_1287_; 
v___x_1287_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___redArg(v_multigoals_1280_, v_as_1281_, v_i_1282_, v_stop_1283_, v_b_1284_, v___y_1285_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03c9_1288_, lean_object* v_multigoals_1289_, lean_object* v_as_1290_, lean_object* v_i_1291_, lean_object* v_stop_1292_, lean_object* v_b_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
size_t v_i_boxed_1296_; size_t v_stop_boxed_1297_; lean_object* v_res_1298_; 
v_i_boxed_1296_ = lean_unbox_usize(v_i_1291_);
lean_dec(v_i_1291_);
v_stop_boxed_1297_ = lean_unbox_usize(v_stop_1292_);
lean_dec(v_stop_1292_);
v_res_1298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3(v_00_u03c9_1288_, v_multigoals_1289_, v_as_1290_, v_i_boxed_1296_, v_stop_boxed_1297_, v_b_1293_, v___y_1294_);
lean_dec(v___y_1294_);
lean_dec_ref(v_as_1290_);
lean_dec(v_multigoals_1289_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__5_spec__10_spec__13(lean_object* v_00_u03b2_1299_, lean_object* v_b_1300_, lean_object* v_acc_1301_, lean_object* v_i_1302_){
_start:
{
lean_object* v___x_1303_; 
v___x_1303_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__5_spec__10_spec__13___redArg(v_b_1300_, v_acc_1301_, v_i_1302_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__5_spec__10_spec__13___boxed(lean_object* v_00_u03b2_1304_, lean_object* v_b_1305_, lean_object* v_acc_1306_, lean_object* v_i_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__5_spec__10_spec__13(v_00_u03b2_1304_, v_b_1305_, v_acc_1306_, v_i_1307_);
lean_dec_ref(v_b_1305_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__0(lean_object* v_a_1309_){
_start:
{
lean_object* v___x_1310_; 
v___x_1310_ = lean_nat_to_int(v_a_1309_);
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3___redArg(lean_object* v___y_1311_){
_start:
{
lean_object* v___x_1313_; lean_object* v_infoState_1314_; lean_object* v_trees_1315_; lean_object* v___x_1316_; 
v___x_1313_ = lean_st_ref_get(v___y_1311_);
v_infoState_1314_ = lean_ctor_get(v___x_1313_, 8);
lean_inc_ref(v_infoState_1314_);
lean_dec(v___x_1313_);
v_trees_1315_ = lean_ctor_get(v_infoState_1314_, 2);
lean_inc_ref(v_trees_1315_);
lean_dec_ref(v_infoState_1314_);
v___x_1316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1316_, 0, v_trees_1315_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3___redArg___boxed(lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3___redArg(v___y_1317_);
lean_dec(v___y_1317_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3(lean_object* v___y_1320_, lean_object* v___y_1321_){
_start:
{
lean_object* v___x_1323_; 
v___x_1323_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3___redArg(v___y_1321_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3___boxed(lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3(v___y_1324_, v___y_1325_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
return v_res_1327_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__0(void){
_start:
{
lean_object* v_cellCount_1328_; lean_object* v___x_1329_; 
v_cellCount_1328_ = lean_unsigned_to_nat(16u);
v___x_1329_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1328_);
return v___x_1329_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__1(void){
_start:
{
lean_object* v_cellCount_1330_; lean_object* v___x_1331_; 
v_cellCount_1330_ = lean_unsigned_to_nat(16u);
v___x_1331_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1330_);
return v___x_1331_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1332_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__1, &l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__1_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__1);
v___x_1333_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__0, &l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__0_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__0);
v___x_1334_ = lean_unsigned_to_nat(0u);
v___x_1335_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1334_);
lean_ctor_set(v___x_1335_, 1, v___x_1333_);
lean_ctor_set(v___x_1335_, 2, v___x_1332_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0(lean_object* v_stx_1336_, lean_object* v_val_1337_, lean_object* v_a_1338_, lean_object* v_x_1339_){
_start:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1341_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__2, &l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__2_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__2);
v___x_1342_ = lean_st_mk_ref(v___x_1341_);
v___x_1343_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg(v_stx_1336_, v___x_1342_);
v___x_1344_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___redArg(v_val_1337_, v_a_1338_, v___x_1342_);
v___x_1345_ = lean_st_ref_get(v___x_1342_);
lean_dec(v___x_1342_);
v___x_1346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1344_);
lean_ctor_set(v___x_1346_, 1, v___x_1345_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___boxed(lean_object* v_stx_1347_, lean_object* v_val_1348_, lean_object* v_a_1349_, lean_object* v_x_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0(v_stx_1347_, v_val_1348_, v_a_1349_, v_x_1350_);
lean_dec_ref(v_a_1349_);
lean_dec(v_val_1348_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1___redArg(lean_object* v_o_1353_, lean_object* v___y_1354_){
_start:
{
lean_object* v___x_1356_; lean_object* v_env_1357_; lean_object* v___x_1358_; lean_object* v_toEnvExtension_1359_; lean_object* v_asyncMode_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v_merged_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1372_; 
v___x_1356_ = lean_st_ref_get(v___y_1354_);
v_env_1357_ = lean_ctor_get(v___x_1356_, 0);
lean_inc_ref(v_env_1357_);
lean_dec(v___x_1356_);
v___x_1358_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_1359_ = lean_ctor_get(v___x_1358_, 0);
v_asyncMode_1360_ = lean_ctor_get(v_toEnvExtension_1359_, 2);
v___x_1361_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_1362_ = lean_box(0);
v___x_1363_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1361_, v___x_1358_, v_env_1357_, v_asyncMode_1360_, v___x_1362_);
v_merged_1364_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1372_ == 0)
{
lean_object* v_unused_1373_; 
v_unused_1373_ = lean_ctor_get(v___x_1363_, 1);
lean_dec(v_unused_1373_);
v___x_1366_ = v___x_1363_;
v_isShared_1367_ = v_isSharedCheck_1372_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_merged_1364_);
lean_dec(v___x_1363_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1372_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1369_; 
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 1, v_merged_1364_);
lean_ctor_set(v___x_1366_, 0, v_o_1353_);
v___x_1369_ = v___x_1366_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_o_1353_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v_merged_1364_);
v___x_1369_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
lean_object* v___x_1370_; 
v___x_1370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1369_);
return v___x_1370_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1___redArg___boxed(lean_object* v_o_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1___redArg(v_o_1374_, v___y_1375_);
lean_dec(v___y_1375_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1(lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
lean_object* v___x_1381_; lean_object* v_scopes_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v_opts_1385_; lean_object* v___x_1386_; 
v___x_1381_ = lean_st_ref_get(v___y_1379_);
v_scopes_1382_ = lean_ctor_get(v___x_1381_, 2);
lean_inc(v_scopes_1382_);
lean_dec(v___x_1381_);
v___x_1383_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1384_ = l_List_head_x21___redArg(v___x_1383_, v_scopes_1382_);
lean_dec(v_scopes_1382_);
v_opts_1385_ = lean_ctor_get(v___x_1384_, 1);
lean_inc_ref(v_opts_1385_);
lean_dec(v___x_1384_);
v___x_1386_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1___redArg(v_opts_1385_, v___y_1379_);
return v___x_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1___boxed(lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1(v___y_1387_, v___y_1388_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
return v_res_1390_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9___lam__0(uint8_t v___y_1392_, uint8_t v_suppressElabErrors_1393_, lean_object* v_x_1394_){
_start:
{
if (lean_obj_tag(v_x_1394_) == 1)
{
lean_object* v_pre_1395_; 
v_pre_1395_ = lean_ctor_get(v_x_1394_, 0);
if (lean_obj_tag(v_pre_1395_) == 0)
{
lean_object* v_str_1396_; lean_object* v___x_1397_; uint8_t v___x_1398_; 
v_str_1396_ = lean_ctor_get(v_x_1394_, 1);
v___x_1397_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9___lam__0___closed__0));
v___x_1398_ = lean_string_dec_eq(v_str_1396_, v___x_1397_);
if (v___x_1398_ == 0)
{
return v___y_1392_;
}
else
{
return v_suppressElabErrors_1393_;
}
}
else
{
return v___y_1392_;
}
}
else
{
return v___y_1392_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9___lam__0___boxed(lean_object* v___y_1399_, lean_object* v_suppressElabErrors_1400_, lean_object* v_x_1401_){
_start:
{
uint8_t v___y_8320__boxed_1402_; uint8_t v_suppressElabErrors_boxed_1403_; uint8_t v_res_1404_; lean_object* v_r_1405_; 
v___y_8320__boxed_1402_ = lean_unbox(v___y_1399_);
v_suppressElabErrors_boxed_1403_ = lean_unbox(v_suppressElabErrors_1400_);
v_res_1404_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9___lam__0(v___y_8320__boxed_1402_, v_suppressElabErrors_boxed_1403_, v_x_1401_);
lean_dec(v_x_1401_);
v_r_1405_ = lean_box(v_res_1404_);
return v_r_1405_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__13(lean_object* v_opts_1406_, lean_object* v_opt_1407_){
_start:
{
lean_object* v_name_1408_; lean_object* v_defValue_1409_; lean_object* v_map_1410_; lean_object* v___x_1411_; 
v_name_1408_ = lean_ctor_get(v_opt_1407_, 0);
v_defValue_1409_ = lean_ctor_get(v_opt_1407_, 1);
v_map_1410_ = lean_ctor_get(v_opts_1406_, 0);
v___x_1411_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1410_, v_name_1408_);
if (lean_obj_tag(v___x_1411_) == 0)
{
uint8_t v___x_1412_; 
v___x_1412_ = lean_unbox(v_defValue_1409_);
return v___x_1412_;
}
else
{
lean_object* v_val_1413_; 
v_val_1413_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_val_1413_);
lean_dec_ref_known(v___x_1411_, 1);
if (lean_obj_tag(v_val_1413_) == 1)
{
uint8_t v_v_1414_; 
v_v_1414_ = lean_ctor_get_uint8(v_val_1413_, 0);
lean_dec_ref_known(v_val_1413_, 0);
return v_v_1414_;
}
else
{
uint8_t v___x_1415_; 
lean_dec(v_val_1413_);
v___x_1415_ = lean_unbox(v_defValue_1409_);
return v___x_1415_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__13___boxed(lean_object* v_opts_1416_, lean_object* v_opt_1417_){
_start:
{
uint8_t v_res_1418_; lean_object* v_r_1419_; 
v_res_1418_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__13(v_opts_1416_, v_opt_1417_);
lean_dec_ref(v_opt_1417_);
lean_dec_ref(v_opts_1416_);
v_r_1419_ = lean_box(v_res_1418_);
return v_r_1419_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_1420_; 
v___x_1420_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1420_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1421_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___redArg___closed__0);
v___x_1422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1421_);
return v___x_1422_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1423_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___redArg___closed__1);
v___x_1424_ = lean_unsigned_to_nat(0u);
v___x_1425_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1424_);
lean_ctor_set(v___x_1425_, 1, v___x_1424_);
lean_ctor_set(v___x_1425_, 2, v___x_1424_);
lean_ctor_set(v___x_1425_, 3, v___x_1424_);
lean_ctor_set(v___x_1425_, 4, v___x_1423_);
lean_ctor_set(v___x_1425_, 5, v___x_1423_);
lean_ctor_set(v___x_1425_, 6, v___x_1423_);
lean_ctor_set(v___x_1425_, 7, v___x_1423_);
lean_ctor_set(v___x_1425_, 8, v___x_1423_);
lean_ctor_set(v___x_1425_, 9, v___x_1423_);
lean_ctor_set(v___x_1425_, 10, v___x_1423_);
return v___x_1425_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___redArg___closed__3(void){
_start:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1426_ = lean_unsigned_to_nat(32u);
v___x_1427_ = lean_mk_empty_array_with_capacity(v___x_1426_);
v___x_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1427_);
return v___x_1428_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___redArg___closed__4(void){
_start:
{
size_t v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1429_ = ((size_t)5ULL);
v___x_1430_ = lean_unsigned_to_nat(0u);
v___x_1431_ = lean_unsigned_to_nat(32u);
v___x_1432_ = lean_mk_empty_array_with_capacity(v___x_1431_);
v___x_1433_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___redArg___closed__3);
v___x_1434_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1434_, 0, v___x_1433_);
lean_ctor_set(v___x_1434_, 1, v___x_1432_);
lean_ctor_set(v___x_1434_, 2, v___x_1430_);
lean_ctor_set(v___x_1434_, 3, v___x_1430_);
lean_ctor_set_usize(v___x_1434_, 4, v___x_1429_);
return v___x_1434_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___redArg___closed__5(void){
_start:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1435_ = lean_box(1);
v___x_1436_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___redArg___closed__4);
v___x_1437_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___redArg___closed__1);
v___x_1438_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1437_);
lean_ctor_set(v___x_1438_, 1, v___x_1436_);
lean_ctor_set(v___x_1438_, 2, v___x_1435_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___redArg(lean_object* v_msgData_1439_, lean_object* v___y_1440_){
_start:
{
lean_object* v___x_1442_; lean_object* v_env_1443_; lean_object* v___x_1444_; lean_object* v_scopes_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v_opts_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1442_ = lean_st_ref_get(v___y_1440_);
v_env_1443_ = lean_ctor_get(v___x_1442_, 0);
lean_inc_ref(v_env_1443_);
lean_dec(v___x_1442_);
v___x_1444_ = lean_st_ref_get(v___y_1440_);
v_scopes_1445_ = lean_ctor_get(v___x_1444_, 2);
lean_inc(v_scopes_1445_);
lean_dec(v___x_1444_);
v___x_1446_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1447_ = l_List_head_x21___redArg(v___x_1446_, v_scopes_1445_);
lean_dec(v_scopes_1445_);
v_opts_1448_ = lean_ctor_get(v___x_1447_, 1);
lean_inc_ref(v_opts_1448_);
lean_dec(v___x_1447_);
v___x_1449_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___redArg___closed__2);
v___x_1450_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___redArg___closed__5);
v___x_1451_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1451_, 0, v_env_1443_);
lean_ctor_set(v___x_1451_, 1, v___x_1449_);
lean_ctor_set(v___x_1451_, 2, v___x_1450_);
lean_ctor_set(v___x_1451_, 3, v_opts_1448_);
v___x_1452_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1451_);
lean_ctor_set(v___x_1452_, 1, v_msgData_1439_);
v___x_1453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1452_);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___redArg___boxed(lean_object* v_msgData_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___redArg(v_msgData_1454_, v___y_1455_);
lean_dec(v___y_1455_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9(lean_object* v_ref_1459_, lean_object* v_msgData_1460_, uint8_t v_severity_1461_, uint8_t v_isSilent_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; uint8_t v___y_1471_; uint8_t v___y_1472_; lean_object* v___y_1473_; lean_object* v___y_1474_; uint8_t v___y_1531_; lean_object* v___y_1532_; uint8_t v___y_1533_; uint8_t v___y_1534_; lean_object* v___y_1535_; uint8_t v___y_1559_; lean_object* v___y_1560_; uint8_t v___y_1561_; uint8_t v___y_1562_; lean_object* v___y_1563_; uint8_t v___y_1567_; uint8_t v___y_1568_; uint8_t v___y_1569_; uint8_t v___x_1584_; uint8_t v___y_1586_; uint8_t v___y_1587_; uint8_t v___y_1588_; uint8_t v___y_1590_; uint8_t v___x_1602_; 
v___x_1584_ = 2;
v___x_1602_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1461_, v___x_1584_);
if (v___x_1602_ == 0)
{
v___y_1590_ = v___x_1602_;
goto v___jp_1589_;
}
else
{
uint8_t v___x_1603_; 
lean_inc_ref(v_msgData_1460_);
v___x_1603_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1460_);
v___y_1590_ = v___x_1603_;
goto v___jp_1589_;
}
v___jp_1466_:
{
lean_object* v___x_1475_; 
v___x_1475_ = l_Lean_Elab_Command_getScope___redArg(v___y_1474_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; lean_object* v___x_1477_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_a_1476_);
lean_dec_ref_known(v___x_1475_, 1);
v___x_1477_ = l_Lean_Elab_Command_getScope___redArg(v___y_1474_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1513_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1480_ = v___x_1477_;
v_isShared_1481_ = v_isSharedCheck_1513_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1477_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1513_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1482_; lean_object* v_currNamespace_1483_; lean_object* v_openDecls_1484_; lean_object* v_env_1485_; lean_object* v_messages_1486_; lean_object* v_scopes_1487_; lean_object* v_usedQuotCtxts_1488_; lean_object* v_nextMacroScope_1489_; lean_object* v_maxRecDepth_1490_; lean_object* v_ngen_1491_; lean_object* v_auxDeclNGen_1492_; lean_object* v_infoState_1493_; lean_object* v_traceState_1494_; lean_object* v_snapshotTasks_1495_; lean_object* v_prevLinterStates_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1512_; 
v___x_1482_ = lean_st_ref_take(v___y_1474_);
v_currNamespace_1483_ = lean_ctor_get(v_a_1476_, 2);
lean_inc(v_currNamespace_1483_);
lean_dec(v_a_1476_);
v_openDecls_1484_ = lean_ctor_get(v_a_1478_, 3);
lean_inc(v_openDecls_1484_);
lean_dec(v_a_1478_);
v_env_1485_ = lean_ctor_get(v___x_1482_, 0);
v_messages_1486_ = lean_ctor_get(v___x_1482_, 1);
v_scopes_1487_ = lean_ctor_get(v___x_1482_, 2);
v_usedQuotCtxts_1488_ = lean_ctor_get(v___x_1482_, 3);
v_nextMacroScope_1489_ = lean_ctor_get(v___x_1482_, 4);
v_maxRecDepth_1490_ = lean_ctor_get(v___x_1482_, 5);
v_ngen_1491_ = lean_ctor_get(v___x_1482_, 6);
v_auxDeclNGen_1492_ = lean_ctor_get(v___x_1482_, 7);
v_infoState_1493_ = lean_ctor_get(v___x_1482_, 8);
v_traceState_1494_ = lean_ctor_get(v___x_1482_, 9);
v_snapshotTasks_1495_ = lean_ctor_get(v___x_1482_, 10);
v_prevLinterStates_1496_ = lean_ctor_get(v___x_1482_, 11);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1498_ = v___x_1482_;
v_isShared_1499_ = v_isSharedCheck_1512_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_prevLinterStates_1496_);
lean_inc(v_snapshotTasks_1495_);
lean_inc(v_traceState_1494_);
lean_inc(v_infoState_1493_);
lean_inc(v_auxDeclNGen_1492_);
lean_inc(v_ngen_1491_);
lean_inc(v_maxRecDepth_1490_);
lean_inc(v_nextMacroScope_1489_);
lean_inc(v_usedQuotCtxts_1488_);
lean_inc(v_scopes_1487_);
lean_inc(v_messages_1486_);
lean_inc(v_env_1485_);
lean_dec(v___x_1482_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1512_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1505_; 
v___x_1500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1500_, 0, v_currNamespace_1483_);
lean_ctor_set(v___x_1500_, 1, v_openDecls_1484_);
v___x_1501_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1500_);
lean_ctor_set(v___x_1501_, 1, v___y_1468_);
lean_inc_ref(v___y_1473_);
lean_inc_ref(v___y_1467_);
v___x_1502_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1502_, 0, v___y_1467_);
lean_ctor_set(v___x_1502_, 1, v___y_1469_);
lean_ctor_set(v___x_1502_, 2, v___y_1470_);
lean_ctor_set(v___x_1502_, 3, v___y_1473_);
lean_ctor_set(v___x_1502_, 4, v___x_1501_);
lean_ctor_set_uint8(v___x_1502_, sizeof(void*)*5, v___y_1471_);
lean_ctor_set_uint8(v___x_1502_, sizeof(void*)*5 + 1, v___y_1472_);
lean_ctor_set_uint8(v___x_1502_, sizeof(void*)*5 + 2, v_isSilent_1462_);
v___x_1503_ = l_Lean_MessageLog_add(v___x_1502_, v_messages_1486_);
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 1, v___x_1503_);
v___x_1505_ = v___x_1498_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_env_1485_);
lean_ctor_set(v_reuseFailAlloc_1511_, 1, v___x_1503_);
lean_ctor_set(v_reuseFailAlloc_1511_, 2, v_scopes_1487_);
lean_ctor_set(v_reuseFailAlloc_1511_, 3, v_usedQuotCtxts_1488_);
lean_ctor_set(v_reuseFailAlloc_1511_, 4, v_nextMacroScope_1489_);
lean_ctor_set(v_reuseFailAlloc_1511_, 5, v_maxRecDepth_1490_);
lean_ctor_set(v_reuseFailAlloc_1511_, 6, v_ngen_1491_);
lean_ctor_set(v_reuseFailAlloc_1511_, 7, v_auxDeclNGen_1492_);
lean_ctor_set(v_reuseFailAlloc_1511_, 8, v_infoState_1493_);
lean_ctor_set(v_reuseFailAlloc_1511_, 9, v_traceState_1494_);
lean_ctor_set(v_reuseFailAlloc_1511_, 10, v_snapshotTasks_1495_);
lean_ctor_set(v_reuseFailAlloc_1511_, 11, v_prevLinterStates_1496_);
v___x_1505_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1509_; 
v___x_1506_ = lean_st_ref_put(v___y_1474_, v___x_1505_);
v___x_1507_ = lean_box(0);
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 0, v___x_1507_);
v___x_1509_ = v___x_1480_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1507_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
}
else
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1521_; 
lean_dec(v_a_1476_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
lean_dec_ref(v___y_1468_);
v_a_1514_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1516_ = v___x_1477_;
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1477_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1519_; 
if (v_isShared_1517_ == 0)
{
v___x_1519_ = v___x_1516_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_a_1514_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
}
else
{
lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1529_; 
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
lean_dec_ref(v___y_1468_);
v_a_1522_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1524_ = v___x_1475_;
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_dec(v___x_1475_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1527_; 
if (v_isShared_1525_ == 0)
{
v___x_1527_ = v___x_1524_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_a_1522_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
}
}
v___jp_1530_:
{
lean_object* v_fileName_1536_; lean_object* v_fileMap_1537_; uint8_t v_suppressElabErrors_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1557_; 
v_fileName_1536_ = lean_ctor_get(v___y_1463_, 0);
v_fileMap_1537_ = lean_ctor_get(v___y_1463_, 1);
v_suppressElabErrors_1538_ = lean_ctor_get_uint8(v___y_1463_, sizeof(void*)*10);
v___x_1539_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1460_);
v___x_1540_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___redArg(v___x_1539_, v___y_1464_);
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1543_ = v___x_1540_;
v_isShared_1544_ = v_isSharedCheck_1557_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1540_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1557_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
lean_inc_ref_n(v_fileMap_1537_, 2);
v___x_1545_ = l_Lean_FileMap_toPosition(v_fileMap_1537_, v___y_1532_);
lean_dec(v___y_1532_);
v___x_1546_ = l_Lean_FileMap_toPosition(v_fileMap_1537_, v___y_1535_);
lean_dec(v___y_1535_);
v___x_1547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1546_);
v___x_1548_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9___closed__0));
if (v_suppressElabErrors_1538_ == 0)
{
lean_del_object(v___x_1543_);
v___y_1467_ = v_fileName_1536_;
v___y_1468_ = v_a_1541_;
v___y_1469_ = v___x_1545_;
v___y_1470_ = v___x_1547_;
v___y_1471_ = v___y_1533_;
v___y_1472_ = v___y_1534_;
v___y_1473_ = v___x_1548_;
v___y_1474_ = v___y_1464_;
goto v___jp_1466_;
}
else
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___f_1551_; uint8_t v___x_1552_; 
v___x_1549_ = lean_box(v___y_1531_);
v___x_1550_ = lean_box(v_suppressElabErrors_1538_);
v___f_1551_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1551_, 0, v___x_1549_);
lean_closure_set(v___f_1551_, 1, v___x_1550_);
lean_inc(v_a_1541_);
v___x_1552_ = l_Lean_MessageData_hasTag(v___f_1551_, v_a_1541_);
if (v___x_1552_ == 0)
{
lean_object* v___x_1553_; lean_object* v___x_1555_; 
lean_dec_ref_known(v___x_1547_, 1);
lean_dec_ref(v___x_1545_);
lean_dec(v_a_1541_);
v___x_1553_ = lean_box(0);
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 0, v___x_1553_);
v___x_1555_ = v___x_1543_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v___x_1553_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
else
{
lean_del_object(v___x_1543_);
v___y_1467_ = v_fileName_1536_;
v___y_1468_ = v_a_1541_;
v___y_1469_ = v___x_1545_;
v___y_1470_ = v___x_1547_;
v___y_1471_ = v___y_1533_;
v___y_1472_ = v___y_1534_;
v___y_1473_ = v___x_1548_;
v___y_1474_ = v___y_1464_;
goto v___jp_1466_;
}
}
}
}
v___jp_1558_:
{
lean_object* v___x_1564_; 
v___x_1564_ = l_Lean_Syntax_getTailPos_x3f(v___y_1560_, v___y_1561_);
lean_dec(v___y_1560_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_inc(v___y_1563_);
v___y_1531_ = v___y_1559_;
v___y_1532_ = v___y_1563_;
v___y_1533_ = v___y_1561_;
v___y_1534_ = v___y_1562_;
v___y_1535_ = v___y_1563_;
goto v___jp_1530_;
}
else
{
lean_object* v_val_1565_; 
v_val_1565_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_val_1565_);
lean_dec_ref_known(v___x_1564_, 1);
v___y_1531_ = v___y_1559_;
v___y_1532_ = v___y_1563_;
v___y_1533_ = v___y_1561_;
v___y_1534_ = v___y_1562_;
v___y_1535_ = v_val_1565_;
goto v___jp_1530_;
}
}
v___jp_1566_:
{
lean_object* v___x_1570_; 
v___x_1570_ = l_Lean_Elab_Command_getRef___redArg(v___y_1463_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_a_1571_; lean_object* v_ref_1572_; lean_object* v___x_1573_; 
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
lean_inc(v_a_1571_);
lean_dec_ref_known(v___x_1570_, 1);
v_ref_1572_ = l_Lean_replaceRef(v_ref_1459_, v_a_1571_);
lean_dec(v_a_1571_);
v___x_1573_ = l_Lean_Syntax_getPos_x3f(v_ref_1572_, v___y_1568_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v___x_1574_; 
v___x_1574_ = lean_unsigned_to_nat(0u);
v___y_1559_ = v___y_1567_;
v___y_1560_ = v_ref_1572_;
v___y_1561_ = v___y_1568_;
v___y_1562_ = v___y_1569_;
v___y_1563_ = v___x_1574_;
goto v___jp_1558_;
}
else
{
lean_object* v_val_1575_; 
v_val_1575_ = lean_ctor_get(v___x_1573_, 0);
lean_inc(v_val_1575_);
lean_dec_ref_known(v___x_1573_, 1);
v___y_1559_ = v___y_1567_;
v___y_1560_ = v_ref_1572_;
v___y_1561_ = v___y_1568_;
v___y_1562_ = v___y_1569_;
v___y_1563_ = v_val_1575_;
goto v___jp_1558_;
}
}
else
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1583_; 
lean_dec_ref(v_msgData_1460_);
v_a_1576_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1578_ = v___x_1570_;
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___x_1570_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1579_ == 0)
{
v___x_1581_ = v___x_1578_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_a_1576_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
}
v___jp_1585_:
{
if (v___y_1588_ == 0)
{
v___y_1567_ = v___y_1586_;
v___y_1568_ = v___y_1587_;
v___y_1569_ = v_severity_1461_;
goto v___jp_1566_;
}
else
{
v___y_1567_ = v___y_1586_;
v___y_1568_ = v___y_1587_;
v___y_1569_ = v___x_1584_;
goto v___jp_1566_;
}
}
v___jp_1589_:
{
if (v___y_1590_ == 0)
{
lean_object* v___x_1591_; lean_object* v_scopes_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v_opts_1595_; uint8_t v___x_1596_; uint8_t v___x_1597_; 
v___x_1591_ = lean_st_ref_get(v___y_1464_);
v_scopes_1592_ = lean_ctor_get(v___x_1591_, 2);
lean_inc(v_scopes_1592_);
lean_dec(v___x_1591_);
v___x_1593_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1594_ = l_List_head_x21___redArg(v___x_1593_, v_scopes_1592_);
lean_dec(v_scopes_1592_);
v_opts_1595_ = lean_ctor_get(v___x_1594_, 1);
lean_inc_ref(v_opts_1595_);
lean_dec(v___x_1594_);
v___x_1596_ = 1;
v___x_1597_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1461_, v___x_1596_);
if (v___x_1597_ == 0)
{
lean_dec_ref(v_opts_1595_);
v___y_1586_ = v___y_1590_;
v___y_1587_ = v___y_1590_;
v___y_1588_ = v___x_1597_;
goto v___jp_1585_;
}
else
{
lean_object* v___x_1598_; uint8_t v___x_1599_; 
v___x_1598_ = l_Lean_warningAsError;
v___x_1599_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__13(v_opts_1595_, v___x_1598_);
lean_dec_ref(v_opts_1595_);
v___y_1586_ = v___y_1590_;
v___y_1587_ = v___y_1590_;
v___y_1588_ = v___x_1599_;
goto v___jp_1585_;
}
}
else
{
lean_object* v___x_1600_; lean_object* v___x_1601_; 
lean_dec_ref(v_msgData_1460_);
v___x_1600_ = lean_box(0);
v___x_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1600_);
return v___x_1601_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9___boxed(lean_object* v_ref_1604_, lean_object* v_msgData_1605_, lean_object* v_severity_1606_, lean_object* v_isSilent_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
uint8_t v_severity_boxed_1611_; uint8_t v_isSilent_boxed_1612_; lean_object* v_res_1613_; 
v_severity_boxed_1611_ = lean_unbox(v_severity_1606_);
v_isSilent_boxed_1612_ = lean_unbox(v_isSilent_1607_);
v_res_1613_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9(v_ref_1604_, v_msgData_1605_, v_severity_boxed_1611_, v_isSilent_boxed_1612_, v___y_1608_, v___y_1609_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
lean_dec(v_ref_1604_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5(lean_object* v_ref_1614_, lean_object* v_msgData_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
uint8_t v___x_1619_; uint8_t v___x_1620_; lean_object* v___x_1621_; 
v___x_1619_ = 1;
v___x_1620_ = 0;
v___x_1621_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9(v_ref_1614_, v_msgData_1615_, v___x_1619_, v___x_1620_, v___y_1616_, v___y_1617_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5___boxed(lean_object* v_ref_1622_, lean_object* v_msgData_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
lean_object* v_res_1627_; 
v_res_1627_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5(v_ref_1622_, v_msgData_1623_, v___y_1624_, v___y_1625_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
lean_dec(v_ref_1622_);
return v_res_1627_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1629_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__0));
v___x_1630_ = l_Lean_stringToMessageData(v___x_1629_);
return v___x_1630_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1632_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__2));
v___x_1633_ = l_Lean_stringToMessageData(v___x_1632_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3(lean_object* v_linterOption_1634_, lean_object* v_stx_1635_, lean_object* v_msg_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_){
_start:
{
lean_object* v_name_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1658_; 
v_name_1640_ = lean_ctor_get(v_linterOption_1634_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v_linterOption_1634_);
if (v_isSharedCheck_1658_ == 0)
{
lean_object* v_unused_1659_; 
v_unused_1659_ = lean_ctor_get(v_linterOption_1634_, 1);
lean_dec(v_unused_1659_);
v___x_1642_ = v_linterOption_1634_;
v_isShared_1643_ = v_isSharedCheck_1658_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_name_1640_);
lean_dec(v_linterOption_1634_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1658_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1647_; 
v___x_1644_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__1);
lean_inc(v_name_1640_);
v___x_1645_ = l_Lean_MessageData_ofName(v_name_1640_);
if (v_isShared_1643_ == 0)
{
lean_ctor_set_tag(v___x_1642_, 7);
lean_ctor_set(v___x_1642_, 1, v___x_1645_);
lean_ctor_set(v___x_1642_, 0, v___x_1644_);
v___x_1647_ = v___x_1642_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1644_);
lean_ctor_set(v_reuseFailAlloc_1657_, 1, v___x_1645_);
v___x_1647_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v_disable_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1648_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__3);
v___x_1649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1647_);
lean_ctor_set(v___x_1649_, 1, v___x_1648_);
v_disable_1650_ = l_Lean_MessageData_note(v___x_1649_);
v___x_1651_ = l_Lean_Linter_linterMessageTag;
v___x_1652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1652_, 0, v_msg_1636_);
lean_ctor_set(v___x_1652_, 1, v_disable_1650_);
v___x_1653_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1651_);
lean_ctor_set(v___x_1653_, 1, v___x_1652_);
v___x_1654_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1654_, 0, v_name_1640_);
lean_ctor_set(v___x_1654_, 1, v___x_1653_);
lean_inc(v_stx_1635_);
v___x_1655_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_1655_, 0, v_stx_1635_);
lean_ctor_set(v___x_1655_, 1, v___x_1654_);
v___x_1656_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5(v_stx_1635_, v___x_1655_, v___y_1637_, v___y_1638_);
lean_dec(v_stx_1635_);
return v___x_1656_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___boxed(lean_object* v_linterOption_1660_, lean_object* v_stx_1661_, lean_object* v_msg_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3(v_linterOption_1660_, v_stx_1661_, v_msg_1662_, v___y_1663_, v___y_1664_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2(lean_object* v_linterOption_1667_, lean_object* v_stx_1668_, lean_object* v_msg_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_){
_start:
{
lean_object* v___x_1673_; lean_object* v_a_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1684_; 
v___x_1673_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1(v___y_1670_, v___y_1671_);
v_a_1674_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1676_ = v___x_1673_;
v_isShared_1677_ = v_isSharedCheck_1684_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_a_1674_);
lean_dec(v___x_1673_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1684_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
uint8_t v___x_1678_; 
v___x_1678_ = l_Lean_Linter_getLinterValue(v_linterOption_1667_, v_a_1674_);
lean_dec(v_a_1674_);
if (v___x_1678_ == 0)
{
lean_object* v___x_1679_; lean_object* v___x_1681_; 
lean_dec_ref(v_msg_1669_);
lean_dec(v_stx_1668_);
lean_dec_ref(v_linterOption_1667_);
v___x_1679_ = lean_box(0);
if (v_isShared_1677_ == 0)
{
lean_ctor_set(v___x_1676_, 0, v___x_1679_);
v___x_1681_ = v___x_1676_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1679_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
else
{
lean_object* v___x_1683_; 
lean_del_object(v___x_1676_);
v___x_1683_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3(v_linterOption_1667_, v_stx_1668_, v_msg_1669_, v___y_1670_, v___y_1671_);
return v___x_1683_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2___boxed(lean_object* v_linterOption_1685_, lean_object* v_stx_1686_, lean_object* v_msg_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2(v_linterOption_1685_, v_stx_1686_, v_msg_1687_, v___y_1688_, v___y_1689_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
return v_res_1691_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___closed__2(void){
_start:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1695_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___closed__1));
v___x_1696_ = l_Lean_MessageData_ofFormat(v___x_1695_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5(lean_object* v_as_1697_, size_t v_sz_1698_, size_t v_i_1699_, lean_object* v_b_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_){
_start:
{
lean_object* v_a_1705_; uint8_t v___x_1709_; 
v___x_1709_ = lean_usize_dec_lt(v_i_1699_, v_sz_1698_);
if (v___x_1709_ == 0)
{
lean_object* v___x_1710_; 
v___x_1710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1710_, 0, v_b_1700_);
return v___x_1710_;
}
else
{
lean_object* v_a_1711_; lean_object* v_fst_1712_; lean_object* v_snd_1713_; lean_object* v_start_1714_; lean_object* v_stop_1715_; lean_object* v_start_1716_; lean_object* v_stop_1717_; lean_object* v___x_1718_; uint8_t v___y_1720_; uint8_t v___x_1731_; 
v_a_1711_ = lean_array_uget_borrowed(v_as_1697_, v_i_1699_);
v_fst_1712_ = lean_ctor_get(v_a_1711_, 0);
v_snd_1713_ = lean_ctor_get(v_a_1711_, 1);
v_start_1714_ = lean_ctor_get(v_b_1700_, 0);
v_stop_1715_ = lean_ctor_get(v_b_1700_, 1);
v_start_1716_ = lean_ctor_get(v_fst_1712_, 0);
v_stop_1717_ = lean_ctor_get(v_fst_1712_, 1);
v___x_1718_ = l_Lean_Linter_Extra_linter_extra_unnecessarySeqFocus;
v___x_1731_ = lean_nat_dec_le(v_start_1714_, v_start_1716_);
if (v___x_1731_ == 0)
{
v___y_1720_ = v___x_1731_;
goto v___jp_1719_;
}
else
{
uint8_t v___x_1732_; 
v___x_1732_ = lean_nat_dec_le(v_stop_1717_, v_stop_1715_);
v___y_1720_ = v___x_1732_;
goto v___jp_1719_;
}
v___jp_1719_:
{
if (v___y_1720_ == 0)
{
lean_object* v___x_1721_; lean_object* v___x_1722_; 
lean_dec_ref(v_b_1700_);
v___x_1721_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___closed__2);
lean_inc(v_snd_1713_);
v___x_1722_ = l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2(v___x_1718_, v_snd_1713_, v___x_1721_, v___y_1701_, v___y_1702_);
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_dec_ref_known(v___x_1722_, 1);
lean_inc(v_fst_1712_);
v_a_1705_ = v_fst_1712_;
goto v___jp_1704_;
}
else
{
lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1730_; 
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1725_ = v___x_1722_;
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_dec(v___x_1722_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1728_; 
if (v_isShared_1726_ == 0)
{
v___x_1728_ = v___x_1725_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_a_1723_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
}
}
else
{
v_a_1705_ = v_b_1700_;
goto v___jp_1704_;
}
}
}
v___jp_1704_:
{
size_t v___x_1706_; size_t v___x_1707_; 
v___x_1706_ = ((size_t)1ULL);
v___x_1707_ = lean_usize_add(v_i_1699_, v___x_1706_);
v_i_1699_ = v___x_1707_;
v_b_1700_ = v_a_1705_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___boxed(lean_object* v_as_1733_, lean_object* v_sz_1734_, lean_object* v_i_1735_, lean_object* v_b_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
size_t v_sz_boxed_1740_; size_t v_i_boxed_1741_; lean_object* v_res_1742_; 
v_sz_boxed_1740_ = lean_unbox_usize(v_sz_1734_);
lean_dec(v_sz_1734_);
v_i_boxed_1741_ = lean_unbox_usize(v_i_1735_);
lean_dec(v_i_1735_);
v_res_1742_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5(v_as_1733_, v_sz_boxed_1740_, v_i_boxed_1741_, v_b_1736_, v___y_1737_, v___y_1738_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec_ref(v_as_1733_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4_spec__6(uint8_t v___x_1743_, lean_object* v_b_1744_, lean_object* v_acc_1745_, lean_object* v_i_1746_){
_start:
{
lean_object* v___y_1748_; lean_object* v_keyArray_1756_; lean_object* v_valueArray_1757_; lean_object* v___x_1758_; uint8_t v___x_1759_; 
v_keyArray_1756_ = lean_ctor_get(v_b_1744_, 1);
v_valueArray_1757_ = lean_ctor_get(v_b_1744_, 2);
v___x_1758_ = lean_array_get_size(v_keyArray_1756_);
v___x_1759_ = lean_nat_dec_lt(v_i_1746_, v___x_1758_);
if (v___x_1759_ == 0)
{
lean_dec(v_i_1746_);
return v_acc_1745_;
}
else
{
lean_object* v___x_1760_; uint8_t v_isSome_1761_; 
v___x_1760_ = lean_array_fget_borrowed(v_keyArray_1756_, v_i_1746_);
v_isSome_1761_ = lean_noption_is_some(v___x_1760_);
if (v_isSome_1761_ == 0)
{
goto v___jp_1752_;
}
else
{
lean_object* v___x_1762_; uint8_t v_isSome_1763_; 
v___x_1762_ = lean_array_fget_borrowed(v_valueArray_1757_, v_i_1746_);
v_isSome_1763_ = lean_noption_is_some(v___x_1762_);
if (v_isSome_1763_ == 0)
{
goto v___jp_1752_;
}
else
{
lean_object* v_val_1764_; uint8_t v_used_1765_; 
lean_inc(v___x_1762_);
v_val_1764_ = lean_noption_get(v___x_1762_);
v_used_1765_ = lean_ctor_get_uint8(v_val_1764_, sizeof(void*)*1);
if (v_used_1765_ == 0)
{
lean_dec(v_val_1764_);
v___y_1748_ = v_acc_1745_;
goto v___jp_1747_;
}
else
{
lean_object* v_stx_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___y_1770_; lean_object* v___x_1773_; 
v_stx_1766_ = lean_ctor_get(v_val_1764_, 0);
lean_inc(v_stx_1766_);
lean_dec(v_val_1764_);
v___x_1767_ = lean_unsigned_to_nat(1u);
v___x_1768_ = l_Lean_Syntax_getArg(v_stx_1766_, v___x_1767_);
lean_dec(v_stx_1766_);
v___x_1773_ = l_Lean_Syntax_getRange_x3f(v___x_1768_, v___x_1743_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_val_1774_; 
lean_inc(v___x_1760_);
v_val_1774_ = lean_noption_get(v___x_1760_);
v___y_1770_ = v_val_1774_;
goto v___jp_1769_;
}
else
{
lean_object* v_val_1775_; 
v_val_1775_ = lean_ctor_get(v___x_1773_, 0);
lean_inc(v_val_1775_);
lean_dec_ref_known(v___x_1773_, 1);
v___y_1770_ = v_val_1775_;
goto v___jp_1769_;
}
v___jp_1769_:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1771_, 0, v___y_1770_);
lean_ctor_set(v___x_1771_, 1, v___x_1768_);
v___x_1772_ = lean_array_push(v_acc_1745_, v___x_1771_);
v___y_1748_ = v___x_1772_;
goto v___jp_1747_;
}
}
}
}
}
v___jp_1747_:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1749_ = lean_unsigned_to_nat(1u);
v___x_1750_ = lean_nat_add(v_i_1746_, v___x_1749_);
lean_dec(v_i_1746_);
v_acc_1745_ = v___y_1748_;
v_i_1746_ = v___x_1750_;
goto _start;
}
v___jp_1752_:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1753_ = lean_unsigned_to_nat(1u);
v___x_1754_ = lean_nat_add(v_i_1746_, v___x_1753_);
lean_dec(v_i_1746_);
v_i_1746_ = v___x_1754_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4_spec__6___boxed(lean_object* v___x_1776_, lean_object* v_b_1777_, lean_object* v_acc_1778_, lean_object* v_i_1779_){
_start:
{
uint8_t v___x_8884__boxed_1780_; lean_object* v_res_1781_; 
v___x_8884__boxed_1780_ = lean_unbox(v___x_1776_);
v_res_1781_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4_spec__6(v___x_8884__boxed_1780_, v_b_1777_, v_acc_1778_, v_i_1779_);
lean_dec_ref(v_b_1777_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4(uint8_t v___x_1782_, lean_object* v_init_1783_, lean_object* v_b_1784_){
_start:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1785_ = lean_unsigned_to_nat(0u);
v___x_1786_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4_spec__6(v___x_1782_, v_b_1784_, v_init_1783_, v___x_1785_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___boxed(lean_object* v___x_1787_, lean_object* v_init_1788_, lean_object* v_b_1789_){
_start:
{
uint8_t v___x_8937__boxed_1790_; lean_object* v_res_1791_; 
v___x_8937__boxed_1790_ = lean_unbox(v___x_1787_);
v_res_1791_ = l_Std_DHashMap_Raw_foldM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4(v___x_8937__boxed_1790_, v_init_1788_, v_b_1789_);
lean_dec_ref(v_b_1789_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6___redArg___lam__0(lean_object* v_r_1792_){
_start:
{
lean_object* v_start_1793_; lean_object* v_stop_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1803_; 
v_start_1793_ = lean_ctor_get(v_r_1792_, 0);
v_stop_1794_ = lean_ctor_get(v_r_1792_, 1);
v_isSharedCheck_1803_ = !lean_is_exclusive(v_r_1792_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1796_ = v_r_1792_;
v_isShared_1797_ = v_isSharedCheck_1803_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_stop_1794_);
lean_inc(v_start_1793_);
lean_dec(v_r_1792_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1803_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1801_; 
v___x_1798_ = lean_nat_to_int(v_stop_1794_);
v___x_1799_ = lean_int_neg(v___x_1798_);
lean_dec(v___x_1798_);
if (v_isShared_1797_ == 0)
{
lean_ctor_set(v___x_1796_, 1, v___x_1799_);
v___x_1801_ = v___x_1796_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_start_1793_);
lean_ctor_set(v_reuseFailAlloc_1802_, 1, v___x_1799_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6___redArg___lam__1(lean_object* v___f_1806_, uint8_t v___x_1807_, lean_object* v_x1_1808_, lean_object* v_x2_1809_){
_start:
{
lean_object* v_fst_1810_; lean_object* v_fst_1811_; lean_object* v___f_1812_; lean_object* v___f_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_8189__overap_1816_; lean_object* v___x_1817_; uint8_t v___x_1818_; 
v_fst_1810_ = lean_ctor_get(v_x1_1808_, 0);
lean_inc(v_fst_1810_);
lean_dec_ref(v_x1_1808_);
v_fst_1811_ = lean_ctor_get(v_x2_1809_, 0);
lean_inc(v_fst_1811_);
lean_dec_ref(v_x2_1809_);
v___f_1812_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6___redArg___lam__1___closed__0));
v___f_1813_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6___redArg___lam__1___closed__1));
lean_inc_ref(v___f_1806_);
v___x_1814_ = lean_apply_1(v___f_1806_, v_fst_1810_);
v___x_1815_ = lean_apply_1(v___f_1806_, v_fst_1811_);
v___x_8189__overap_1816_ = l_lexOrd___redArg(v___f_1812_, v___f_1813_);
v___x_1817_ = lean_apply_2(v___x_8189__overap_1816_, v___x_1814_, v___x_1815_);
v___x_1818_ = lean_unbox(v___x_1817_);
if (v___x_1818_ == 0)
{
return v___x_1807_;
}
else
{
uint8_t v___x_1819_; 
v___x_1819_ = 0;
return v___x_1819_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6___redArg___lam__1___boxed(lean_object* v___f_1820_, lean_object* v___x_1821_, lean_object* v_x1_1822_, lean_object* v_x2_1823_){
_start:
{
uint8_t v___x_8967__boxed_1824_; uint8_t v_res_1825_; lean_object* v_r_1826_; 
v___x_8967__boxed_1824_ = lean_unbox(v___x_1821_);
v_res_1825_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6___redArg___lam__1(v___f_1820_, v___x_8967__boxed_1824_, v_x1_1822_, v_x2_1823_);
v_r_1826_ = lean_box(v_res_1825_);
return v_r_1826_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6_spec__9___redArg(lean_object* v_hi_1827_, lean_object* v_pivot_1828_, lean_object* v_as_1829_, lean_object* v_i_1830_, lean_object* v_k_1831_){
_start:
{
uint8_t v___x_1836_; 
v___x_1836_ = lean_nat_dec_lt(v_k_1831_, v_hi_1827_);
if (v___x_1836_ == 0)
{
lean_object* v___x_1837_; lean_object* v___x_1838_; 
lean_dec(v_k_1831_);
lean_dec_ref(v_pivot_1828_);
v___x_1837_ = lean_array_fswap(v_as_1829_, v_i_1830_, v_hi_1827_);
v___x_1838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1838_, 0, v_i_1830_);
lean_ctor_set(v___x_1838_, 1, v___x_1837_);
return v___x_1838_;
}
else
{
lean_object* v___x_1839_; lean_object* v_fst_1840_; lean_object* v_fst_1841_; lean_object* v___f_1842_; lean_object* v___f_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_8004__overap_1846_; lean_object* v___x_1847_; uint8_t v___x_1848_; 
v___x_1839_ = lean_array_fget_borrowed(v_as_1829_, v_k_1831_);
v_fst_1840_ = lean_ctor_get(v___x_1839_, 0);
v_fst_1841_ = lean_ctor_get(v_pivot_1828_, 0);
v___f_1842_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6___redArg___lam__1___closed__0));
v___f_1843_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6___redArg___lam__1___closed__1));
lean_inc(v_fst_1840_);
v___x_1844_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6___redArg___lam__0(v_fst_1840_);
lean_inc(v_fst_1841_);
v___x_1845_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6___redArg___lam__0(v_fst_1841_);
v___x_8004__overap_1846_ = l_lexOrd___redArg(v___f_1842_, v___f_1843_);
v___x_1847_ = lean_apply_2(v___x_8004__overap_1846_, v___x_1844_, v___x_1845_);
v___x_1848_ = lean_unbox(v___x_1847_);
if (v___x_1848_ == 0)
{
if (v___x_1836_ == 0)
{
goto v___jp_1832_;
}
else
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1849_ = lean_array_fswap(v_as_1829_, v_i_1830_, v_k_1831_);
v___x_1850_ = lean_unsigned_to_nat(1u);
v___x_1851_ = lean_nat_add(v_i_1830_, v___x_1850_);
lean_dec(v_i_1830_);
v___x_1852_ = lean_nat_add(v_k_1831_, v___x_1850_);
lean_dec(v_k_1831_);
v_as_1829_ = v___x_1849_;
v_i_1830_ = v___x_1851_;
v_k_1831_ = v___x_1852_;
goto _start;
}
}
else
{
goto v___jp_1832_;
}
}
v___jp_1832_:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1833_ = lean_unsigned_to_nat(1u);
v___x_1834_ = lean_nat_add(v_k_1831_, v___x_1833_);
lean_dec(v_k_1831_);
v_k_1831_ = v___x_1834_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6_spec__9___redArg___boxed(lean_object* v_hi_1854_, lean_object* v_pivot_1855_, lean_object* v_as_1856_, lean_object* v_i_1857_, lean_object* v_k_1858_){
_start:
{
lean_object* v_res_1859_; 
v_res_1859_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6_spec__9___redArg(v_hi_1854_, v_pivot_1855_, v_as_1856_, v_i_1857_, v_k_1858_);
lean_dec(v_hi_1854_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6___redArg(lean_object* v_n_1861_, lean_object* v_as_1862_, lean_object* v_lo_1863_, lean_object* v_hi_1864_){
_start:
{
lean_object* v___y_1866_; uint8_t v___x_1876_; 
v___x_1876_ = lean_nat_dec_lt(v_lo_1863_, v_hi_1864_);
if (v___x_1876_ == 0)
{
lean_dec(v_lo_1863_);
return v_as_1862_;
}
else
{
lean_object* v___f_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v_mid_1880_; lean_object* v___y_1882_; lean_object* v___y_1888_; lean_object* v___x_1893_; lean_object* v___x_1894_; uint8_t v___x_1895_; 
v___f_1877_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6___redArg___closed__0));
v___x_1878_ = lean_nat_add(v_lo_1863_, v_hi_1864_);
v___x_1879_ = lean_unsigned_to_nat(1u);
v_mid_1880_ = lean_nat_shiftr(v___x_1878_, v___x_1879_);
lean_dec(v___x_1878_);
v___x_1893_ = lean_array_fget_borrowed(v_as_1862_, v_mid_1880_);
v___x_1894_ = lean_array_fget_borrowed(v_as_1862_, v_lo_1863_);
lean_inc(v___x_1894_);
lean_inc(v___x_1893_);
v___x_1895_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6___redArg___lam__1(v___f_1877_, v___x_1876_, v___x_1893_, v___x_1894_);
if (v___x_1895_ == 0)
{
v___y_1888_ = v_as_1862_;
goto v___jp_1887_;
}
else
{
lean_object* v___x_1896_; 
v___x_1896_ = lean_array_fswap(v_as_1862_, v_lo_1863_, v_mid_1880_);
v___y_1888_ = v___x_1896_;
goto v___jp_1887_;
}
v___jp_1881_:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; uint8_t v___x_1885_; 
v___x_1883_ = lean_array_fget_borrowed(v___y_1882_, v_mid_1880_);
v___x_1884_ = lean_array_fget_borrowed(v___y_1882_, v_hi_1864_);
lean_inc(v___x_1884_);
lean_inc(v___x_1883_);
v___x_1885_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6___redArg___lam__1(v___f_1877_, v___x_1876_, v___x_1883_, v___x_1884_);
if (v___x_1885_ == 0)
{
lean_dec(v_mid_1880_);
v___y_1866_ = v___y_1882_;
goto v___jp_1865_;
}
else
{
lean_object* v___x_1886_; 
v___x_1886_ = lean_array_fswap(v___y_1882_, v_mid_1880_, v_hi_1864_);
lean_dec(v_mid_1880_);
v___y_1866_ = v___x_1886_;
goto v___jp_1865_;
}
}
v___jp_1887_:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; uint8_t v___x_1891_; 
v___x_1889_ = lean_array_fget_borrowed(v___y_1888_, v_hi_1864_);
v___x_1890_ = lean_array_fget_borrowed(v___y_1888_, v_lo_1863_);
lean_inc(v___x_1890_);
lean_inc(v___x_1889_);
v___x_1891_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6___redArg___lam__1(v___f_1877_, v___x_1876_, v___x_1889_, v___x_1890_);
if (v___x_1891_ == 0)
{
v___y_1882_ = v___y_1888_;
goto v___jp_1881_;
}
else
{
lean_object* v___x_1892_; 
v___x_1892_ = lean_array_fswap(v___y_1888_, v_lo_1863_, v_hi_1864_);
v___y_1882_ = v___x_1892_;
goto v___jp_1881_;
}
}
}
v___jp_1865_:
{
lean_object* v_pivot_1867_; lean_object* v___x_1868_; lean_object* v_fst_1869_; lean_object* v_snd_1870_; uint8_t v___x_1871_; 
v_pivot_1867_ = lean_array_fget(v___y_1866_, v_hi_1864_);
lean_inc_n(v_lo_1863_, 2);
v___x_1868_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6_spec__9___redArg(v_hi_1864_, v_pivot_1867_, v___y_1866_, v_lo_1863_, v_lo_1863_);
v_fst_1869_ = lean_ctor_get(v___x_1868_, 0);
lean_inc(v_fst_1869_);
v_snd_1870_ = lean_ctor_get(v___x_1868_, 1);
lean_inc(v_snd_1870_);
lean_dec_ref(v___x_1868_);
v___x_1871_ = lean_nat_dec_le(v_hi_1864_, v_fst_1869_);
if (v___x_1871_ == 0)
{
lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1872_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6___redArg(v_n_1861_, v_snd_1870_, v_lo_1863_, v_fst_1869_);
v___x_1873_ = lean_unsigned_to_nat(1u);
v___x_1874_ = lean_nat_add(v_fst_1869_, v___x_1873_);
lean_dec(v_fst_1869_);
v_as_1862_ = v___x_1872_;
v_lo_1863_ = v___x_1874_;
goto _start;
}
else
{
lean_dec(v_fst_1869_);
lean_dec(v_lo_1863_);
return v_snd_1870_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6___redArg___boxed(lean_object* v_n_1897_, lean_object* v_as_1898_, lean_object* v_lo_1899_, lean_object* v_hi_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6___redArg(v_n_1897_, v_as_1898_, v_lo_1899_, v_hi_1900_);
lean_dec(v_hi_1900_);
lean_dec(v_n_1897_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1(lean_object* v_stx_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_){
_start:
{
lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1937_; lean_object* v___y_1938_; lean_object* v___y_1941_; lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___x_1947_; lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1986_; 
v___x_1947_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1(v___y_1907_, v___y_1908_);
v_a_1948_ = lean_ctor_get(v___x_1947_, 0);
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1950_ = v___x_1947_;
v_isShared_1951_ = v_isSharedCheck_1986_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1947_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1986_;
goto v_resetjp_1949_;
}
v___jp_1910_:
{
size_t v_sz_1913_; size_t v___x_1914_; lean_object* v___x_1915_; 
v_sz_1913_ = lean_array_size(v___y_1912_);
v___x_1914_ = ((size_t)0ULL);
lean_inc_ref(v___y_1911_);
v___x_1915_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5(v___y_1912_, v_sz_1913_, v___x_1914_, v___y_1911_, v___y_1907_, v___y_1908_);
lean_dec_ref(v___y_1912_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1923_; 
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1923_ == 0)
{
lean_object* v_unused_1924_; 
v_unused_1924_ = lean_ctor_get(v___x_1915_, 0);
lean_dec(v_unused_1924_);
v___x_1917_ = v___x_1915_;
v_isShared_1918_ = v_isSharedCheck_1923_;
goto v_resetjp_1916_;
}
else
{
lean_dec(v___x_1915_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1923_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1919_; lean_object* v___x_1921_; 
v___x_1919_ = lean_box(0);
if (v_isShared_1918_ == 0)
{
lean_ctor_set(v___x_1917_, 0, v___x_1919_);
v___x_1921_ = v___x_1917_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v___x_1919_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
else
{
lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1932_; 
v_a_1925_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1927_ = v___x_1915_;
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___x_1915_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___x_1930_; 
if (v_isShared_1928_ == 0)
{
v___x_1930_ = v___x_1927_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_a_1925_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
}
}
v___jp_1933_:
{
lean_object* v___x_1939_; 
v___x_1939_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6___redArg(v___y_1935_, v___y_1936_, v___y_1934_, v___y_1938_);
lean_dec(v___y_1938_);
lean_dec(v___y_1935_);
v___y_1911_ = v___y_1937_;
v___y_1912_ = v___x_1939_;
goto v___jp_1910_;
}
v___jp_1940_:
{
uint8_t v___x_1946_; 
v___x_1946_ = lean_nat_dec_le(v___y_1945_, v___y_1942_);
if (v___x_1946_ == 0)
{
lean_dec(v___y_1942_);
lean_inc(v___y_1945_);
v___y_1934_ = v___y_1945_;
v___y_1935_ = v___y_1941_;
v___y_1936_ = v___y_1943_;
v___y_1937_ = v___y_1944_;
v___y_1938_ = v___y_1945_;
goto v___jp_1933_;
}
else
{
v___y_1934_ = v___y_1945_;
v___y_1935_ = v___y_1941_;
v___y_1936_ = v___y_1943_;
v___y_1937_ = v___y_1944_;
v___y_1938_ = v___y_1942_;
goto v___jp_1933_;
}
}
v_resetjp_1949_:
{
lean_object* v___x_1952_; uint8_t v___y_1954_; lean_object* v___x_1982_; uint8_t v___x_1983_; 
v___x_1952_ = lean_st_ref_get(v___y_1908_);
v___x_1982_ = l_Lean_Linter_Extra_linter_extra_unnecessarySeqFocus;
v___x_1983_ = l_Lean_Linter_getLinterValue(v___x_1982_, v_a_1948_);
lean_dec(v_a_1948_);
if (v___x_1983_ == 0)
{
lean_dec(v___x_1952_);
v___y_1954_ = v___x_1983_;
goto v___jp_1953_;
}
else
{
lean_object* v_infoState_1984_; uint8_t v_enabled_1985_; 
v_infoState_1984_ = lean_ctor_get(v___x_1952_, 8);
lean_inc_ref(v_infoState_1984_);
lean_dec(v___x_1952_);
v_enabled_1985_ = lean_ctor_get_uint8(v_infoState_1984_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1984_);
v___y_1954_ = v_enabled_1985_;
goto v___jp_1953_;
}
v___jp_1953_:
{
if (v___y_1954_ == 0)
{
lean_object* v___x_1955_; lean_object* v___x_1957_; 
lean_dec(v_stx_1906_);
v___x_1955_ = lean_box(0);
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 0, v___x_1955_);
v___x_1957_ = v___x_1950_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___x_1955_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
else
{
lean_object* v___x_1959_; lean_object* v_messages_1960_; uint8_t v___x_1961_; 
v___x_1959_ = lean_st_ref_get(v___y_1908_);
v_messages_1960_ = lean_ctor_get(v___x_1959_, 1);
lean_inc_ref(v_messages_1960_);
lean_dec(v___x_1959_);
v___x_1961_ = l_Lean_MessageLog_hasErrors(v_messages_1960_);
lean_dec_ref(v_messages_1960_);
if (v___x_1961_ == 0)
{
lean_object* v___x_1962_; lean_object* v_a_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___f_1966_; lean_object* v___x_1967_; lean_object* v_snd_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; uint8_t v___x_1974_; 
lean_del_object(v___x_1950_);
v___x_1962_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3___redArg(v___y_1908_);
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
lean_inc(v_a_1963_);
lean_dec_ref(v___x_1962_);
v___x_1964_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_multigoalKindsRef;
v___x_1965_ = lean_st_ref_get(v___x_1964_);
v___f_1966_ = lean_alloc_closure((void*)(l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1966_, 0, v_stx_1906_);
lean_closure_set(v___f_1966_, 1, v___x_1965_);
lean_closure_set(v___f_1966_, 2, v_a_1963_);
v___x_1967_ = l_runST___redArg(v___f_1966_);
v_snd_1968_ = lean_ctor_get(v___x_1967_, 1);
lean_inc(v_snd_1968_);
lean_dec(v___x_1967_);
v___x_1969_ = lean_unsigned_to_nat(0u);
v___x_1970_ = ((lean_object*)(l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1___closed__0));
v___x_1971_ = l_Std_DHashMap_Raw_foldM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4(v___x_1961_, v___x_1970_, v_snd_1968_);
lean_dec(v_snd_1968_);
v___x_1972_ = ((lean_object*)(l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1___closed__1));
v___x_1973_ = lean_array_get_size(v___x_1971_);
v___x_1974_ = lean_nat_dec_eq(v___x_1973_, v___x_1969_);
if (v___x_1974_ == 0)
{
lean_object* v___x_1975_; lean_object* v___x_1976_; uint8_t v___x_1977_; 
v___x_1975_ = lean_unsigned_to_nat(1u);
v___x_1976_ = lean_nat_sub(v___x_1973_, v___x_1975_);
v___x_1977_ = lean_nat_dec_le(v___x_1969_, v___x_1976_);
if (v___x_1977_ == 0)
{
lean_inc(v___x_1976_);
v___y_1941_ = v___x_1973_;
v___y_1942_ = v___x_1976_;
v___y_1943_ = v___x_1971_;
v___y_1944_ = v___x_1972_;
v___y_1945_ = v___x_1976_;
goto v___jp_1940_;
}
else
{
v___y_1941_ = v___x_1973_;
v___y_1942_ = v___x_1976_;
v___y_1943_ = v___x_1971_;
v___y_1944_ = v___x_1972_;
v___y_1945_ = v___x_1969_;
goto v___jp_1940_;
}
}
else
{
v___y_1911_ = v___x_1972_;
v___y_1912_ = v___x_1971_;
goto v___jp_1910_;
}
}
else
{
lean_object* v___x_1978_; lean_object* v___x_1980_; 
lean_dec(v_stx_1906_);
v___x_1978_ = lean_box(0);
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 0, v___x_1978_);
v___x_1980_ = v___x_1950_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v___x_1978_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1___boxed(lean_object* v_stx_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_){
_start:
{
lean_object* v_res_1991_; 
v_res_1991_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1(v_stx_1987_, v___y_1988_, v___y_1989_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
return v_res_1991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1(lean_object* v_o_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_){
_start:
{
lean_object* v___x_2011_; 
v___x_2011_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1___redArg(v_o_2007_, v___y_2009_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1___boxed(lean_object* v_o_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_){
_start:
{
lean_object* v_res_2016_; 
v_res_2016_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1(v_o_2012_, v___y_2013_, v___y_2014_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6(lean_object* v_n_2017_, lean_object* v_as_2018_, lean_object* v_lo_2019_, lean_object* v_hi_2020_, lean_object* v_w_2021_, lean_object* v_hlo_2022_, lean_object* v_hhi_2023_){
_start:
{
lean_object* v___x_2024_; 
v___x_2024_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6___redArg(v_n_2017_, v_as_2018_, v_lo_2019_, v_hi_2020_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6___boxed(lean_object* v_n_2025_, lean_object* v_as_2026_, lean_object* v_lo_2027_, lean_object* v_hi_2028_, lean_object* v_w_2029_, lean_object* v_hlo_2030_, lean_object* v_hhi_2031_){
_start:
{
lean_object* v_res_2032_; 
v_res_2032_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6(v_n_2025_, v_as_2026_, v_lo_2027_, v_hi_2028_, v_w_2029_, v_hlo_2030_, v_hhi_2031_);
lean_dec(v_hi_2028_);
lean_dec(v_n_2025_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6_spec__9(lean_object* v_n_2033_, lean_object* v_lo_2034_, lean_object* v_hi_2035_, lean_object* v_hhi_2036_, lean_object* v_pivot_2037_, lean_object* v_as_2038_, lean_object* v_i_2039_, lean_object* v_k_2040_, lean_object* v_ilo_2041_, lean_object* v_ik_2042_, lean_object* v_w_2043_){
_start:
{
lean_object* v___x_2044_; 
v___x_2044_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6_spec__9___redArg(v_hi_2035_, v_pivot_2037_, v_as_2038_, v_i_2039_, v_k_2040_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6_spec__9___boxed(lean_object* v_n_2045_, lean_object* v_lo_2046_, lean_object* v_hi_2047_, lean_object* v_hhi_2048_, lean_object* v_pivot_2049_, lean_object* v_as_2050_, lean_object* v_i_2051_, lean_object* v_k_2052_, lean_object* v_ilo_2053_, lean_object* v_ik_2054_, lean_object* v_w_2055_){
_start:
{
lean_object* v_res_2056_; 
v_res_2056_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6_spec__9(v_n_2045_, v_lo_2046_, v_hi_2047_, v_hhi_2048_, v_pivot_2049_, v_as_2050_, v_i_2051_, v_k_2052_, v_ilo_2053_, v_ik_2054_, v_w_2055_);
lean_dec(v_hi_2047_);
lean_dec(v_lo_2046_);
lean_dec(v_n_2045_);
return v_res_2056_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12(lean_object* v_msgData_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_){
_start:
{
lean_object* v___x_2061_; 
v___x_2061_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___redArg(v_msgData_2057_, v___y_2059_);
return v___x_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12___boxed(lean_object* v_msgData_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__9_spec__12(v_msgData_2062_, v___y_2063_, v___y_2064_);
lean_dec(v___y_2064_);
lean_dec_ref(v___y_2063_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_3917858151____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2068_ = ((lean_object*)(l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter));
v___x_2069_ = l_Lean_Elab_Command_addLinter(v___x_2068_);
return v___x_2069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_3917858151____hygCtx___hyg_2____boxed(lean_object* v_a_2070_){
_start:
{
lean_object* v_res_2071_; 
v_res_2071_ = l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_3917858151____hygCtx___hyg_2_();
return v_res_2071_;
}
}
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_Extra_UnnecessarySeqFocus(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_Extra_linter_extra_unnecessarySeqFocus = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_Extra_linter_extra_unnecessarySeqFocus);
lean_dec_ref(res);
res = l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_3107221289____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_Extra_UnnecessarySeqFocus_multigoalKindsRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_Extra_UnnecessarySeqFocus_multigoalKindsRef);
lean_dec_ref(res);
res = l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_3917858151____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Linter_Extra_UnnecessarySeqFocus(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* initialize_Lean_Linter_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Linter_Extra_UnnecessarySeqFocus(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Extra_UnnecessarySeqFocus(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Linter_Extra_UnnecessarySeqFocus(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Linter_Extra_UnnecessarySeqFocus(builtin);
}
#ifdef __cplusplus
}
#endif
