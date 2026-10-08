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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default___redArg();
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
uint64_t l_Lean_Syntax_instHashableRange_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
uint8_t l_Lean_Syntax_instBEqRange_beq(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedInfoTree_default;
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
extern lean_object* l_Lean_Linter_linterSetsExt;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
extern lean_object* l_Lean_Linter_linterMessageTag;
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_instOrdNat___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instOrdInt___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_lexOrd___redArg(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_instMonadST___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Syntax_instBEqRange_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_instHashableRange_hash___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10_spec__13_spec__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg___closed__0;
static const lean_ctor_object l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(5) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__2 = (const lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__3 = (const lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__0 = (const lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__0_value),((lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__3_value)}};
static const lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__4 = (const lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1 = (const lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1_value),((lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__4_value)}};
static const lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__5 = (const lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__0_value),((lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__5_value)}};
static const lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__6 = (const lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__7 = (const lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__0_value),((lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__6_value)}};
static const lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__8 = (const lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__0_value),((lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__8_value)}};
static const lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__9 = (const lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__9_value;
static const lean_ctor_object l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__0_value),((lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__9_value)}};
static const lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__10 = (const lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__10_value;
static const lean_ctor_object l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__0_value),((lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__10_value)}};
static const lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__11 = (const lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__11_value;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10_spec__13_spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__0;
static lean_once_cell_t l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__13(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__13___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__0(lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instOrdNat___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg___closed__0_value;
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instOrdInt___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__7(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1___closed__0 = (const lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1___closed__0_value;
static const lean_array_object l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_271_ = l_instMonadST___redArg();
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
lean_object* v_kind_285_; lean_object* v_args_286_; lean_object* v___f_287_; lean_object* v___y_289_; lean_object* v___x_303_; lean_object* v___x_304_; uint8_t v___y_306_; lean_object* v___x_314_; uint8_t v___x_315_; 
v_kind_285_ = lean_ctor_get(v_stx_281_, 1);
v_args_286_ = lean_ctor_get(v_stx_281_, 2);
lean_inc_ref(v_args_286_);
v___f_287_ = lean_alloc_closure((void*)(l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___lam__0___boxed), 4, 0);
v___x_303_ = ((lean_object*)(l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___closed__2));
v___x_304_ = ((lean_object*)(l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___closed__3));
v___x_314_ = ((lean_object*)(l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__1));
v___x_315_ = lean_name_eq(v_kind_285_, v___x_314_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; uint8_t v___x_317_; 
v___x_316_ = ((lean_object*)(l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__3));
v___x_317_ = lean_name_eq(v_kind_285_, v___x_316_);
v___y_306_ = v___x_317_;
goto v___jp_305_;
}
else
{
v___y_306_ = v___x_315_;
goto v___jp_305_;
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
size_t v___x_295_; size_t v___x_296_; lean_object* v___x_593__overap_297_; lean_object* v___x_298_; 
v___x_295_ = ((size_t)0ULL);
v___x_296_ = lean_usize_of_nat(v___x_291_);
v___x_593__overap_297_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_284_, v___f_287_, v_args_286_, v___x_295_, v___x_296_, v___x_292_);
lean_inc(v___y_289_);
v___x_298_ = lean_apply_2(v___x_593__overap_297_, v___y_289_, lean_box(0));
return v___x_298_;
}
}
else
{
size_t v___x_299_; size_t v___x_300_; lean_object* v___x_597__overap_301_; lean_object* v___x_302_; 
v___x_299_ = ((size_t)0ULL);
v___x_300_ = lean_usize_of_nat(v___x_291_);
v___x_597__overap_301_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_284_, v___f_287_, v_args_286_, v___x_299_, v___x_300_, v___x_292_);
lean_inc(v___y_289_);
v___x_302_ = lean_apply_2(v___x_597__overap_301_, v___y_289_, lean_box(0));
return v___x_302_;
}
}
}
v___jp_305_:
{
if (v___y_306_ == 0)
{
lean_dec_ref_known(v_stx_281_, 3);
v___y_289_ = v_a_282_;
goto v___jp_288_;
}
else
{
lean_object* v___x_307_; 
v___x_307_ = l_Lean_Syntax_getRange_x3f(v_stx_281_, v___y_306_);
if (lean_obj_tag(v___x_307_) == 1)
{
lean_object* v_val_308_; lean_object* v___x_309_; uint8_t v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v_val_308_ = lean_ctor_get(v___x_307_, 0);
lean_inc(v_val_308_);
lean_dec_ref_known(v___x_307_, 1);
v___x_309_ = lean_st_ref_take(v_a_282_);
v___x_310_ = 0;
v___x_311_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_311_, 0, v_stx_281_);
lean_ctor_set_uint8(v___x_311_, sizeof(void*)*1, v___x_310_);
v___x_312_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_303_, v___x_304_, v___x_309_, v_val_308_, v___x_311_);
v___x_313_ = lean_st_ref_put(v_a_282_, v___x_312_);
v___y_289_ = v_a_282_;
goto v___jp_288_;
}
else
{
lean_dec(v___x_307_);
lean_dec_ref_known(v_stx_281_, 3);
v___y_289_ = v_a_282_;
goto v___jp_288_;
}
}
}
}
else
{
lean_object* v___x_318_; 
lean_dec(v_stx_281_);
v___x_318_ = lean_box(0);
return v___x_318_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___lam__0(lean_object* v_x_319_, lean_object* v___y_320_, lean_object* v___y_321_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg(v___y_320_, v___y_321_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___boxed(lean_object* v_stx_324_, lean_object* v_a_325_, lean_object* v_a_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg(v_stx_324_, v_a_325_);
lean_dec(v_a_325_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics(lean_object* v_00_u03c9_328_, lean_object* v_stx_329_, lean_object* v_a_330_){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg(v_stx_329_, v_a_330_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___boxed(lean_object* v_00_u03c9_333_, lean_object* v_stx_334_, lean_object* v_a_335_, lean_object* v_a_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics(v_00_u03c9_333_, v_stx_334_, v_a_335_);
lean_dec(v_a_335_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_getPath(lean_object* v_x_338_, lean_object* v_x_339_, lean_object* v_x_340_){
_start:
{
if (lean_obj_tag(v_x_340_) == 0)
{
lean_object* v___x_341_; 
lean_dec_ref(v_x_339_);
v___x_341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_341_, 0, v_x_338_);
return v___x_341_;
}
else
{
lean_object* v_head_342_; lean_object* v_tail_343_; lean_object* v_fst_344_; lean_object* v_snd_345_; lean_object* v_size_346_; uint8_t v___x_347_; 
lean_dec_ref(v_x_338_);
v_head_342_ = lean_ctor_get(v_x_340_, 0);
v_tail_343_ = lean_ctor_get(v_x_340_, 1);
v_fst_344_ = lean_ctor_get(v_head_342_, 0);
v_snd_345_ = lean_ctor_get(v_head_342_, 1);
v_size_346_ = lean_ctor_get(v_x_339_, 2);
v___x_347_ = lean_nat_dec_eq(v_size_346_, v_fst_344_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; 
lean_dec_ref(v_x_339_);
v___x_348_ = lean_box(0);
return v___x_348_;
}
else
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_350_ = l_Lean_PersistentArray_get_x21___redArg(v___x_349_, v_x_339_, v_snd_345_);
lean_dec_ref(v_x_339_);
if (lean_obj_tag(v___x_350_) == 1)
{
lean_object* v_i_351_; lean_object* v_children_352_; 
v_i_351_ = lean_ctor_get(v___x_350_, 0);
lean_inc_ref(v_i_351_);
v_children_352_ = lean_ctor_get(v___x_350_, 1);
lean_inc_ref(v_children_352_);
lean_dec_ref_known(v___x_350_, 2);
v_x_338_ = v_i_351_;
v_x_339_ = v_children_352_;
v_x_340_ = v_tail_343_;
goto _start;
}
else
{
lean_object* v___x_354_; 
lean_dec(v___x_350_);
v___x_354_ = lean_box(0);
return v___x_354_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_getPath___boxed(lean_object* v_x_355_, lean_object* v_x_356_, lean_object* v_x_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_getPath(v_x_355_, v_x_356_, v_x_357_);
lean_dec(v_x_357_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10_spec__13_spec__14___redArg(lean_object* v_x_359_, lean_object* v_x_360_){
_start:
{
if (lean_obj_tag(v_x_360_) == 0)
{
return v_x_359_;
}
else
{
lean_object* v_key_361_; lean_object* v_value_362_; lean_object* v_tail_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_386_; 
v_key_361_ = lean_ctor_get(v_x_360_, 0);
v_value_362_ = lean_ctor_get(v_x_360_, 1);
v_tail_363_ = lean_ctor_get(v_x_360_, 2);
v_isSharedCheck_386_ = !lean_is_exclusive(v_x_360_);
if (v_isSharedCheck_386_ == 0)
{
v___x_365_ = v_x_360_;
v_isShared_366_ = v_isSharedCheck_386_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_tail_363_);
lean_inc(v_value_362_);
lean_inc(v_key_361_);
lean_dec(v_x_360_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_386_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_367_; uint64_t v___x_368_; uint64_t v___x_369_; uint64_t v___x_370_; uint64_t v_fold_371_; uint64_t v___x_372_; uint64_t v___x_373_; uint64_t v___x_374_; size_t v___x_375_; size_t v___x_376_; size_t v___x_377_; size_t v___x_378_; size_t v___x_379_; lean_object* v___x_380_; lean_object* v___x_382_; 
v___x_367_ = lean_array_get_size(v_x_359_);
v___x_368_ = l_Lean_Syntax_instHashableRange_hash(v_key_361_);
v___x_369_ = 32ULL;
v___x_370_ = lean_uint64_shift_right(v___x_368_, v___x_369_);
v_fold_371_ = lean_uint64_xor(v___x_368_, v___x_370_);
v___x_372_ = 16ULL;
v___x_373_ = lean_uint64_shift_right(v_fold_371_, v___x_372_);
v___x_374_ = lean_uint64_xor(v_fold_371_, v___x_373_);
v___x_375_ = lean_uint64_to_usize(v___x_374_);
v___x_376_ = lean_usize_of_nat(v___x_367_);
v___x_377_ = ((size_t)1ULL);
v___x_378_ = lean_usize_sub(v___x_376_, v___x_377_);
v___x_379_ = lean_usize_land(v___x_375_, v___x_378_);
v___x_380_ = lean_array_uget_borrowed(v_x_359_, v___x_379_);
lean_inc(v___x_380_);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 2, v___x_380_);
v___x_382_ = v___x_365_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_key_361_);
lean_ctor_set(v_reuseFailAlloc_385_, 1, v_value_362_);
lean_ctor_set(v_reuseFailAlloc_385_, 2, v___x_380_);
v___x_382_ = v_reuseFailAlloc_385_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
lean_object* v___x_383_; 
v___x_383_ = lean_array_uset(v_x_359_, v___x_379_, v___x_382_);
v_x_359_ = v___x_383_;
v_x_360_ = v_tail_363_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10_spec__13___redArg(lean_object* v_i_387_, lean_object* v_source_388_, lean_object* v_target_389_){
_start:
{
lean_object* v___x_390_; uint8_t v___x_391_; 
v___x_390_ = lean_array_get_size(v_source_388_);
v___x_391_ = lean_nat_dec_lt(v_i_387_, v___x_390_);
if (v___x_391_ == 0)
{
lean_dec_ref(v_source_388_);
lean_dec(v_i_387_);
return v_target_389_;
}
else
{
lean_object* v_es_392_; lean_object* v___x_393_; lean_object* v_source_394_; lean_object* v_target_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v_es_392_ = lean_array_fget(v_source_388_, v_i_387_);
v___x_393_ = lean_box(0);
v_source_394_ = lean_array_fset(v_source_388_, v_i_387_, v___x_393_);
v_target_395_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10_spec__13_spec__14___redArg(v_target_389_, v_es_392_);
v___x_396_ = lean_unsigned_to_nat(1u);
v___x_397_ = lean_nat_add(v_i_387_, v___x_396_);
lean_dec(v_i_387_);
v_i_387_ = v___x_397_;
v_source_388_ = v_source_394_;
v_target_389_ = v_target_395_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10___redArg(lean_object* v_data_399_){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v_nbuckets_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_400_ = lean_array_get_size(v_data_399_);
v___x_401_ = lean_unsigned_to_nat(2u);
v_nbuckets_402_ = lean_nat_mul(v___x_400_, v___x_401_);
v___x_403_ = lean_unsigned_to_nat(0u);
v___x_404_ = lean_box(0);
v___x_405_ = lean_mk_array(v_nbuckets_402_, v___x_404_);
v___x_406_ = lean_array_propagate_mark(v_data_399_, v___x_405_);
v___x_407_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10_spec__13___redArg(v___x_403_, v_data_399_, v___x_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__11___redArg(lean_object* v_a_408_, lean_object* v_b_409_, lean_object* v_x_410_){
_start:
{
if (lean_obj_tag(v_x_410_) == 0)
{
lean_dec(v_b_409_);
lean_dec_ref(v_a_408_);
return v_x_410_;
}
else
{
lean_object* v_key_411_; lean_object* v_value_412_; lean_object* v_tail_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_425_; 
v_key_411_ = lean_ctor_get(v_x_410_, 0);
v_value_412_ = lean_ctor_get(v_x_410_, 1);
v_tail_413_ = lean_ctor_get(v_x_410_, 2);
v_isSharedCheck_425_ = !lean_is_exclusive(v_x_410_);
if (v_isSharedCheck_425_ == 0)
{
v___x_415_ = v_x_410_;
v_isShared_416_ = v_isSharedCheck_425_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_tail_413_);
lean_inc(v_value_412_);
lean_inc(v_key_411_);
lean_dec(v_x_410_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_425_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
uint8_t v___x_417_; 
v___x_417_ = l_Lean_Syntax_instBEqRange_beq(v_key_411_, v_a_408_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; lean_object* v___x_420_; 
v___x_418_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__11___redArg(v_a_408_, v_b_409_, v_tail_413_);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 2, v___x_418_);
v___x_420_ = v___x_415_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_key_411_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v_value_412_);
lean_ctor_set(v_reuseFailAlloc_421_, 2, v___x_418_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
else
{
lean_object* v___x_423_; 
lean_dec(v_value_412_);
lean_dec(v_key_411_);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 1, v_b_409_);
lean_ctor_set(v___x_415_, 0, v_a_408_);
v___x_423_ = v___x_415_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_a_408_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v_b_409_);
lean_ctor_set(v_reuseFailAlloc_424_, 2, v_tail_413_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__7___redArg(lean_object* v_a_426_, lean_object* v_x_427_){
_start:
{
if (lean_obj_tag(v_x_427_) == 0)
{
uint8_t v___x_428_; 
v___x_428_ = 0;
return v___x_428_;
}
else
{
lean_object* v_key_429_; lean_object* v_tail_430_; uint8_t v___x_431_; 
v_key_429_ = lean_ctor_get(v_x_427_, 0);
v_tail_430_ = lean_ctor_get(v_x_427_, 2);
v___x_431_ = l_Lean_Syntax_instBEqRange_beq(v_key_429_, v_a_426_);
if (v___x_431_ == 0)
{
v_x_427_ = v_tail_430_;
goto _start;
}
else
{
return v___x_431_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__7___redArg___boxed(lean_object* v_a_433_, lean_object* v_x_434_){
_start:
{
uint8_t v_res_435_; lean_object* v_r_436_; 
v_res_435_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__7___redArg(v_a_433_, v_x_434_);
lean_dec(v_x_434_);
lean_dec_ref(v_a_433_);
v_r_436_ = lean_box(v_res_435_);
return v_r_436_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4___redArg(lean_object* v_m_437_, lean_object* v_a_438_, lean_object* v_b_439_){
_start:
{
lean_object* v_size_440_; lean_object* v_buckets_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_484_; 
v_size_440_ = lean_ctor_get(v_m_437_, 0);
v_buckets_441_ = lean_ctor_get(v_m_437_, 1);
v_isSharedCheck_484_ = !lean_is_exclusive(v_m_437_);
if (v_isSharedCheck_484_ == 0)
{
v___x_443_ = v_m_437_;
v_isShared_444_ = v_isSharedCheck_484_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_buckets_441_);
lean_inc(v_size_440_);
lean_dec(v_m_437_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_484_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_445_; uint64_t v___x_446_; uint64_t v___x_447_; uint64_t v___x_448_; uint64_t v_fold_449_; uint64_t v___x_450_; uint64_t v___x_451_; uint64_t v___x_452_; size_t v___x_453_; size_t v___x_454_; size_t v___x_455_; size_t v___x_456_; size_t v___x_457_; lean_object* v_bkt_458_; uint8_t v___x_459_; 
v___x_445_ = lean_array_get_size(v_buckets_441_);
v___x_446_ = l_Lean_Syntax_instHashableRange_hash(v_a_438_);
v___x_447_ = 32ULL;
v___x_448_ = lean_uint64_shift_right(v___x_446_, v___x_447_);
v_fold_449_ = lean_uint64_xor(v___x_446_, v___x_448_);
v___x_450_ = 16ULL;
v___x_451_ = lean_uint64_shift_right(v_fold_449_, v___x_450_);
v___x_452_ = lean_uint64_xor(v_fold_449_, v___x_451_);
v___x_453_ = lean_uint64_to_usize(v___x_452_);
v___x_454_ = lean_usize_of_nat(v___x_445_);
v___x_455_ = ((size_t)1ULL);
v___x_456_ = lean_usize_sub(v___x_454_, v___x_455_);
v___x_457_ = lean_usize_land(v___x_453_, v___x_456_);
v_bkt_458_ = lean_array_uget_borrowed(v_buckets_441_, v___x_457_);
v___x_459_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__7___redArg(v_a_438_, v_bkt_458_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; lean_object* v_size_x27_461_; lean_object* v___x_462_; lean_object* v_buckets_x27_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; uint8_t v___x_469_; 
v___x_460_ = lean_unsigned_to_nat(1u);
v_size_x27_461_ = lean_nat_add(v_size_440_, v___x_460_);
lean_dec(v_size_440_);
lean_inc(v_bkt_458_);
v___x_462_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_462_, 0, v_a_438_);
lean_ctor_set(v___x_462_, 1, v_b_439_);
lean_ctor_set(v___x_462_, 2, v_bkt_458_);
v_buckets_x27_463_ = lean_array_uset(v_buckets_441_, v___x_457_, v___x_462_);
v___x_464_ = lean_unsigned_to_nat(4u);
v___x_465_ = lean_nat_mul(v_size_x27_461_, v___x_464_);
v___x_466_ = lean_unsigned_to_nat(3u);
v___x_467_ = lean_nat_div(v___x_465_, v___x_466_);
lean_dec(v___x_465_);
v___x_468_ = lean_array_get_size(v_buckets_x27_463_);
v___x_469_ = lean_nat_dec_le(v___x_467_, v___x_468_);
lean_dec(v___x_467_);
if (v___x_469_ == 0)
{
lean_object* v_val_470_; lean_object* v___x_472_; 
v_val_470_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10___redArg(v_buckets_x27_463_);
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 1, v_val_470_);
lean_ctor_set(v___x_443_, 0, v_size_x27_461_);
v___x_472_ = v___x_443_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_size_x27_461_);
lean_ctor_set(v_reuseFailAlloc_473_, 1, v_val_470_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
else
{
lean_object* v___x_475_; 
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 1, v_buckets_x27_463_);
lean_ctor_set(v___x_443_, 0, v_size_x27_461_);
v___x_475_ = v___x_443_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_size_x27_461_);
lean_ctor_set(v_reuseFailAlloc_476_, 1, v_buckets_x27_463_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
else
{
lean_object* v___x_477_; lean_object* v_buckets_x27_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_482_; 
lean_inc(v_bkt_458_);
v___x_477_ = lean_box(0);
v_buckets_x27_478_ = lean_array_uset(v_buckets_441_, v___x_457_, v___x_477_);
v___x_479_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__11___redArg(v_a_438_, v_b_439_, v_bkt_458_);
v___x_480_ = lean_array_uset(v_buckets_x27_478_, v___x_457_, v___x_479_);
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 1, v___x_480_);
v___x_482_ = v___x_443_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_size_440_);
lean_ctor_set(v_reuseFailAlloc_483_, 1, v___x_480_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5___redArg(lean_object* v_a_485_, lean_object* v_x_486_){
_start:
{
if (lean_obj_tag(v_x_486_) == 0)
{
lean_object* v___x_487_; 
v___x_487_ = lean_box(0);
return v___x_487_;
}
else
{
lean_object* v_key_488_; lean_object* v_value_489_; lean_object* v_tail_490_; uint8_t v___x_491_; 
v_key_488_ = lean_ctor_get(v_x_486_, 0);
v_value_489_ = lean_ctor_get(v_x_486_, 1);
v_tail_490_ = lean_ctor_get(v_x_486_, 2);
v___x_491_ = l_Lean_Syntax_instBEqRange_beq(v_key_488_, v_a_485_);
if (v___x_491_ == 0)
{
v_x_486_ = v_tail_490_;
goto _start;
}
else
{
lean_object* v___x_493_; 
lean_inc(v_value_489_);
v___x_493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_493_, 0, v_value_489_);
return v___x_493_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5___redArg___boxed(lean_object* v_a_494_, lean_object* v_x_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5___redArg(v_a_494_, v_x_495_);
lean_dec(v_x_495_);
lean_dec_ref(v_a_494_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2___redArg(lean_object* v_m_497_, lean_object* v_a_498_){
_start:
{
lean_object* v_buckets_499_; lean_object* v___x_500_; uint64_t v___x_501_; uint64_t v___x_502_; uint64_t v___x_503_; uint64_t v_fold_504_; uint64_t v___x_505_; uint64_t v___x_506_; uint64_t v___x_507_; size_t v___x_508_; size_t v___x_509_; size_t v___x_510_; size_t v___x_511_; size_t v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v_buckets_499_ = lean_ctor_get(v_m_497_, 1);
v___x_500_ = lean_array_get_size(v_buckets_499_);
v___x_501_ = l_Lean_Syntax_instHashableRange_hash(v_a_498_);
v___x_502_ = 32ULL;
v___x_503_ = lean_uint64_shift_right(v___x_501_, v___x_502_);
v_fold_504_ = lean_uint64_xor(v___x_501_, v___x_503_);
v___x_505_ = 16ULL;
v___x_506_ = lean_uint64_shift_right(v_fold_504_, v___x_505_);
v___x_507_ = lean_uint64_xor(v_fold_504_, v___x_506_);
v___x_508_ = lean_uint64_to_usize(v___x_507_);
v___x_509_ = lean_usize_of_nat(v___x_500_);
v___x_510_ = ((size_t)1ULL);
v___x_511_ = lean_usize_sub(v___x_509_, v___x_510_);
v___x_512_ = lean_usize_land(v___x_508_, v___x_511_);
v___x_513_ = lean_array_uget_borrowed(v_buckets_499_, v___x_512_);
v___x_514_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5___redArg(v_a_498_, v___x_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2___redArg___boxed(lean_object* v_m_515_, lean_object* v_a_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2___redArg(v_m_515_, v_a_516_);
lean_dec_ref(v_a_516_);
lean_dec_ref(v_m_515_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__8___redArg(lean_object* v_a_518_, lean_object* v_x_519_){
_start:
{
if (lean_obj_tag(v_x_519_) == 0)
{
return v_x_519_;
}
else
{
lean_object* v_key_520_; lean_object* v_value_521_; lean_object* v_tail_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_531_; 
v_key_520_ = lean_ctor_get(v_x_519_, 0);
v_value_521_ = lean_ctor_get(v_x_519_, 1);
v_tail_522_ = lean_ctor_get(v_x_519_, 2);
v_isSharedCheck_531_ = !lean_is_exclusive(v_x_519_);
if (v_isSharedCheck_531_ == 0)
{
v___x_524_ = v_x_519_;
v_isShared_525_ = v_isSharedCheck_531_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_tail_522_);
lean_inc(v_value_521_);
lean_inc(v_key_520_);
lean_dec(v_x_519_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_531_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
uint8_t v___x_526_; 
v___x_526_ = l_Lean_Syntax_instBEqRange_beq(v_key_520_, v_a_518_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; lean_object* v___x_529_; 
v___x_527_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__8___redArg(v_a_518_, v_tail_522_);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 2, v___x_527_);
v___x_529_ = v___x_524_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_key_520_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v_value_521_);
lean_ctor_set(v_reuseFailAlloc_530_, 2, v___x_527_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
else
{
lean_del_object(v___x_524_);
lean_dec(v_value_521_);
lean_dec(v_key_520_);
return v_tail_522_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__8___redArg___boxed(lean_object* v_a_532_, lean_object* v_x_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__8___redArg(v_a_532_, v_x_533_);
lean_dec_ref(v_a_532_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3___redArg(lean_object* v_m_535_, lean_object* v_a_536_){
_start:
{
lean_object* v_size_537_; lean_object* v_buckets_538_; lean_object* v___x_539_; uint64_t v___x_540_; uint64_t v___x_541_; uint64_t v___x_542_; uint64_t v_fold_543_; uint64_t v___x_544_; uint64_t v___x_545_; uint64_t v___x_546_; size_t v___x_547_; size_t v___x_548_; size_t v___x_549_; size_t v___x_550_; size_t v___x_551_; lean_object* v_bkt_552_; uint8_t v___x_553_; 
v_size_537_ = lean_ctor_get(v_m_535_, 0);
v_buckets_538_ = lean_ctor_get(v_m_535_, 1);
v___x_539_ = lean_array_get_size(v_buckets_538_);
v___x_540_ = l_Lean_Syntax_instHashableRange_hash(v_a_536_);
v___x_541_ = 32ULL;
v___x_542_ = lean_uint64_shift_right(v___x_540_, v___x_541_);
v_fold_543_ = lean_uint64_xor(v___x_540_, v___x_542_);
v___x_544_ = 16ULL;
v___x_545_ = lean_uint64_shift_right(v_fold_543_, v___x_544_);
v___x_546_ = lean_uint64_xor(v_fold_543_, v___x_545_);
v___x_547_ = lean_uint64_to_usize(v___x_546_);
v___x_548_ = lean_usize_of_nat(v___x_539_);
v___x_549_ = ((size_t)1ULL);
v___x_550_ = lean_usize_sub(v___x_548_, v___x_549_);
v___x_551_ = lean_usize_land(v___x_547_, v___x_550_);
v_bkt_552_ = lean_array_uget_borrowed(v_buckets_538_, v___x_551_);
v___x_553_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__7___redArg(v_a_536_, v_bkt_552_);
if (v___x_553_ == 0)
{
return v_m_535_;
}
else
{
lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_566_; 
lean_inc(v_bkt_552_);
lean_inc_ref(v_buckets_538_);
lean_inc(v_size_537_);
v_isSharedCheck_566_ = !lean_is_exclusive(v_m_535_);
if (v_isSharedCheck_566_ == 0)
{
lean_object* v_unused_567_; lean_object* v_unused_568_; 
v_unused_567_ = lean_ctor_get(v_m_535_, 1);
lean_dec(v_unused_567_);
v_unused_568_ = lean_ctor_get(v_m_535_, 0);
lean_dec(v_unused_568_);
v___x_555_ = v_m_535_;
v_isShared_556_ = v_isSharedCheck_566_;
goto v_resetjp_554_;
}
else
{
lean_dec(v_m_535_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_566_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_557_; lean_object* v_buckets_x27_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_564_; 
v___x_557_ = lean_box(0);
v_buckets_x27_558_ = lean_array_uset(v_buckets_538_, v___x_551_, v___x_557_);
v___x_559_ = lean_unsigned_to_nat(1u);
v___x_560_ = lean_nat_sub(v_size_537_, v___x_559_);
lean_dec(v_size_537_);
v___x_561_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__8___redArg(v_a_536_, v_bkt_552_);
v___x_562_ = lean_array_uset(v_buckets_x27_558_, v___x_551_, v___x_561_);
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 1, v___x_562_);
lean_ctor_set(v___x_555_, 0, v___x_560_);
v___x_564_ = v___x_555_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_560_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v___x_562_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3___redArg___boxed(lean_object* v_m_569_, lean_object* v_a_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3___redArg(v_m_569_, v_a_570_);
lean_dec_ref(v_a_570_);
return v_res_571_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg(lean_object* v_multigoals_608_, lean_object* v_x_609_, lean_object* v_a_610_){
_start:
{
switch(lean_obj_tag(v_x_609_))
{
case 0:
{
lean_object* v_t_612_; 
v_t_612_ = lean_ctor_get(v_x_609_, 1);
lean_inc_ref(v_t_612_);
lean_dec_ref_known(v_x_609_, 2);
v_x_609_ = v_t_612_;
goto _start;
}
case 1:
{
lean_object* v_i_614_; lean_object* v_children_615_; lean_object* v_snd_617_; lean_object* v_snd_621_; 
v_i_614_ = lean_ctor_get(v_x_609_, 0);
lean_inc_ref(v_i_614_);
v_children_615_ = lean_ctor_get(v_x_609_, 1);
lean_inc_ref(v_children_615_);
lean_dec_ref_known(v_x_609_, 2);
if (lean_obj_tag(v_i_614_) == 0)
{
lean_object* v_i_624_; lean_object* v_toElabInfo_625_; lean_object* v_goalsBefore_626_; lean_object* v_stx_627_; uint8_t v___x_628_; lean_object* v___x_629_; 
v_i_624_ = lean_ctor_get(v_i_614_, 0);
v_toElabInfo_625_ = lean_ctor_get(v_i_624_, 0);
v_goalsBefore_626_ = lean_ctor_get(v_i_624_, 2);
v_stx_627_ = lean_ctor_get(v_toElabInfo_625_, 1);
v___x_628_ = 1;
v___x_629_ = l_Lean_Syntax_getRange_x3f(v_stx_627_, v___x_628_);
if (lean_obj_tag(v___x_629_) == 1)
{
lean_object* v_val_630_; lean_object* v___y_632_; lean_object* v___x_634_; lean_object* v___x_635_; 
v_val_630_ = lean_ctor_get(v___x_629_, 0);
lean_inc(v_val_630_);
lean_dec_ref_known(v___x_629_, 1);
v___x_634_ = lean_st_ref_get(v_a_610_);
v___x_635_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2___redArg(v___x_634_, v_val_630_);
lean_dec(v___x_634_);
if (lean_obj_tag(v___x_635_) == 1)
{
lean_object* v_val_636_; lean_object* v___y_638_; uint8_t v___y_639_; lean_object* v___x_650_; lean_object* v___x_651_; uint8_t v___x_652_; lean_object* v___y_654_; 
v_val_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_val_636_);
lean_dec_ref_known(v___x_635_, 1);
lean_inc(v_stx_627_);
v___x_650_ = l_Lean_Syntax_getKind(v_stx_627_);
v___x_651_ = ((lean_object*)(l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__1));
v___x_652_ = lean_name_eq(v___x_650_, v___x_651_);
if (v___x_652_ == 0)
{
lean_object* v___x_680_; uint8_t v___x_681_; lean_object* v___y_683_; uint8_t v___y_699_; 
v___x_680_ = ((lean_object*)(l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__3));
v___x_681_ = lean_name_eq(v___x_650_, v___x_680_);
lean_dec(v___x_650_);
if (v___x_681_ == 0)
{
lean_object* v___x_701_; 
lean_dec(v_val_636_);
lean_dec(v_val_630_);
lean_dec_ref_known(v_i_614_, 1);
v___x_701_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___redArg(v_multigoals_608_, v_children_615_, v_a_610_);
lean_dec_ref(v_children_615_);
return v___x_701_;
}
else
{
lean_object* v___x_702_; lean_object* v___x_703_; uint8_t v___x_704_; 
v___x_702_ = l_List_lengthTR___redArg(v_goalsBefore_626_);
v___x_703_ = lean_unsigned_to_nat(1u);
v___x_704_ = lean_nat_dec_eq(v___x_702_, v___x_703_);
lean_dec(v___x_702_);
if (v___x_704_ == 0)
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; uint8_t v___x_708_; 
v___x_705_ = lean_unsigned_to_nat(0u);
v___x_706_ = l_Lean_Syntax_getArg(v_stx_627_, v___x_705_);
v___x_707_ = l_Lean_Syntax_getKind(v___x_706_);
v___x_708_ = l_Lean_NameSet_contains(v_multigoals_608_, v___x_707_);
lean_dec(v___x_707_);
if (v___x_708_ == 0)
{
v___y_699_ = v___x_681_;
goto v___jp_698_;
}
else
{
v___y_699_ = v___x_652_;
goto v___jp_698_;
}
}
else
{
goto v___jp_685_;
}
}
v___jp_682_:
{
lean_object* v___x_684_; 
v___x_684_ = lean_st_ref_take(v_a_610_);
if (lean_obj_tag(v___y_683_) == 0)
{
v___y_638_ = v___x_684_;
v___y_639_ = v___x_652_;
goto v___jp_637_;
}
else
{
v___y_638_ = v___x_684_;
v___y_639_ = v___x_681_;
goto v___jp_637_;
}
}
v___jp_685_:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_686_ = lean_unsigned_to_nat(1u);
v___x_687_ = ((lean_object*)(l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__11));
lean_inc_ref(v_children_615_);
v___x_688_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_getPath(v_i_614_, v_children_615_, v___x_687_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v___x_689_; 
v___x_689_ = lean_box(0);
v___y_683_ = v___x_689_;
goto v___jp_682_;
}
else
{
lean_object* v_val_690_; 
v_val_690_ = lean_ctor_get(v___x_688_, 0);
lean_inc(v_val_690_);
lean_dec_ref_known(v___x_688_, 1);
if (lean_obj_tag(v_val_690_) == 0)
{
lean_object* v_i_691_; lean_object* v_goalsAfter_692_; lean_object* v___x_693_; uint8_t v___x_694_; 
v_i_691_ = lean_ctor_get(v_val_690_, 0);
lean_inc_ref(v_i_691_);
lean_dec_ref_known(v_val_690_, 1);
v_goalsAfter_692_ = lean_ctor_get(v_i_691_, 4);
lean_inc(v_goalsAfter_692_);
lean_dec_ref(v_i_691_);
v___x_693_ = l_List_lengthTR___redArg(v_goalsAfter_692_);
lean_dec(v_goalsAfter_692_);
v___x_694_ = lean_nat_dec_eq(v___x_693_, v___x_686_);
lean_dec(v___x_693_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; 
v___x_695_ = lean_box(0);
v___y_683_ = v___x_695_;
goto v___jp_682_;
}
else
{
lean_object* v___x_696_; 
v___x_696_ = ((lean_object*)(l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__7));
v___y_683_ = v___x_696_;
goto v___jp_682_;
}
}
else
{
lean_object* v___x_697_; 
lean_dec(v_val_690_);
v___x_697_ = lean_box(0);
v___y_683_ = v___x_697_;
goto v___jp_682_;
}
}
}
v___jp_698_:
{
if (v___y_699_ == 0)
{
lean_object* v___x_700_; 
lean_dec_ref_known(v_i_614_, 1);
v___x_700_ = lean_box(0);
v___y_683_ = v___x_700_;
goto v___jp_682_;
}
else
{
goto v___jp_685_;
}
}
}
else
{
lean_object* v___x_709_; lean_object* v___x_710_; uint8_t v___x_711_; 
lean_dec(v___x_650_);
v___x_709_ = l_List_lengthTR___redArg(v_goalsBefore_626_);
v___x_710_ = lean_unsigned_to_nat(1u);
v___x_711_ = lean_nat_dec_eq(v___x_709_, v___x_710_);
lean_dec(v___x_709_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; uint8_t v___x_715_; 
v___x_712_ = lean_unsigned_to_nat(0u);
v___x_713_ = l_Lean_Syntax_getArg(v_stx_627_, v___x_712_);
v___x_714_ = l_Lean_Syntax_getKind(v___x_713_);
v___x_715_ = l_Lean_NameSet_contains(v_multigoals_608_, v___x_714_);
lean_dec(v___x_714_);
if (v___x_715_ == 0)
{
if (v___x_652_ == 0)
{
lean_dec_ref_known(v_i_614_, 1);
goto v___jp_678_;
}
else
{
goto v___jp_665_;
}
}
else
{
lean_dec_ref_known(v_i_614_, 1);
goto v___jp_678_;
}
}
else
{
goto v___jp_665_;
}
}
v___jp_637_:
{
if (v___y_639_ == 0)
{
lean_object* v___x_640_; 
lean_dec(v_val_636_);
v___x_640_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3___redArg(v___y_638_, v_val_630_);
lean_dec(v_val_630_);
v_snd_621_ = v___x_640_;
goto v___jp_620_;
}
else
{
lean_object* v_stx_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_649_; 
v_stx_641_ = lean_ctor_get(v_val_636_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v_val_636_);
if (v_isSharedCheck_649_ == 0)
{
v___x_643_ = v_val_636_;
v_isShared_644_ = v_isSharedCheck_649_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_stx_641_);
lean_dec(v_val_636_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_649_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_646_; 
if (v_isShared_644_ == 0)
{
v___x_646_ = v___x_643_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_stx_641_);
v___x_646_ = v_reuseFailAlloc_648_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
lean_object* v___x_647_; 
lean_ctor_set_uint8(v___x_646_, sizeof(void*)*1, v___x_628_);
v___x_647_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4___redArg(v___y_638_, v_val_630_, v___x_646_);
v_snd_621_ = v___x_647_;
goto v___jp_620_;
}
}
}
}
v___jp_653_:
{
lean_object* v___x_655_; 
v___x_655_ = lean_st_ref_take(v_a_610_);
if (lean_obj_tag(v___y_654_) == 0)
{
lean_dec(v_val_636_);
v___y_632_ = v___x_655_;
goto v___jp_631_;
}
else
{
if (v___x_652_ == 0)
{
lean_dec(v_val_636_);
v___y_632_ = v___x_655_;
goto v___jp_631_;
}
else
{
lean_object* v_stx_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_664_; 
v_stx_656_ = lean_ctor_get(v_val_636_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v_val_636_);
if (v_isSharedCheck_664_ == 0)
{
v___x_658_ = v_val_636_;
v_isShared_659_ = v_isSharedCheck_664_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_stx_656_);
lean_dec(v_val_636_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_664_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_661_; 
if (v_isShared_659_ == 0)
{
v___x_661_ = v___x_658_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_stx_656_);
v___x_661_ = v_reuseFailAlloc_663_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
lean_object* v___x_662_; 
lean_ctor_set_uint8(v___x_661_, sizeof(void*)*1, v___x_628_);
v___x_662_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4___redArg(v___x_655_, v_val_630_, v___x_661_);
v_snd_617_ = v___x_662_;
goto v___jp_616_;
}
}
}
}
}
v___jp_665_:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_666_ = lean_unsigned_to_nat(1u);
v___x_667_ = ((lean_object*)(l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__6));
lean_inc_ref(v_children_615_);
v___x_668_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_getPath(v_i_614_, v_children_615_, v___x_667_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v___x_669_; 
v___x_669_ = lean_box(0);
v___y_654_ = v___x_669_;
goto v___jp_653_;
}
else
{
lean_object* v_val_670_; 
v_val_670_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_val_670_);
lean_dec_ref_known(v___x_668_, 1);
if (lean_obj_tag(v_val_670_) == 0)
{
lean_object* v_i_671_; lean_object* v_goalsAfter_672_; lean_object* v___x_673_; uint8_t v___x_674_; 
v_i_671_ = lean_ctor_get(v_val_670_, 0);
lean_inc_ref(v_i_671_);
lean_dec_ref_known(v_val_670_, 1);
v_goalsAfter_672_ = lean_ctor_get(v_i_671_, 4);
lean_inc(v_goalsAfter_672_);
lean_dec_ref(v_i_671_);
v___x_673_ = l_List_lengthTR___redArg(v_goalsAfter_672_);
lean_dec(v_goalsAfter_672_);
v___x_674_ = lean_nat_dec_eq(v___x_673_, v___x_666_);
lean_dec(v___x_673_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; 
v___x_675_ = lean_box(0);
v___y_654_ = v___x_675_;
goto v___jp_653_;
}
else
{
lean_object* v___x_676_; 
v___x_676_ = ((lean_object*)(l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__7));
v___y_654_ = v___x_676_;
goto v___jp_653_;
}
}
else
{
lean_object* v___x_677_; 
lean_dec(v_val_670_);
v___x_677_ = lean_box(0);
v___y_654_ = v___x_677_;
goto v___jp_653_;
}
}
}
v___jp_678_:
{
lean_object* v___x_679_; 
v___x_679_ = lean_box(0);
v___y_654_ = v___x_679_;
goto v___jp_653_;
}
}
else
{
lean_object* v___x_716_; 
lean_dec(v___x_635_);
lean_dec(v_val_630_);
lean_dec_ref_known(v_i_614_, 1);
v___x_716_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___redArg(v_multigoals_608_, v_children_615_, v_a_610_);
lean_dec_ref(v_children_615_);
return v___x_716_;
}
v___jp_631_:
{
lean_object* v___x_633_; 
v___x_633_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3___redArg(v___y_632_, v_val_630_);
lean_dec(v_val_630_);
v_snd_617_ = v___x_633_;
goto v___jp_616_;
}
}
else
{
lean_object* v___x_717_; 
lean_dec(v___x_629_);
lean_dec_ref_known(v_i_614_, 1);
v___x_717_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___redArg(v_multigoals_608_, v_children_615_, v_a_610_);
lean_dec_ref(v_children_615_);
return v___x_717_;
}
}
else
{
lean_object* v___x_718_; 
lean_dec_ref(v_i_614_);
v___x_718_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___redArg(v_multigoals_608_, v_children_615_, v_a_610_);
lean_dec_ref(v_children_615_);
return v___x_718_;
}
v___jp_616_:
{
lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_618_ = lean_st_ref_put(v_a_610_, v_snd_617_);
v___x_619_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___redArg(v_multigoals_608_, v_children_615_, v_a_610_);
lean_dec_ref(v_children_615_);
return v___x_619_;
}
v___jp_620_:
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = lean_st_ref_put(v_a_610_, v_snd_621_);
v___x_623_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___redArg(v_multigoals_608_, v_children_615_, v_a_610_);
lean_dec_ref(v_children_615_);
return v___x_623_;
}
}
default: 
{
lean_object* v___x_719_; 
lean_dec_ref_known(v_x_609_, 1);
v___x_719_ = lean_box(0);
return v___x_719_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(lean_object* v_multigoals_720_, lean_object* v_as_721_, size_t v_i_722_, size_t v_stop_723_, lean_object* v_b_724_, lean_object* v___y_725_){
_start:
{
uint8_t v___x_727_; 
v___x_727_ = lean_usize_dec_eq(v_i_722_, v_stop_723_);
if (v___x_727_ == 0)
{
lean_object* v___x_728_; lean_object* v___x_729_; size_t v___x_730_; size_t v___x_731_; 
v___x_728_ = lean_array_uget_borrowed(v_as_721_, v_i_722_);
lean_inc(v___x_728_);
v___x_729_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg(v_multigoals_720_, v___x_728_, v___y_725_);
v___x_730_ = ((size_t)1ULL);
v___x_731_ = lean_usize_add(v_i_722_, v___x_730_);
v_i_722_ = v___x_731_;
v_b_724_ = v___x_729_;
goto _start;
}
else
{
return v_b_724_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2___redArg(lean_object* v_multigoals_733_, lean_object* v_x_734_, lean_object* v___y_735_){
_start:
{
if (lean_obj_tag(v_x_734_) == 0)
{
lean_object* v_cs_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; uint8_t v___x_741_; 
v_cs_737_ = lean_ctor_get(v_x_734_, 0);
v___x_738_ = lean_unsigned_to_nat(0u);
v___x_739_ = lean_array_get_size(v_cs_737_);
v___x_740_ = lean_box(0);
v___x_741_ = lean_nat_dec_lt(v___x_738_, v___x_739_);
if (v___x_741_ == 0)
{
return v___x_740_;
}
else
{
size_t v___x_742_; size_t v___x_743_; lean_object* v___x_744_; 
v___x_742_ = ((size_t)0ULL);
v___x_743_ = lean_usize_of_nat(v___x_739_);
v___x_744_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___redArg(v_multigoals_733_, v_cs_737_, v___x_742_, v___x_743_, v___x_740_, v___y_735_);
return v___x_744_;
}
}
else
{
lean_object* v_vs_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; uint8_t v___x_749_; 
v_vs_745_ = lean_ctor_get(v_x_734_, 0);
v___x_746_ = lean_unsigned_to_nat(0u);
v___x_747_ = lean_array_get_size(v_vs_745_);
v___x_748_ = lean_box(0);
v___x_749_ = lean_nat_dec_lt(v___x_746_, v___x_747_);
if (v___x_749_ == 0)
{
return v___x_748_;
}
else
{
size_t v___x_750_; size_t v___x_751_; lean_object* v___x_752_; 
v___x_750_ = ((size_t)0ULL);
v___x_751_ = lean_usize_of_nat(v___x_747_);
v___x_752_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_733_, v_vs_745_, v___x_750_, v___x_751_, v___x_748_, v___y_735_);
return v___x_752_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___redArg(lean_object* v_multigoals_753_, lean_object* v_as_754_, size_t v_i_755_, size_t v_stop_756_, lean_object* v_b_757_, lean_object* v___y_758_){
_start:
{
uint8_t v___x_760_; 
v___x_760_ = lean_usize_dec_eq(v_i_755_, v_stop_756_);
if (v___x_760_ == 0)
{
lean_object* v___x_761_; lean_object* v___x_762_; size_t v___x_763_; size_t v___x_764_; 
v___x_761_ = lean_array_uget_borrowed(v_as_754_, v_i_755_);
v___x_762_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2___redArg(v_multigoals_753_, v___x_761_, v___y_758_);
v___x_763_ = ((size_t)1ULL);
v___x_764_ = lean_usize_add(v_i_755_, v___x_763_);
v_i_755_ = v___x_764_;
v_b_757_ = v___x_762_;
goto _start;
}
else
{
return v_b_757_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg(lean_object* v_multigoals_766_, lean_object* v_x_767_, size_t v_x_768_, size_t v_x_769_, lean_object* v___y_770_){
_start:
{
if (lean_obj_tag(v_x_767_) == 0)
{
lean_object* v_cs_772_; lean_object* v___x_773_; size_t v___x_774_; lean_object* v_j_775_; lean_object* v___x_776_; size_t v___x_777_; size_t v___x_778_; size_t v___x_779_; size_t v___x_780_; size_t v___x_781_; size_t v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; uint8_t v___x_788_; 
v_cs_772_ = lean_ctor_get(v_x_767_, 0);
v___x_773_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg___closed__0);
v___x_774_ = lean_usize_shift_right(v_x_768_, v_x_769_);
v_j_775_ = lean_usize_to_nat(v___x_774_);
v___x_776_ = lean_array_get_borrowed(v___x_773_, v_cs_772_, v_j_775_);
v___x_777_ = ((size_t)1ULL);
v___x_778_ = lean_usize_shift_left(v___x_777_, v_x_769_);
v___x_779_ = lean_usize_sub(v___x_778_, v___x_777_);
v___x_780_ = lean_usize_land(v_x_768_, v___x_779_);
v___x_781_ = ((size_t)5ULL);
v___x_782_ = lean_usize_sub(v_x_769_, v___x_781_);
v___x_783_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg(v_multigoals_766_, v___x_776_, v___x_780_, v___x_782_, v___y_770_);
v___x_784_ = lean_unsigned_to_nat(1u);
v___x_785_ = lean_nat_add(v_j_775_, v___x_784_);
lean_dec(v_j_775_);
v___x_786_ = lean_array_get_size(v_cs_772_);
v___x_787_ = lean_box(0);
v___x_788_ = lean_nat_dec_lt(v___x_785_, v___x_786_);
if (v___x_788_ == 0)
{
lean_dec(v___x_785_);
return v___x_787_;
}
else
{
size_t v___x_789_; size_t v___x_790_; lean_object* v___x_791_; 
v___x_789_ = lean_usize_of_nat(v___x_785_);
lean_dec(v___x_785_);
v___x_790_ = lean_usize_of_nat(v___x_786_);
v___x_791_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___redArg(v_multigoals_766_, v_cs_772_, v___x_789_, v___x_790_, v___x_787_, v___y_770_);
return v___x_791_;
}
}
else
{
lean_object* v_vs_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; uint8_t v___x_796_; 
v_vs_792_ = lean_ctor_get(v_x_767_, 0);
v___x_793_ = lean_usize_to_nat(v_x_768_);
v___x_794_ = lean_array_get_size(v_vs_792_);
v___x_795_ = lean_box(0);
v___x_796_ = lean_nat_dec_lt(v___x_793_, v___x_794_);
if (v___x_796_ == 0)
{
lean_dec(v___x_793_);
return v___x_795_;
}
else
{
size_t v___x_797_; size_t v___x_798_; lean_object* v___x_799_; 
v___x_797_ = lean_usize_of_nat(v___x_793_);
lean_dec(v___x_793_);
v___x_798_ = lean_usize_of_nat(v___x_794_);
v___x_799_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_766_, v_vs_792_, v___x_797_, v___x_798_, v___x_795_, v___y_770_);
return v___x_799_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2___redArg(lean_object* v_multigoals_800_, lean_object* v_t_801_, lean_object* v___y_802_){
_start:
{
lean_object* v_root_804_; lean_object* v_tail_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; uint8_t v___x_810_; 
v_root_804_ = lean_ctor_get(v_t_801_, 0);
v_tail_805_ = lean_ctor_get(v_t_801_, 1);
v___x_806_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2___redArg(v_multigoals_800_, v_root_804_, v___y_802_);
v___x_807_ = lean_unsigned_to_nat(0u);
v___x_808_ = lean_array_get_size(v_tail_805_);
v___x_809_ = lean_box(0);
v___x_810_ = lean_nat_dec_lt(v___x_807_, v___x_808_);
if (v___x_810_ == 0)
{
return v___x_809_;
}
else
{
size_t v___x_811_; size_t v___x_812_; lean_object* v___x_813_; 
v___x_811_ = ((size_t)0ULL);
v___x_812_ = lean_usize_of_nat(v___x_808_);
v___x_813_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_800_, v_tail_805_, v___x_811_, v___x_812_, v___x_809_, v___y_802_);
return v___x_813_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0___redArg(lean_object* v_multigoals_814_, lean_object* v_t_815_, lean_object* v_start_816_, lean_object* v___y_817_){
_start:
{
lean_object* v___x_819_; uint8_t v___x_820_; 
v___x_819_ = lean_unsigned_to_nat(0u);
v___x_820_ = lean_nat_dec_eq(v_start_816_, v___x_819_);
if (v___x_820_ == 0)
{
lean_object* v_root_821_; lean_object* v_tail_822_; size_t v_shift_823_; lean_object* v_tailOff_824_; uint8_t v___x_825_; 
v_root_821_ = lean_ctor_get(v_t_815_, 0);
v_tail_822_ = lean_ctor_get(v_t_815_, 1);
v_shift_823_ = lean_ctor_get_usize(v_t_815_, 4);
v_tailOff_824_ = lean_ctor_get(v_t_815_, 3);
v___x_825_ = lean_nat_dec_le(v_tailOff_824_, v_start_816_);
if (v___x_825_ == 0)
{
size_t v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; uint8_t v___x_830_; 
v___x_826_ = lean_usize_of_nat(v_start_816_);
v___x_827_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg(v_multigoals_814_, v_root_821_, v___x_826_, v_shift_823_, v___y_817_);
v___x_828_ = lean_array_get_size(v_tail_822_);
v___x_829_ = lean_box(0);
v___x_830_ = lean_nat_dec_lt(v___x_819_, v___x_828_);
if (v___x_830_ == 0)
{
return v___x_829_;
}
else
{
size_t v___x_831_; size_t v___x_832_; lean_object* v___x_833_; 
v___x_831_ = ((size_t)0ULL);
v___x_832_ = lean_usize_of_nat(v___x_828_);
v___x_833_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_814_, v_tail_822_, v___x_831_, v___x_832_, v___x_829_, v___y_817_);
return v___x_833_;
}
}
else
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; uint8_t v___x_837_; 
v___x_834_ = lean_nat_sub(v_start_816_, v_tailOff_824_);
v___x_835_ = lean_array_get_size(v_tail_822_);
v___x_836_ = lean_box(0);
v___x_837_ = lean_nat_dec_lt(v___x_834_, v___x_835_);
if (v___x_837_ == 0)
{
lean_dec(v___x_834_);
return v___x_836_;
}
else
{
size_t v___x_838_; size_t v___x_839_; lean_object* v___x_840_; 
v___x_838_ = lean_usize_of_nat(v___x_834_);
lean_dec(v___x_834_);
v___x_839_ = lean_usize_of_nat(v___x_835_);
v___x_840_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_814_, v_tail_822_, v___x_838_, v___x_839_, v___x_836_, v___y_817_);
return v___x_840_;
}
}
}
else
{
lean_object* v___x_841_; 
v___x_841_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2___redArg(v_multigoals_814_, v_t_815_, v___y_817_);
return v___x_841_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___redArg(lean_object* v_multigoals_842_, lean_object* v_trees_843_, lean_object* v_a_844_){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_846_ = lean_unsigned_to_nat(0u);
v___x_847_ = l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0___redArg(v_multigoals_842_, v_trees_843_, v___x_846_, v_a_844_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___redArg___boxed(lean_object* v_multigoals_848_, lean_object* v_trees_849_, lean_object* v_a_850_, lean_object* v_a_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___redArg(v_multigoals_848_, v_trees_849_, v_a_850_);
lean_dec(v_a_850_);
lean_dec_ref(v_trees_849_);
lean_dec(v_multigoals_848_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg___boxed(lean_object* v_multigoals_853_, lean_object* v_as_854_, lean_object* v_i_855_, lean_object* v_stop_856_, lean_object* v_b_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
size_t v_i_boxed_860_; size_t v_stop_boxed_861_; lean_object* v_res_862_; 
v_i_boxed_860_ = lean_unbox_usize(v_i_855_);
lean_dec(v_i_855_);
v_stop_boxed_861_ = lean_unbox_usize(v_stop_856_);
lean_dec(v_stop_856_);
v_res_862_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_853_, v_as_854_, v_i_boxed_860_, v_stop_boxed_861_, v_b_857_, v___y_858_);
lean_dec(v___y_858_);
lean_dec_ref(v_as_854_);
lean_dec(v_multigoals_853_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_multigoals_863_, lean_object* v_as_864_, lean_object* v_i_865_, lean_object* v_stop_866_, lean_object* v_b_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
size_t v_i_boxed_870_; size_t v_stop_boxed_871_; lean_object* v_res_872_; 
v_i_boxed_870_ = lean_unbox_usize(v_i_865_);
lean_dec(v_i_865_);
v_stop_boxed_871_ = lean_unbox_usize(v_stop_866_);
lean_dec(v_stop_866_);
v_res_872_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___redArg(v_multigoals_863_, v_as_864_, v_i_boxed_870_, v_stop_boxed_871_, v_b_867_, v___y_868_);
lean_dec(v___y_868_);
lean_dec_ref(v_as_864_);
lean_dec(v_multigoals_863_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2___redArg___boxed(lean_object* v_multigoals_873_, lean_object* v_t_874_, lean_object* v___y_875_, lean_object* v___y_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2___redArg(v_multigoals_873_, v_t_874_, v___y_875_);
lean_dec(v___y_875_);
lean_dec_ref(v_t_874_);
lean_dec(v_multigoals_873_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_multigoals_878_, lean_object* v_x_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2___redArg(v_multigoals_878_, v_x_879_, v___y_880_);
lean_dec(v___y_880_);
lean_dec_ref(v_x_879_);
lean_dec(v_multigoals_878_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0___redArg___boxed(lean_object* v_multigoals_883_, lean_object* v_t_884_, lean_object* v_start_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0___redArg(v_multigoals_883_, v_t_884_, v_start_885_, v___y_886_);
lean_dec(v___y_886_);
lean_dec(v_start_885_);
lean_dec_ref(v_t_884_);
lean_dec(v_multigoals_883_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg___boxed(lean_object* v_multigoals_889_, lean_object* v_x_890_, lean_object* v_x_891_, lean_object* v_x_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
size_t v_x_7412__boxed_895_; size_t v_x_7413__boxed_896_; lean_object* v_res_897_; 
v_x_7412__boxed_895_ = lean_unbox_usize(v_x_891_);
lean_dec(v_x_891_);
v_x_7413__boxed_896_ = lean_unbox_usize(v_x_892_);
lean_dec(v_x_892_);
v_res_897_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg(v_multigoals_889_, v_x_890_, v_x_7412__boxed_895_, v_x_7413__boxed_896_, v___y_893_);
lean_dec(v___y_893_);
lean_dec_ref(v_x_890_);
lean_dec(v_multigoals_889_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___boxed(lean_object* v_multigoals_898_, lean_object* v_x_899_, lean_object* v_a_900_, lean_object* v_a_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg(v_multigoals_898_, v_x_899_, v_a_900_);
lean_dec(v_a_900_);
lean_dec(v_multigoals_898_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList(lean_object* v_multigoals_903_, lean_object* v_00_u03c9_904_, lean_object* v_trees_905_, lean_object* v_a_906_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___redArg(v_multigoals_903_, v_trees_905_, v_a_906_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___boxed(lean_object* v_multigoals_909_, lean_object* v_00_u03c9_910_, lean_object* v_trees_911_, lean_object* v_a_912_, lean_object* v_a_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList(v_multigoals_909_, v_00_u03c9_910_, v_trees_911_, v_a_912_);
lean_dec(v_a_912_);
lean_dec_ref(v_trees_911_);
lean_dec(v_multigoals_909_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics(lean_object* v_multigoals_915_, lean_object* v_00_u03c9_916_, lean_object* v_x_917_, lean_object* v_a_918_){
_start:
{
lean_object* v___x_920_; 
v___x_920_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg(v_multigoals_915_, v_x_917_, v_a_918_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___boxed(lean_object* v_multigoals_921_, lean_object* v_00_u03c9_922_, lean_object* v_x_923_, lean_object* v_a_924_, lean_object* v_a_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics(v_multigoals_921_, v_00_u03c9_922_, v_x_923_, v_a_924_);
lean_dec(v_a_924_);
lean_dec(v_multigoals_921_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0(lean_object* v_00_u03c9_927_, lean_object* v_multigoals_928_, lean_object* v_t_929_, lean_object* v_start_930_, lean_object* v___y_931_){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0___redArg(v_multigoals_928_, v_t_929_, v_start_930_, v___y_931_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0___boxed(lean_object* v_00_u03c9_934_, lean_object* v_multigoals_935_, lean_object* v_t_936_, lean_object* v_start_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0(v_00_u03c9_934_, v_multigoals_935_, v_t_936_, v_start_937_, v___y_938_);
lean_dec(v___y_938_);
lean_dec(v_start_937_);
lean_dec_ref(v_t_936_);
lean_dec(v_multigoals_935_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2(lean_object* v_00_u03b2_941_, lean_object* v_m_942_, lean_object* v_a_943_){
_start:
{
lean_object* v___x_944_; 
v___x_944_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2___redArg(v_m_942_, v_a_943_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2___boxed(lean_object* v_00_u03b2_945_, lean_object* v_m_946_, lean_object* v_a_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2(v_00_u03b2_945_, v_m_946_, v_a_947_);
lean_dec_ref(v_a_947_);
lean_dec_ref(v_m_946_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3(lean_object* v_00_u03b2_949_, lean_object* v_m_950_, lean_object* v_a_951_){
_start:
{
lean_object* v___x_952_; 
v___x_952_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3___redArg(v_m_950_, v_a_951_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3___boxed(lean_object* v_00_u03b2_953_, lean_object* v_m_954_, lean_object* v_a_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3(v_00_u03b2_953_, v_m_954_, v_a_955_);
lean_dec_ref(v_a_955_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4(lean_object* v_00_u03b2_957_, lean_object* v_m_958_, lean_object* v_a_959_, lean_object* v_b_960_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4___redArg(v_m_958_, v_a_959_, v_b_960_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0(lean_object* v_00_u03c9_962_, lean_object* v_multigoals_963_, lean_object* v_x_964_, size_t v_x_965_, size_t v_x_966_, lean_object* v___y_967_){
_start:
{
lean_object* v___x_969_; 
v___x_969_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg(v_multigoals_963_, v_x_964_, v_x_965_, v_x_966_, v___y_967_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___boxed(lean_object* v_00_u03c9_970_, lean_object* v_multigoals_971_, lean_object* v_x_972_, lean_object* v_x_973_, lean_object* v_x_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
size_t v_x_7871__boxed_977_; size_t v_x_7872__boxed_978_; lean_object* v_res_979_; 
v_x_7871__boxed_977_ = lean_unbox_usize(v_x_973_);
lean_dec(v_x_973_);
v_x_7872__boxed_978_ = lean_unbox_usize(v_x_974_);
lean_dec(v_x_974_);
v_res_979_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0(v_00_u03c9_970_, v_multigoals_971_, v_x_972_, v_x_7871__boxed_977_, v_x_7872__boxed_978_, v___y_975_);
lean_dec(v___y_975_);
lean_dec_ref(v_x_972_);
lean_dec(v_multigoals_971_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1(lean_object* v_00_u03c9_980_, lean_object* v_multigoals_981_, lean_object* v_as_982_, size_t v_i_983_, size_t v_stop_984_, lean_object* v_b_985_, lean_object* v___y_986_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_981_, v_as_982_, v_i_983_, v_stop_984_, v_b_985_, v___y_986_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___boxed(lean_object* v_00_u03c9_989_, lean_object* v_multigoals_990_, lean_object* v_as_991_, lean_object* v_i_992_, lean_object* v_stop_993_, lean_object* v_b_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
size_t v_i_boxed_997_; size_t v_stop_boxed_998_; lean_object* v_res_999_; 
v_i_boxed_997_ = lean_unbox_usize(v_i_992_);
lean_dec(v_i_992_);
v_stop_boxed_998_ = lean_unbox_usize(v_stop_993_);
lean_dec(v_stop_993_);
v_res_999_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1(v_00_u03c9_989_, v_multigoals_990_, v_as_991_, v_i_boxed_997_, v_stop_boxed_998_, v_b_994_, v___y_995_);
lean_dec(v___y_995_);
lean_dec_ref(v_as_991_);
lean_dec(v_multigoals_990_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2(lean_object* v_00_u03c9_1000_, lean_object* v_multigoals_1001_, lean_object* v_t_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2___redArg(v_multigoals_1001_, v_t_1002_, v___y_1003_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2___boxed(lean_object* v_00_u03c9_1006_, lean_object* v_multigoals_1007_, lean_object* v_t_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2(v_00_u03c9_1006_, v_multigoals_1007_, v_t_1008_, v___y_1009_);
lean_dec(v___y_1009_);
lean_dec_ref(v_t_1008_);
lean_dec(v_multigoals_1007_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5(lean_object* v_00_u03b2_1012_, lean_object* v_a_1013_, lean_object* v_x_1014_){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5___redArg(v_a_1013_, v_x_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1016_, lean_object* v_a_1017_, lean_object* v_x_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5(v_00_u03b2_1016_, v_a_1017_, v_x_1018_);
lean_dec(v_x_1018_);
lean_dec_ref(v_a_1017_);
return v_res_1019_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__7(lean_object* v_00_u03b2_1020_, lean_object* v_a_1021_, lean_object* v_x_1022_){
_start:
{
uint8_t v___x_1023_; 
v___x_1023_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__7___redArg(v_a_1021_, v_x_1022_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__7___boxed(lean_object* v_00_u03b2_1024_, lean_object* v_a_1025_, lean_object* v_x_1026_){
_start:
{
uint8_t v_res_1027_; lean_object* v_r_1028_; 
v_res_1027_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__7(v_00_u03b2_1024_, v_a_1025_, v_x_1026_);
lean_dec(v_x_1026_);
lean_dec_ref(v_a_1025_);
v_r_1028_ = lean_box(v_res_1027_);
return v_r_1028_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__8(lean_object* v_00_u03b2_1029_, lean_object* v_a_1030_, lean_object* v_x_1031_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__8___redArg(v_a_1030_, v_x_1031_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__8___boxed(lean_object* v_00_u03b2_1033_, lean_object* v_a_1034_, lean_object* v_x_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__8(v_00_u03b2_1033_, v_a_1034_, v_x_1035_);
lean_dec_ref(v_a_1034_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10(lean_object* v_00_u03b2_1037_, lean_object* v_data_1038_){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10___redArg(v_data_1038_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__11(lean_object* v_00_u03b2_1040_, lean_object* v_a_1041_, lean_object* v_b_1042_, lean_object* v_x_1043_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__11___redArg(v_a_1041_, v_b_1042_, v_x_1043_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2(lean_object* v_00_u03c9_1045_, lean_object* v_multigoals_1046_, lean_object* v_x_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2___redArg(v_multigoals_1046_, v_x_1047_, v___y_1048_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03c9_1051_, lean_object* v_multigoals_1052_, lean_object* v_x_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2(v_00_u03c9_1051_, v_multigoals_1052_, v_x_1053_, v___y_1054_);
lean_dec(v___y_1054_);
lean_dec_ref(v_x_1053_);
lean_dec(v_multigoals_1052_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3(lean_object* v_00_u03c9_1057_, lean_object* v_multigoals_1058_, lean_object* v_as_1059_, size_t v_i_1060_, size_t v_stop_1061_, lean_object* v_b_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___redArg(v_multigoals_1058_, v_as_1059_, v_i_1060_, v_stop_1061_, v_b_1062_, v___y_1063_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03c9_1066_, lean_object* v_multigoals_1067_, lean_object* v_as_1068_, lean_object* v_i_1069_, lean_object* v_stop_1070_, lean_object* v_b_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
size_t v_i_boxed_1074_; size_t v_stop_boxed_1075_; lean_object* v_res_1076_; 
v_i_boxed_1074_ = lean_unbox_usize(v_i_1069_);
lean_dec(v_i_1069_);
v_stop_boxed_1075_ = lean_unbox_usize(v_stop_1070_);
lean_dec(v_stop_1070_);
v_res_1076_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3(v_00_u03c9_1066_, v_multigoals_1067_, v_as_1068_, v_i_boxed_1074_, v_stop_boxed_1075_, v_b_1071_, v___y_1072_);
lean_dec(v___y_1072_);
lean_dec_ref(v_as_1068_);
lean_dec(v_multigoals_1067_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10_spec__13(lean_object* v_00_u03b2_1077_, lean_object* v_i_1078_, lean_object* v_source_1079_, lean_object* v_target_1080_){
_start:
{
lean_object* v___x_1081_; 
v___x_1081_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10_spec__13___redArg(v_i_1078_, v_source_1079_, v_target_1080_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10_spec__13_spec__14(lean_object* v_00_u03b2_1082_, lean_object* v_x_1083_, lean_object* v_x_1084_){
_start:
{
lean_object* v___x_1085_; 
v___x_1085_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10_spec__13_spec__14___redArg(v_x_1083_, v_x_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__0(lean_object* v_a_1086_){
_start:
{
lean_object* v___x_1087_; 
v___x_1087_ = lean_nat_to_int(v_a_1086_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3___redArg(lean_object* v___y_1088_){
_start:
{
lean_object* v___x_1090_; lean_object* v_infoState_1091_; lean_object* v_trees_1092_; lean_object* v___x_1093_; 
v___x_1090_ = lean_st_ref_get(v___y_1088_);
v_infoState_1091_ = lean_ctor_get(v___x_1090_, 8);
lean_inc_ref(v_infoState_1091_);
lean_dec(v___x_1090_);
v_trees_1092_ = lean_ctor_get(v_infoState_1091_, 2);
lean_inc_ref(v_trees_1092_);
lean_dec_ref(v_infoState_1091_);
v___x_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1093_, 0, v_trees_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3___redArg___boxed(lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3___redArg(v___y_1094_);
lean_dec(v___y_1094_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3(lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v___x_1100_; 
v___x_1100_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3___redArg(v___y_1098_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3___boxed(lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3(v___y_1101_, v___y_1102_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
return v_res_1104_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1105_ = lean_box(0);
v___x_1106_ = lean_unsigned_to_nat(16u);
v___x_1107_ = lean_mk_array(v___x_1106_, v___x_1105_);
return v___x_1107_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1108_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__0, &l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__0_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__0);
v___x_1109_ = lean_unsigned_to_nat(0u);
v___x_1110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1109_);
lean_ctor_set(v___x_1110_, 1, v___x_1108_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0(lean_object* v_stx_1111_, lean_object* v_val_1112_, lean_object* v_a_1113_, lean_object* v_x_1114_){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1116_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__1, &l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__1_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__1);
v___x_1117_ = lean_st_mk_ref(v___x_1116_);
v___x_1118_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg(v_stx_1111_, v___x_1117_);
v___x_1119_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___redArg(v_val_1112_, v_a_1113_, v___x_1117_);
v___x_1120_ = lean_st_ref_get(v___x_1117_);
lean_dec(v___x_1117_);
v___x_1121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1119_);
lean_ctor_set(v___x_1121_, 1, v___x_1120_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___boxed(lean_object* v_stx_1122_, lean_object* v_val_1123_, lean_object* v_a_1124_, lean_object* v_x_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0(v_stx_1122_, v_val_1123_, v_a_1124_, v_x_1125_);
lean_dec_ref(v_a_1124_);
lean_dec(v_val_1123_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1___redArg(lean_object* v_o_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v_env_1133_; lean_object* v___x_1134_; lean_object* v_toEnvExtension_1135_; lean_object* v_asyncMode_1136_; lean_object* v___x_1137_; uint8_t v___x_1138_; lean_object* v___x_1139_; lean_object* v_merged_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1148_; 
v___x_1131_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_1132_ = lean_st_ref_get(v___y_1129_);
v_env_1133_ = lean_ctor_get(v___x_1132_, 0);
lean_inc_ref(v_env_1133_);
lean_dec(v___x_1132_);
v___x_1134_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_1135_ = lean_ctor_get(v___x_1134_, 0);
v_asyncMode_1136_ = lean_ctor_get(v_toEnvExtension_1135_, 2);
v___x_1137_ = lean_box(0);
v___x_1138_ = 0;
v___x_1139_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1131_, v___x_1134_, v_env_1133_, v_asyncMode_1136_, v___x_1137_, v___x_1138_);
v_merged_1140_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1148_ == 0)
{
lean_object* v_unused_1149_; 
v_unused_1149_ = lean_ctor_get(v___x_1139_, 1);
lean_dec(v_unused_1149_);
v___x_1142_ = v___x_1139_;
v_isShared_1143_ = v_isSharedCheck_1148_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_merged_1140_);
lean_dec(v___x_1139_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1148_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 1, v_merged_1140_);
lean_ctor_set(v___x_1142_, 0, v_o_1128_);
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_o_1128_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v_merged_1140_);
v___x_1145_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
lean_object* v___x_1146_; 
v___x_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1145_);
return v___x_1146_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1___redArg___boxed(lean_object* v_o_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1___redArg(v_o_1150_, v___y_1151_);
lean_dec(v___y_1151_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1(lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v_scopes_1159_; lean_object* v___x_1160_; lean_object* v_opts_1161_; lean_object* v___x_1162_; 
v___x_1157_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1158_ = lean_st_ref_get(v___y_1155_);
v_scopes_1159_ = lean_ctor_get(v___x_1158_, 2);
lean_inc(v_scopes_1159_);
lean_dec(v___x_1158_);
v___x_1160_ = l_List_head_x21___redArg(v___x_1157_, v_scopes_1159_);
lean_dec(v_scopes_1159_);
v_opts_1161_ = lean_ctor_get(v___x_1160_, 1);
lean_inc_ref(v_opts_1161_);
lean_dec(v___x_1160_);
v___x_1162_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1___redArg(v_opts_1161_, v___y_1155_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1___boxed(lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1(v___y_1163_, v___y_1164_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
return v_res_1166_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___lam__0(uint8_t v_suppressElabErrors_1168_, uint8_t v___y_1169_, lean_object* v_x_1170_){
_start:
{
if (lean_obj_tag(v_x_1170_) == 1)
{
lean_object* v_pre_1171_; 
v_pre_1171_ = lean_ctor_get(v_x_1170_, 0);
if (lean_obj_tag(v_pre_1171_) == 0)
{
lean_object* v_str_1172_; lean_object* v___x_1173_; uint8_t v___x_1174_; 
v_str_1172_ = lean_ctor_get(v_x_1170_, 1);
v___x_1173_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___lam__0___closed__0));
v___x_1174_ = lean_string_dec_eq(v_str_1172_, v___x_1173_);
if (v___x_1174_ == 0)
{
return v___x_1174_;
}
else
{
return v_suppressElabErrors_1168_;
}
}
else
{
return v___y_1169_;
}
}
else
{
return v___y_1169_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___lam__0___boxed(lean_object* v_suppressElabErrors_1175_, lean_object* v___y_1176_, lean_object* v_x_1177_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1178_; uint8_t v___y_7632__boxed_1179_; uint8_t v_res_1180_; lean_object* v_r_1181_; 
v_suppressElabErrors_boxed_1178_ = lean_unbox(v_suppressElabErrors_1175_);
v___y_7632__boxed_1179_ = lean_unbox(v___y_1176_);
v_res_1180_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___lam__0(v_suppressElabErrors_boxed_1178_, v___y_7632__boxed_1179_, v_x_1177_);
lean_dec(v_x_1177_);
v_r_1181_ = lean_box(v_res_1180_);
return v_r_1181_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__13(lean_object* v_opts_1182_, lean_object* v_opt_1183_){
_start:
{
lean_object* v_name_1184_; lean_object* v_defValue_1185_; lean_object* v_map_1186_; lean_object* v___x_1187_; 
v_name_1184_ = lean_ctor_get(v_opt_1183_, 0);
v_defValue_1185_ = lean_ctor_get(v_opt_1183_, 1);
v_map_1186_ = lean_ctor_get(v_opts_1182_, 0);
v___x_1187_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1186_, v_name_1184_);
if (lean_obj_tag(v___x_1187_) == 0)
{
uint8_t v___x_1188_; 
v___x_1188_ = lean_unbox(v_defValue_1185_);
return v___x_1188_;
}
else
{
lean_object* v_val_1189_; 
v_val_1189_ = lean_ctor_get(v___x_1187_, 0);
lean_inc(v_val_1189_);
lean_dec_ref_known(v___x_1187_, 1);
if (lean_obj_tag(v_val_1189_) == 1)
{
uint8_t v_v_1190_; 
v_v_1190_ = lean_ctor_get_uint8(v_val_1189_, 0);
lean_dec_ref_known(v_val_1189_, 0);
return v_v_1190_;
}
else
{
uint8_t v___x_1191_; 
lean_dec(v_val_1189_);
v___x_1191_ = lean_unbox(v_defValue_1185_);
return v___x_1191_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__13___boxed(lean_object* v_opts_1192_, lean_object* v_opt_1193_){
_start:
{
uint8_t v_res_1194_; lean_object* v_r_1195_; 
v_res_1194_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__13(v_opts_1192_, v_opt_1193_);
lean_dec_ref(v_opt_1193_);
lean_dec_ref(v_opts_1192_);
v_r_1195_ = lean_box(v_res_1194_);
return v_r_1195_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1196_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1197_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__0);
v___x_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1197_);
return v___x_1198_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1199_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1200_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__1);
v___x_1201_ = lean_unsigned_to_nat(0u);
v___x_1202_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1201_);
lean_ctor_set(v___x_1202_, 1, v___x_1201_);
lean_ctor_set(v___x_1202_, 2, v___x_1201_);
lean_ctor_set(v___x_1202_, 3, v___x_1201_);
lean_ctor_set(v___x_1202_, 4, v___x_1200_);
lean_ctor_set(v___x_1202_, 5, v___x_1200_);
lean_ctor_set(v___x_1202_, 6, v___x_1200_);
lean_ctor_set(v___x_1202_, 7, v___x_1200_);
lean_ctor_set(v___x_1202_, 8, v___x_1200_);
lean_ctor_set(v___x_1202_, 9, v___x_1200_);
lean_ctor_set(v___x_1202_, 10, v___x_1200_);
lean_ctor_set(v___x_1202_, 11, v___x_1199_);
return v___x_1202_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__3(void){
_start:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1203_ = lean_unsigned_to_nat(32u);
v___x_1204_ = lean_mk_empty_array_with_capacity(v___x_1203_);
v___x_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1204_);
return v___x_1205_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__4(void){
_start:
{
size_t v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1206_ = ((size_t)5ULL);
v___x_1207_ = lean_unsigned_to_nat(0u);
v___x_1208_ = lean_unsigned_to_nat(32u);
v___x_1209_ = lean_mk_empty_array_with_capacity(v___x_1208_);
v___x_1210_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__3);
v___x_1211_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
lean_ctor_set(v___x_1211_, 1, v___x_1209_);
lean_ctor_set(v___x_1211_, 2, v___x_1207_);
lean_ctor_set(v___x_1211_, 3, v___x_1207_);
lean_ctor_set_usize(v___x_1211_, 4, v___x_1206_);
return v___x_1211_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__5(void){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1212_ = lean_box(1);
v___x_1213_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__4);
v___x_1214_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__1);
v___x_1215_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1214_);
lean_ctor_set(v___x_1215_, 1, v___x_1213_);
lean_ctor_set(v___x_1215_, 2, v___x_1212_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg(lean_object* v_msgData_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v___x_1219_; lean_object* v_env_1220_; uint8_t v___x_1221_; lean_object* v_env_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v_scopes_1225_; lean_object* v___x_1226_; lean_object* v_opts_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1219_ = lean_st_ref_get(v___y_1217_);
v_env_1220_ = lean_ctor_get(v___x_1219_, 0);
lean_inc_ref(v_env_1220_);
lean_dec(v___x_1219_);
v___x_1221_ = 0;
v_env_1222_ = l_Lean_Environment_setRecordingDeps(v_env_1220_, v___x_1221_);
v___x_1223_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1224_ = lean_st_ref_get(v___y_1217_);
v_scopes_1225_ = lean_ctor_get(v___x_1224_, 2);
lean_inc(v_scopes_1225_);
lean_dec(v___x_1224_);
v___x_1226_ = l_List_head_x21___redArg(v___x_1223_, v_scopes_1225_);
lean_dec(v_scopes_1225_);
v_opts_1227_ = lean_ctor_get(v___x_1226_, 1);
lean_inc_ref(v_opts_1227_);
lean_dec(v___x_1226_);
v___x_1228_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__2);
v___x_1229_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__5);
v___x_1230_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1230_, 0, v_env_1222_);
lean_ctor_set(v___x_1230_, 1, v___x_1228_);
lean_ctor_set(v___x_1230_, 2, v___x_1229_);
lean_ctor_set(v___x_1230_, 3, v_opts_1227_);
v___x_1231_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1230_);
lean_ctor_set(v___x_1231_, 1, v_msgData_1216_);
v___x_1232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1231_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___boxed(lean_object* v_msgData_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg(v_msgData_1233_, v___y_1234_);
lean_dec(v___y_1234_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10(lean_object* v_ref_1238_, lean_object* v_msgData_1239_, uint8_t v_severity_1240_, uint8_t v_isSilent_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v___y_1246_; uint8_t v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; uint8_t v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; uint8_t v___y_1311_; lean_object* v___y_1312_; uint8_t v___y_1313_; uint8_t v___y_1314_; lean_object* v___y_1315_; uint8_t v___y_1339_; lean_object* v___y_1340_; uint8_t v___y_1341_; uint8_t v___y_1342_; lean_object* v___y_1343_; uint8_t v___y_1347_; uint8_t v___y_1348_; uint8_t v___y_1349_; uint8_t v___x_1364_; uint8_t v___y_1366_; uint8_t v___y_1367_; uint8_t v___y_1368_; uint8_t v___y_1370_; uint8_t v___x_1382_; 
v___x_1364_ = 2;
v___x_1382_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1240_, v___x_1364_);
if (v___x_1382_ == 0)
{
v___y_1370_ = v___x_1382_;
goto v___jp_1369_;
}
else
{
uint8_t v___x_1383_; 
lean_inc_ref(v_msgData_1239_);
v___x_1383_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1239_);
v___y_1370_ = v___x_1383_;
goto v___jp_1369_;
}
v___jp_1245_:
{
lean_object* v___x_1254_; 
v___x_1254_ = l_Lean_Elab_Command_getScope___redArg(v___y_1253_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v_a_1255_; lean_object* v_currNamespace_1256_; lean_object* v___x_1257_; 
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
lean_inc(v_a_1255_);
lean_dec_ref_known(v___x_1254_, 1);
v_currNamespace_1256_ = lean_ctor_get(v_a_1255_, 2);
lean_inc(v_currNamespace_1256_);
lean_dec(v_a_1255_);
v___x_1257_ = l_Lean_Elab_Command_getScope___redArg(v___y_1253_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v_a_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1293_; 
v_a_1258_ = lean_ctor_get(v___x_1257_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1260_ = v___x_1257_;
v_isShared_1261_ = v_isSharedCheck_1293_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_a_1258_);
lean_dec(v___x_1257_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1293_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v_openDecls_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v_env_1267_; lean_object* v_messages_1268_; lean_object* v_scopes_1269_; lean_object* v_usedQuotCtxts_1270_; lean_object* v_nextMacroScope_1271_; lean_object* v_maxRecDepth_1272_; lean_object* v_ngen_1273_; lean_object* v_auxDeclNGen_1274_; lean_object* v_infoState_1275_; lean_object* v_traceState_1276_; lean_object* v_snapshotTasks_1277_; lean_object* v_prevLinterStates_1278_; lean_object* v_codeQualityEntryTasks_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1292_; 
v_openDecls_1262_ = lean_ctor_get(v_a_1258_, 3);
lean_inc(v_openDecls_1262_);
lean_dec(v_a_1258_);
v___x_1263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1263_, 0, v_currNamespace_1256_);
lean_ctor_set(v___x_1263_, 1, v_openDecls_1262_);
v___x_1264_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1263_);
lean_ctor_set(v___x_1264_, 1, v___y_1248_);
lean_inc_ref(v___y_1249_);
lean_inc_ref(v___y_1246_);
v___x_1265_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1265_, 0, v___y_1246_);
lean_ctor_set(v___x_1265_, 1, v___y_1252_);
lean_ctor_set(v___x_1265_, 2, v___y_1250_);
lean_ctor_set(v___x_1265_, 3, v___y_1249_);
lean_ctor_set(v___x_1265_, 4, v___x_1264_);
lean_ctor_set_uint8(v___x_1265_, sizeof(void*)*5, v___y_1251_);
lean_ctor_set_uint8(v___x_1265_, sizeof(void*)*5 + 1, v___y_1247_);
lean_ctor_set_uint8(v___x_1265_, sizeof(void*)*5 + 2, v_isSilent_1241_);
v___x_1266_ = lean_st_ref_take(v___y_1253_);
v_env_1267_ = lean_ctor_get(v___x_1266_, 0);
v_messages_1268_ = lean_ctor_get(v___x_1266_, 1);
v_scopes_1269_ = lean_ctor_get(v___x_1266_, 2);
v_usedQuotCtxts_1270_ = lean_ctor_get(v___x_1266_, 3);
v_nextMacroScope_1271_ = lean_ctor_get(v___x_1266_, 4);
v_maxRecDepth_1272_ = lean_ctor_get(v___x_1266_, 5);
v_ngen_1273_ = lean_ctor_get(v___x_1266_, 6);
v_auxDeclNGen_1274_ = lean_ctor_get(v___x_1266_, 7);
v_infoState_1275_ = lean_ctor_get(v___x_1266_, 8);
v_traceState_1276_ = lean_ctor_get(v___x_1266_, 9);
v_snapshotTasks_1277_ = lean_ctor_get(v___x_1266_, 10);
v_prevLinterStates_1278_ = lean_ctor_get(v___x_1266_, 11);
v_codeQualityEntryTasks_1279_ = lean_ctor_get(v___x_1266_, 12);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1281_ = v___x_1266_;
v_isShared_1282_ = v_isSharedCheck_1292_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1279_);
lean_inc(v_prevLinterStates_1278_);
lean_inc(v_snapshotTasks_1277_);
lean_inc(v_traceState_1276_);
lean_inc(v_infoState_1275_);
lean_inc(v_auxDeclNGen_1274_);
lean_inc(v_ngen_1273_);
lean_inc(v_maxRecDepth_1272_);
lean_inc(v_nextMacroScope_1271_);
lean_inc(v_usedQuotCtxts_1270_);
lean_inc(v_scopes_1269_);
lean_inc(v_messages_1268_);
lean_inc(v_env_1267_);
lean_dec(v___x_1266_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1292_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1286_; 
v___x_1283_ = lean_box(0);
v___x_1284_ = l_Lean_MessageLog_add(v___x_1265_, v_messages_1268_);
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 1, v___x_1284_);
v___x_1286_ = v___x_1281_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_env_1267_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v___x_1284_);
lean_ctor_set(v_reuseFailAlloc_1291_, 2, v_scopes_1269_);
lean_ctor_set(v_reuseFailAlloc_1291_, 3, v_usedQuotCtxts_1270_);
lean_ctor_set(v_reuseFailAlloc_1291_, 4, v_nextMacroScope_1271_);
lean_ctor_set(v_reuseFailAlloc_1291_, 5, v_maxRecDepth_1272_);
lean_ctor_set(v_reuseFailAlloc_1291_, 6, v_ngen_1273_);
lean_ctor_set(v_reuseFailAlloc_1291_, 7, v_auxDeclNGen_1274_);
lean_ctor_set(v_reuseFailAlloc_1291_, 8, v_infoState_1275_);
lean_ctor_set(v_reuseFailAlloc_1291_, 9, v_traceState_1276_);
lean_ctor_set(v_reuseFailAlloc_1291_, 10, v_snapshotTasks_1277_);
lean_ctor_set(v_reuseFailAlloc_1291_, 11, v_prevLinterStates_1278_);
lean_ctor_set(v_reuseFailAlloc_1291_, 12, v_codeQualityEntryTasks_1279_);
v___x_1286_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
lean_object* v___x_1287_; lean_object* v___x_1289_; 
v___x_1287_ = lean_st_ref_put(v___y_1253_, v___x_1286_);
if (v_isShared_1261_ == 0)
{
lean_ctor_set(v___x_1260_, 0, v___x_1283_);
v___x_1289_ = v___x_1260_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1283_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
lean_dec(v_currNamespace_1256_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1248_);
v_a_1294_ = lean_ctor_get(v___x_1257_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1296_ = v___x_1257_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1257_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1294_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
else
{
lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1309_; 
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1248_);
v_a_1302_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1309_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1304_ = v___x_1254_;
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_dec(v___x_1254_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1307_; 
if (v_isShared_1305_ == 0)
{
v___x_1307_ = v___x_1304_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_a_1302_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
}
}
v___jp_1310_:
{
lean_object* v_fileName_1316_; lean_object* v_fileMap_1317_; uint8_t v_suppressElabErrors_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___f_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1337_; 
v_fileName_1316_ = lean_ctor_get(v___y_1242_, 0);
v_fileMap_1317_ = lean_ctor_get(v___y_1242_, 1);
v_suppressElabErrors_1318_ = lean_ctor_get_uint8(v___y_1242_, sizeof(void*)*10);
v___x_1319_ = lean_box(v_suppressElabErrors_1318_);
v___x_1320_ = lean_box(v___y_1311_);
v___f_1321_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1321_, 0, v___x_1319_);
lean_closure_set(v___f_1321_, 1, v___x_1320_);
v___x_1322_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1239_);
v___x_1323_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg(v___x_1322_, v___y_1243_);
v_a_1324_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1326_ = v___x_1323_;
v_isShared_1327_ = v_isSharedCheck_1337_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v___x_1323_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1337_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
lean_inc_ref_n(v_fileMap_1317_, 2);
v___x_1328_ = l_Lean_FileMap_toPosition(v_fileMap_1317_, v___y_1312_);
lean_dec(v___y_1312_);
v___x_1329_ = l_Lean_FileMap_toPosition(v_fileMap_1317_, v___y_1315_);
lean_dec(v___y_1315_);
v___x_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1329_);
v___x_1331_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___closed__0));
if (v_suppressElabErrors_1318_ == 0)
{
lean_del_object(v___x_1326_);
lean_dec_ref(v___f_1321_);
v___y_1246_ = v_fileName_1316_;
v___y_1247_ = v___y_1313_;
v___y_1248_ = v_a_1324_;
v___y_1249_ = v___x_1331_;
v___y_1250_ = v___x_1330_;
v___y_1251_ = v___y_1314_;
v___y_1252_ = v___x_1328_;
v___y_1253_ = v___y_1243_;
goto v___jp_1245_;
}
else
{
uint8_t v___x_1332_; 
lean_inc(v_a_1324_);
v___x_1332_ = l_Lean_MessageData_hasTag(v___f_1321_, v_a_1324_);
if (v___x_1332_ == 0)
{
lean_object* v___x_1333_; lean_object* v___x_1335_; 
lean_dec_ref_known(v___x_1330_, 1);
lean_dec_ref(v___x_1328_);
lean_dec(v_a_1324_);
v___x_1333_ = lean_box(0);
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 0, v___x_1333_);
v___x_1335_ = v___x_1326_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1333_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
else
{
lean_del_object(v___x_1326_);
v___y_1246_ = v_fileName_1316_;
v___y_1247_ = v___y_1313_;
v___y_1248_ = v_a_1324_;
v___y_1249_ = v___x_1331_;
v___y_1250_ = v___x_1330_;
v___y_1251_ = v___y_1314_;
v___y_1252_ = v___x_1328_;
v___y_1253_ = v___y_1243_;
goto v___jp_1245_;
}
}
}
}
v___jp_1338_:
{
lean_object* v___x_1344_; 
v___x_1344_ = l_Lean_Syntax_getTailPos_x3f(v___y_1340_, v___y_1342_);
lean_dec(v___y_1340_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_inc(v___y_1343_);
v___y_1311_ = v___y_1339_;
v___y_1312_ = v___y_1343_;
v___y_1313_ = v___y_1341_;
v___y_1314_ = v___y_1342_;
v___y_1315_ = v___y_1343_;
goto v___jp_1310_;
}
else
{
lean_object* v_val_1345_; 
v_val_1345_ = lean_ctor_get(v___x_1344_, 0);
lean_inc(v_val_1345_);
lean_dec_ref_known(v___x_1344_, 1);
v___y_1311_ = v___y_1339_;
v___y_1312_ = v___y_1343_;
v___y_1313_ = v___y_1341_;
v___y_1314_ = v___y_1342_;
v___y_1315_ = v_val_1345_;
goto v___jp_1310_;
}
}
v___jp_1346_:
{
lean_object* v___x_1350_; 
v___x_1350_ = l_Lean_Elab_Command_getRef___redArg(v___y_1242_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v_a_1351_; lean_object* v_ref_1352_; lean_object* v___x_1353_; 
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
lean_inc(v_a_1351_);
lean_dec_ref_known(v___x_1350_, 1);
v_ref_1352_ = l_Lean_replaceRef(v_ref_1238_, v_a_1351_);
lean_dec(v_a_1351_);
v___x_1353_ = l_Lean_Syntax_getPos_x3f(v_ref_1352_, v___y_1348_);
if (lean_obj_tag(v___x_1353_) == 0)
{
lean_object* v___x_1354_; 
v___x_1354_ = lean_unsigned_to_nat(0u);
v___y_1339_ = v___y_1347_;
v___y_1340_ = v_ref_1352_;
v___y_1341_ = v___y_1349_;
v___y_1342_ = v___y_1348_;
v___y_1343_ = v___x_1354_;
goto v___jp_1338_;
}
else
{
lean_object* v_val_1355_; 
v_val_1355_ = lean_ctor_get(v___x_1353_, 0);
lean_inc(v_val_1355_);
lean_dec_ref_known(v___x_1353_, 1);
v___y_1339_ = v___y_1347_;
v___y_1340_ = v_ref_1352_;
v___y_1341_ = v___y_1349_;
v___y_1342_ = v___y_1348_;
v___y_1343_ = v_val_1355_;
goto v___jp_1338_;
}
}
else
{
lean_object* v_a_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1363_; 
lean_dec_ref(v_msgData_1239_);
v_a_1356_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1358_ = v___x_1350_;
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_a_1356_);
lean_dec(v___x_1350_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1361_; 
if (v_isShared_1359_ == 0)
{
v___x_1361_ = v___x_1358_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1356_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
}
v___jp_1365_:
{
if (v___y_1368_ == 0)
{
v___y_1347_ = v___y_1366_;
v___y_1348_ = v___y_1367_;
v___y_1349_ = v_severity_1240_;
goto v___jp_1346_;
}
else
{
v___y_1347_ = v___y_1366_;
v___y_1348_ = v___y_1367_;
v___y_1349_ = v___x_1364_;
goto v___jp_1346_;
}
}
v___jp_1369_:
{
if (v___y_1370_ == 0)
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v_scopes_1373_; lean_object* v___x_1374_; lean_object* v_opts_1375_; uint8_t v___x_1376_; uint8_t v___x_1377_; 
v___x_1371_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1372_ = lean_st_ref_get(v___y_1243_);
v_scopes_1373_ = lean_ctor_get(v___x_1372_, 2);
lean_inc(v_scopes_1373_);
lean_dec(v___x_1372_);
v___x_1374_ = l_List_head_x21___redArg(v___x_1371_, v_scopes_1373_);
lean_dec(v_scopes_1373_);
v_opts_1375_ = lean_ctor_get(v___x_1374_, 1);
lean_inc_ref(v_opts_1375_);
lean_dec(v___x_1374_);
v___x_1376_ = 1;
v___x_1377_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1240_, v___x_1376_);
if (v___x_1377_ == 0)
{
lean_dec_ref(v_opts_1375_);
v___y_1366_ = v___y_1370_;
v___y_1367_ = v___y_1370_;
v___y_1368_ = v___x_1377_;
goto v___jp_1365_;
}
else
{
lean_object* v___x_1378_; uint8_t v___x_1379_; 
v___x_1378_ = l_Lean_warningAsError;
v___x_1379_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__13(v_opts_1375_, v___x_1378_);
lean_dec_ref(v_opts_1375_);
v___y_1366_ = v___y_1370_;
v___y_1367_ = v___y_1370_;
v___y_1368_ = v___x_1379_;
goto v___jp_1365_;
}
}
else
{
lean_object* v___x_1380_; lean_object* v___x_1381_; 
lean_dec_ref(v_msgData_1239_);
v___x_1380_ = lean_box(0);
v___x_1381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1380_);
return v___x_1381_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___boxed(lean_object* v_ref_1384_, lean_object* v_msgData_1385_, lean_object* v_severity_1386_, lean_object* v_isSilent_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
uint8_t v_severity_boxed_1391_; uint8_t v_isSilent_boxed_1392_; lean_object* v_res_1393_; 
v_severity_boxed_1391_ = lean_unbox(v_severity_1386_);
v_isSilent_boxed_1392_ = lean_unbox(v_isSilent_1387_);
v_res_1393_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10(v_ref_1384_, v_msgData_1385_, v_severity_boxed_1391_, v_isSilent_boxed_1392_, v___y_1388_, v___y_1389_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec(v_ref_1384_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5(lean_object* v_ref_1394_, lean_object* v_msgData_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
uint8_t v___x_1399_; uint8_t v___x_1400_; lean_object* v___x_1401_; 
v___x_1399_ = 1;
v___x_1400_ = 0;
v___x_1401_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10(v_ref_1394_, v_msgData_1395_, v___x_1399_, v___x_1400_, v___y_1396_, v___y_1397_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5___boxed(lean_object* v_ref_1402_, lean_object* v_msgData_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5(v_ref_1402_, v_msgData_1403_, v___y_1404_, v___y_1405_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
lean_dec(v_ref_1402_);
return v_res_1407_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1409_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__0));
v___x_1410_ = l_Lean_stringToMessageData(v___x_1409_);
return v___x_1410_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1412_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__2));
v___x_1413_ = l_Lean_stringToMessageData(v___x_1412_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3(lean_object* v_linterOption_1414_, lean_object* v_stx_1415_, lean_object* v_msg_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
lean_object* v_name_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1438_; 
v_name_1420_ = lean_ctor_get(v_linterOption_1414_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v_linterOption_1414_);
if (v_isSharedCheck_1438_ == 0)
{
lean_object* v_unused_1439_; 
v_unused_1439_ = lean_ctor_get(v_linterOption_1414_, 1);
lean_dec(v_unused_1439_);
v___x_1422_ = v_linterOption_1414_;
v_isShared_1423_ = v_isSharedCheck_1438_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_name_1420_);
lean_dec(v_linterOption_1414_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1438_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1427_; 
v___x_1424_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__1);
lean_inc(v_name_1420_);
v___x_1425_ = l_Lean_MessageData_ofName(v_name_1420_);
if (v_isShared_1423_ == 0)
{
lean_ctor_set_tag(v___x_1422_, 7);
lean_ctor_set(v___x_1422_, 1, v___x_1425_);
lean_ctor_set(v___x_1422_, 0, v___x_1424_);
v___x_1427_ = v___x_1422_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1424_);
lean_ctor_set(v_reuseFailAlloc_1437_, 1, v___x_1425_);
v___x_1427_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v_disable_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1428_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__3);
v___x_1429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1427_);
lean_ctor_set(v___x_1429_, 1, v___x_1428_);
v_disable_1430_ = l_Lean_MessageData_note(v___x_1429_);
v___x_1431_ = l_Lean_Linter_linterMessageTag;
v___x_1432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1432_, 0, v_msg_1416_);
lean_ctor_set(v___x_1432_, 1, v_disable_1430_);
v___x_1433_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1431_);
lean_ctor_set(v___x_1433_, 1, v___x_1432_);
v___x_1434_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1434_, 0, v_name_1420_);
lean_ctor_set(v___x_1434_, 1, v___x_1433_);
lean_inc(v_stx_1415_);
v___x_1435_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_1435_, 0, v_stx_1415_);
lean_ctor_set(v___x_1435_, 1, v___x_1434_);
v___x_1436_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5(v_stx_1415_, v___x_1435_, v___y_1417_, v___y_1418_);
lean_dec(v_stx_1415_);
return v___x_1436_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___boxed(lean_object* v_linterOption_1440_, lean_object* v_stx_1441_, lean_object* v_msg_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3(v_linterOption_1440_, v_stx_1441_, v_msg_1442_, v___y_1443_, v___y_1444_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2(lean_object* v_linterOption_1447_, lean_object* v_stx_1448_, lean_object* v_msg_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v___x_1453_; lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1464_; 
v___x_1453_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1(v___y_1450_, v___y_1451_);
v_a_1454_ = lean_ctor_get(v___x_1453_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1456_ = v___x_1453_;
v_isShared_1457_ = v_isSharedCheck_1464_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___x_1453_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1464_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
uint8_t v___x_1458_; 
v___x_1458_ = l_Lean_Linter_getLinterValue(v_linterOption_1447_, v_a_1454_);
lean_dec(v_a_1454_);
if (v___x_1458_ == 0)
{
lean_object* v___x_1459_; lean_object* v___x_1461_; 
lean_dec_ref(v_msg_1449_);
lean_dec(v_stx_1448_);
lean_dec_ref(v_linterOption_1447_);
v___x_1459_ = lean_box(0);
if (v_isShared_1457_ == 0)
{
lean_ctor_set(v___x_1456_, 0, v___x_1459_);
v___x_1461_ = v___x_1456_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v___x_1459_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
else
{
lean_object* v___x_1463_; 
lean_del_object(v___x_1456_);
v___x_1463_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3(v_linterOption_1447_, v_stx_1448_, v_msg_1449_, v___y_1450_, v___y_1451_);
return v___x_1463_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2___boxed(lean_object* v_linterOption_1465_, lean_object* v_stx_1466_, lean_object* v_msg_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2(v_linterOption_1465_, v_stx_1466_, v_msg_1467_, v___y_1468_, v___y_1469_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
return v_res_1471_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__2(void){
_start:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1475_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__1));
v___x_1476_ = l_Lean_MessageData_ofFormat(v___x_1475_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4(lean_object* v_as_1477_, size_t v_sz_1478_, size_t v_i_1479_, lean_object* v_b_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
lean_object* v_a_1485_; uint8_t v___x_1489_; 
v___x_1489_ = lean_usize_dec_lt(v_i_1479_, v_sz_1478_);
if (v___x_1489_ == 0)
{
lean_object* v___x_1490_; 
v___x_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1490_, 0, v_b_1480_);
return v___x_1490_;
}
else
{
lean_object* v_a_1491_; lean_object* v_fst_1492_; lean_object* v_snd_1493_; lean_object* v_start_1494_; lean_object* v_stop_1495_; lean_object* v_start_1496_; lean_object* v_stop_1497_; lean_object* v___x_1498_; uint8_t v___y_1500_; uint8_t v___x_1511_; 
v_a_1491_ = lean_array_uget_borrowed(v_as_1477_, v_i_1479_);
v_fst_1492_ = lean_ctor_get(v_a_1491_, 0);
v_snd_1493_ = lean_ctor_get(v_a_1491_, 1);
v_start_1494_ = lean_ctor_get(v_b_1480_, 0);
v_stop_1495_ = lean_ctor_get(v_b_1480_, 1);
v_start_1496_ = lean_ctor_get(v_fst_1492_, 0);
v_stop_1497_ = lean_ctor_get(v_fst_1492_, 1);
v___x_1498_ = l_Lean_Linter_Extra_linter_extra_unnecessarySeqFocus;
v___x_1511_ = lean_nat_dec_le(v_start_1494_, v_start_1496_);
if (v___x_1511_ == 0)
{
v___y_1500_ = v___x_1511_;
goto v___jp_1499_;
}
else
{
uint8_t v___x_1512_; 
v___x_1512_ = lean_nat_dec_le(v_stop_1497_, v_stop_1495_);
v___y_1500_ = v___x_1512_;
goto v___jp_1499_;
}
v___jp_1499_:
{
if (v___y_1500_ == 0)
{
lean_object* v___x_1501_; lean_object* v___x_1502_; 
lean_dec_ref(v_b_1480_);
v___x_1501_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__2);
lean_inc(v_snd_1493_);
v___x_1502_ = l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2(v___x_1498_, v_snd_1493_, v___x_1501_, v___y_1481_, v___y_1482_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_dec_ref_known(v___x_1502_, 1);
lean_inc(v_fst_1492_);
v_a_1485_ = v_fst_1492_;
goto v___jp_1484_;
}
else
{
lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1510_; 
v_a_1503_ = lean_ctor_get(v___x_1502_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1505_ = v___x_1502_;
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1502_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1508_; 
if (v_isShared_1506_ == 0)
{
v___x_1508_ = v___x_1505_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_a_1503_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
}
}
else
{
v_a_1485_ = v_b_1480_;
goto v___jp_1484_;
}
}
}
v___jp_1484_:
{
size_t v___x_1486_; size_t v___x_1487_; 
v___x_1486_ = ((size_t)1ULL);
v___x_1487_ = lean_usize_add(v_i_1479_, v___x_1486_);
v_i_1479_ = v___x_1487_;
v_b_1480_ = v_a_1485_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___boxed(lean_object* v_as_1513_, lean_object* v_sz_1514_, lean_object* v_i_1515_, lean_object* v_b_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
size_t v_sz_boxed_1520_; size_t v_i_boxed_1521_; lean_object* v_res_1522_; 
v_sz_boxed_1520_ = lean_unbox_usize(v_sz_1514_);
lean_dec(v_sz_1514_);
v_i_boxed_1521_ = lean_unbox_usize(v_i_1515_);
lean_dec(v_i_1515_);
v_res_1522_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4(v_as_1513_, v_sz_boxed_1520_, v_i_boxed_1521_, v_b_1516_, v___y_1517_, v___y_1518_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec_ref(v_as_1513_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__0(lean_object* v_r_1523_){
_start:
{
lean_object* v_start_1524_; lean_object* v_stop_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1534_; 
v_start_1524_ = lean_ctor_get(v_r_1523_, 0);
v_stop_1525_ = lean_ctor_get(v_r_1523_, 1);
v_isSharedCheck_1534_ = !lean_is_exclusive(v_r_1523_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1527_ = v_r_1523_;
v_isShared_1528_ = v_isSharedCheck_1534_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_stop_1525_);
lean_inc(v_start_1524_);
lean_dec(v_r_1523_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1534_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1532_; 
v___x_1529_ = lean_nat_to_int(v_stop_1525_);
v___x_1530_ = lean_int_neg(v___x_1529_);
lean_dec(v___x_1529_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 1, v___x_1530_);
v___x_1532_ = v___x_1527_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_start_1524_);
lean_ctor_set(v_reuseFailAlloc_1533_, 1, v___x_1530_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg(lean_object* v_hi_1537_, lean_object* v_pivot_1538_, lean_object* v_as_1539_, lean_object* v_i_1540_, lean_object* v_k_1541_){
_start:
{
uint8_t v___x_1546_; 
v___x_1546_ = lean_nat_dec_lt(v_k_1541_, v_hi_1537_);
if (v___x_1546_ == 0)
{
lean_object* v___x_1547_; lean_object* v___x_1548_; 
lean_dec(v_k_1541_);
lean_dec_ref(v_pivot_1538_);
v___x_1547_ = lean_array_fswap(v_as_1539_, v_i_1540_, v_hi_1537_);
v___x_1548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1548_, 0, v_i_1540_);
lean_ctor_set(v___x_1548_, 1, v___x_1547_);
return v___x_1548_;
}
else
{
lean_object* v___x_1549_; lean_object* v_fst_1550_; lean_object* v_fst_1551_; lean_object* v___f_1552_; lean_object* v___f_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_7291__overap_1556_; lean_object* v___x_1557_; uint8_t v___x_1558_; 
v___x_1549_ = lean_array_fget_borrowed(v_as_1539_, v_k_1541_);
v_fst_1550_ = lean_ctor_get(v___x_1549_, 0);
v_fst_1551_ = lean_ctor_get(v_pivot_1538_, 0);
v___f_1552_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg___closed__0));
v___f_1553_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg___closed__1));
lean_inc(v_fst_1550_);
v___x_1554_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__0(v_fst_1550_);
lean_inc(v_fst_1551_);
v___x_1555_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__0(v_fst_1551_);
v___x_7291__overap_1556_ = l_lexOrd___redArg(v___f_1552_, v___f_1553_);
v___x_1557_ = lean_apply_2(v___x_7291__overap_1556_, v___x_1554_, v___x_1555_);
v___x_1558_ = lean_unbox(v___x_1557_);
if (v___x_1558_ == 0)
{
if (v___x_1546_ == 0)
{
goto v___jp_1542_;
}
else
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1559_ = lean_array_fswap(v_as_1539_, v_i_1540_, v_k_1541_);
v___x_1560_ = lean_unsigned_to_nat(1u);
v___x_1561_ = lean_nat_add(v_i_1540_, v___x_1560_);
lean_dec(v_i_1540_);
v___x_1562_ = lean_nat_add(v_k_1541_, v___x_1560_);
lean_dec(v_k_1541_);
v_as_1539_ = v___x_1559_;
v_i_1540_ = v___x_1561_;
v_k_1541_ = v___x_1562_;
goto _start;
}
}
else
{
goto v___jp_1542_;
}
}
v___jp_1542_:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1543_ = lean_unsigned_to_nat(1u);
v___x_1544_ = lean_nat_add(v_k_1541_, v___x_1543_);
lean_dec(v_k_1541_);
v_k_1541_ = v___x_1544_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg___boxed(lean_object* v_hi_1564_, lean_object* v_pivot_1565_, lean_object* v_as_1566_, lean_object* v_i_1567_, lean_object* v_k_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg(v_hi_1564_, v_pivot_1565_, v_as_1566_, v_i_1567_, v_k_1568_);
lean_dec(v_hi_1564_);
return v_res_1569_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__1(lean_object* v___f_1570_, lean_object* v___f_1571_, lean_object* v___f_1572_, uint8_t v___x_1573_, lean_object* v_x1_1574_, lean_object* v_x2_1575_){
_start:
{
lean_object* v_fst_1576_; lean_object* v_fst_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_7499__overap_1580_; lean_object* v___x_1581_; uint8_t v___x_1582_; 
v_fst_1576_ = lean_ctor_get(v_x1_1574_, 0);
lean_inc(v_fst_1576_);
lean_dec_ref(v_x1_1574_);
v_fst_1577_ = lean_ctor_get(v_x2_1575_, 0);
lean_inc(v_fst_1577_);
lean_dec_ref(v_x2_1575_);
lean_inc_ref(v___f_1570_);
v___x_1578_ = lean_apply_1(v___f_1570_, v_fst_1576_);
v___x_1579_ = lean_apply_1(v___f_1570_, v_fst_1577_);
v___x_7499__overap_1580_ = l_lexOrd___redArg(v___f_1571_, v___f_1572_);
v___x_1581_ = lean_apply_2(v___x_7499__overap_1580_, v___x_1578_, v___x_1579_);
v___x_1582_ = lean_unbox(v___x_1581_);
if (v___x_1582_ == 0)
{
return v___x_1573_;
}
else
{
uint8_t v___x_1583_; 
v___x_1583_ = 0;
return v___x_1583_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__1___boxed(lean_object* v___f_1584_, lean_object* v___f_1585_, lean_object* v___f_1586_, lean_object* v___x_1587_, lean_object* v_x1_1588_, lean_object* v_x2_1589_){
_start:
{
uint8_t v___x_8266__boxed_1590_; uint8_t v_res_1591_; lean_object* v_r_1592_; 
v___x_8266__boxed_1590_ = lean_unbox(v___x_1587_);
v_res_1591_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__1(v___f_1584_, v___f_1585_, v___f_1586_, v___x_8266__boxed_1590_, v_x1_1588_, v_x2_1589_);
v_r_1592_ = lean_box(v_res_1591_);
return v_r_1592_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg(lean_object* v_n_1594_, lean_object* v_as_1595_, lean_object* v_lo_1596_, lean_object* v_hi_1597_){
_start:
{
lean_object* v___y_1599_; uint8_t v___x_1609_; 
v___x_1609_ = lean_nat_dec_lt(v_lo_1596_, v_hi_1597_);
if (v___x_1609_ == 0)
{
lean_dec(v_lo_1596_);
return v_as_1595_;
}
else
{
lean_object* v___f_1610_; lean_object* v___f_1611_; lean_object* v___f_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v_mid_1615_; lean_object* v___y_1617_; lean_object* v___y_1623_; lean_object* v___x_1628_; lean_object* v___x_1629_; uint8_t v___x_1630_; 
v___f_1610_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___closed__0));
v___f_1611_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg___closed__0));
v___f_1612_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg___closed__1));
v___x_1613_ = lean_nat_add(v_lo_1596_, v_hi_1597_);
v___x_1614_ = lean_unsigned_to_nat(1u);
v_mid_1615_ = lean_nat_shiftr(v___x_1613_, v___x_1614_);
lean_dec(v___x_1613_);
v___x_1628_ = lean_array_fget_borrowed(v_as_1595_, v_mid_1615_);
v___x_1629_ = lean_array_fget_borrowed(v_as_1595_, v_lo_1596_);
lean_inc(v___x_1629_);
lean_inc(v___x_1628_);
v___x_1630_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__1(v___f_1610_, v___f_1611_, v___f_1612_, v___x_1609_, v___x_1628_, v___x_1629_);
if (v___x_1630_ == 0)
{
v___y_1623_ = v_as_1595_;
goto v___jp_1622_;
}
else
{
lean_object* v___x_1631_; 
v___x_1631_ = lean_array_fswap(v_as_1595_, v_lo_1596_, v_mid_1615_);
v___y_1623_ = v___x_1631_;
goto v___jp_1622_;
}
v___jp_1616_:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; uint8_t v___x_1620_; 
v___x_1618_ = lean_array_fget_borrowed(v___y_1617_, v_mid_1615_);
v___x_1619_ = lean_array_fget_borrowed(v___y_1617_, v_hi_1597_);
lean_inc(v___x_1619_);
lean_inc(v___x_1618_);
v___x_1620_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__1(v___f_1610_, v___f_1611_, v___f_1612_, v___x_1609_, v___x_1618_, v___x_1619_);
if (v___x_1620_ == 0)
{
lean_dec(v_mid_1615_);
v___y_1599_ = v___y_1617_;
goto v___jp_1598_;
}
else
{
lean_object* v___x_1621_; 
v___x_1621_ = lean_array_fswap(v___y_1617_, v_mid_1615_, v_hi_1597_);
lean_dec(v_mid_1615_);
v___y_1599_ = v___x_1621_;
goto v___jp_1598_;
}
}
v___jp_1622_:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; uint8_t v___x_1626_; 
v___x_1624_ = lean_array_fget_borrowed(v___y_1623_, v_hi_1597_);
v___x_1625_ = lean_array_fget_borrowed(v___y_1623_, v_lo_1596_);
lean_inc(v___x_1625_);
lean_inc(v___x_1624_);
v___x_1626_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__1(v___f_1610_, v___f_1611_, v___f_1612_, v___x_1609_, v___x_1624_, v___x_1625_);
if (v___x_1626_ == 0)
{
v___y_1617_ = v___y_1623_;
goto v___jp_1616_;
}
else
{
lean_object* v___x_1627_; 
v___x_1627_ = lean_array_fswap(v___y_1623_, v_lo_1596_, v_hi_1597_);
v___y_1617_ = v___x_1627_;
goto v___jp_1616_;
}
}
}
v___jp_1598_:
{
lean_object* v_pivot_1600_; lean_object* v___x_1601_; lean_object* v_fst_1602_; lean_object* v_snd_1603_; uint8_t v___x_1604_; 
v_pivot_1600_ = lean_array_fget(v___y_1599_, v_hi_1597_);
lean_inc_n(v_lo_1596_, 2);
v___x_1601_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg(v_hi_1597_, v_pivot_1600_, v___y_1599_, v_lo_1596_, v_lo_1596_);
v_fst_1602_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_fst_1602_);
v_snd_1603_ = lean_ctor_get(v___x_1601_, 1);
lean_inc(v_snd_1603_);
lean_dec_ref(v___x_1601_);
v___x_1604_ = lean_nat_dec_le(v_hi_1597_, v_fst_1602_);
if (v___x_1604_ == 0)
{
lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1605_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg(v_n_1594_, v_snd_1603_, v_lo_1596_, v_fst_1602_);
v___x_1606_ = lean_unsigned_to_nat(1u);
v___x_1607_ = lean_nat_add(v_fst_1602_, v___x_1606_);
lean_dec(v_fst_1602_);
v_as_1595_ = v___x_1605_;
v_lo_1596_ = v___x_1607_;
goto _start;
}
else
{
lean_dec(v_fst_1602_);
lean_dec(v_lo_1596_);
return v_snd_1603_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___boxed(lean_object* v_n_1632_, lean_object* v_as_1633_, lean_object* v_lo_1634_, lean_object* v_hi_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg(v_n_1632_, v_as_1633_, v_lo_1634_, v_hi_1635_);
lean_dec(v_hi_1635_);
lean_dec(v_n_1632_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6(uint8_t v___x_1637_, lean_object* v_x_1638_, lean_object* v_x_1639_){
_start:
{
if (lean_obj_tag(v_x_1639_) == 0)
{
return v_x_1638_;
}
else
{
lean_object* v_value_1640_; uint8_t v_used_1641_; 
v_value_1640_ = lean_ctor_get(v_x_1639_, 1);
v_used_1641_ = lean_ctor_get_uint8(v_value_1640_, sizeof(void*)*1);
if (v_used_1641_ == 0)
{
lean_object* v_tail_1642_; 
v_tail_1642_ = lean_ctor_get(v_x_1639_, 2);
lean_inc(v_tail_1642_);
lean_dec_ref_known(v_x_1639_, 3);
v_x_1639_ = v_tail_1642_;
goto _start;
}
else
{
lean_object* v_key_1644_; lean_object* v_tail_1645_; lean_object* v_stx_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___y_1650_; lean_object* v___x_1654_; 
lean_inc(v_value_1640_);
v_key_1644_ = lean_ctor_get(v_x_1639_, 0);
lean_inc(v_key_1644_);
v_tail_1645_ = lean_ctor_get(v_x_1639_, 2);
lean_inc(v_tail_1645_);
lean_dec_ref_known(v_x_1639_, 3);
v_stx_1646_ = lean_ctor_get(v_value_1640_, 0);
lean_inc(v_stx_1646_);
lean_dec(v_value_1640_);
v___x_1647_ = lean_unsigned_to_nat(1u);
v___x_1648_ = l_Lean_Syntax_getArg(v_stx_1646_, v___x_1647_);
lean_dec(v_stx_1646_);
v___x_1654_ = l_Lean_Syntax_getRange_x3f(v___x_1648_, v___x_1637_);
if (lean_obj_tag(v___x_1654_) == 0)
{
v___y_1650_ = v_key_1644_;
goto v___jp_1649_;
}
else
{
lean_object* v_val_1655_; 
lean_dec(v_key_1644_);
v_val_1655_ = lean_ctor_get(v___x_1654_, 0);
lean_inc(v_val_1655_);
lean_dec_ref_known(v___x_1654_, 1);
v___y_1650_ = v_val_1655_;
goto v___jp_1649_;
}
v___jp_1649_:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___y_1650_);
lean_ctor_set(v___x_1651_, 1, v___x_1648_);
v___x_1652_ = lean_array_push(v_x_1638_, v___x_1651_);
v_x_1638_ = v___x_1652_;
v_x_1639_ = v_tail_1645_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6___boxed(lean_object* v___x_1656_, lean_object* v_x_1657_, lean_object* v_x_1658_){
_start:
{
uint8_t v___x_8360__boxed_1659_; lean_object* v_res_1660_; 
v___x_8360__boxed_1659_ = lean_unbox(v___x_1656_);
v_res_1660_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6(v___x_8360__boxed_1659_, v_x_1657_, v_x_1658_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__7(uint8_t v___x_1661_, lean_object* v_as_1662_, size_t v_i_1663_, size_t v_stop_1664_, lean_object* v_b_1665_){
_start:
{
uint8_t v___x_1666_; 
v___x_1666_ = lean_usize_dec_eq(v_i_1663_, v_stop_1664_);
if (v___x_1666_ == 0)
{
lean_object* v___x_1667_; lean_object* v___x_1668_; size_t v___x_1669_; size_t v___x_1670_; 
v___x_1667_ = lean_array_uget_borrowed(v_as_1662_, v_i_1663_);
lean_inc(v___x_1667_);
v___x_1668_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6(v___x_1661_, v_b_1665_, v___x_1667_);
v___x_1669_ = ((size_t)1ULL);
v___x_1670_ = lean_usize_add(v_i_1663_, v___x_1669_);
v_i_1663_ = v___x_1670_;
v_b_1665_ = v___x_1668_;
goto _start;
}
else
{
return v_b_1665_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__7___boxed(lean_object* v___x_1672_, lean_object* v_as_1673_, lean_object* v_i_1674_, lean_object* v_stop_1675_, lean_object* v_b_1676_){
_start:
{
uint8_t v___x_8401__boxed_1677_; size_t v_i_boxed_1678_; size_t v_stop_boxed_1679_; lean_object* v_res_1680_; 
v___x_8401__boxed_1677_ = lean_unbox(v___x_1672_);
v_i_boxed_1678_ = lean_unbox_usize(v_i_1674_);
lean_dec(v_i_1674_);
v_stop_boxed_1679_ = lean_unbox_usize(v_stop_1675_);
lean_dec(v_stop_1675_);
v_res_1680_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__7(v___x_8401__boxed_1677_, v_as_1673_, v_i_boxed_1678_, v_stop_boxed_1679_, v_b_1676_);
lean_dec_ref(v_as_1673_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1(lean_object* v_stx_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v___y_1690_; lean_object* v___y_1691_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1720_; lean_object* v___y_1721_; lean_object* v___y_1722_; lean_object* v___y_1723_; lean_object* v___y_1724_; lean_object* v___y_1727_; lean_object* v___x_1735_; lean_object* v_a_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1773_; 
v___x_1735_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1(v___y_1686_, v___y_1687_);
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_1773_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1738_ = v___x_1735_;
v_isShared_1739_ = v_isSharedCheck_1773_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_a_1736_);
lean_dec(v___x_1735_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1773_;
goto v_resetjp_1737_;
}
v___jp_1689_:
{
size_t v_sz_1692_; size_t v___x_1693_; lean_object* v___x_1694_; 
v_sz_1692_ = lean_array_size(v___y_1691_);
v___x_1693_ = ((size_t)0ULL);
lean_inc_ref(v___y_1690_);
v___x_1694_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4(v___y_1691_, v_sz_1692_, v___x_1693_, v___y_1690_, v___y_1686_, v___y_1687_);
lean_dec_ref(v___y_1691_);
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1702_; 
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1694_);
if (v_isSharedCheck_1702_ == 0)
{
lean_object* v_unused_1703_; 
v_unused_1703_ = lean_ctor_get(v___x_1694_, 0);
lean_dec(v_unused_1703_);
v___x_1696_ = v___x_1694_;
v_isShared_1697_ = v_isSharedCheck_1702_;
goto v_resetjp_1695_;
}
else
{
lean_dec(v___x_1694_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1702_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1698_; lean_object* v___x_1700_; 
v___x_1698_ = lean_box(0);
if (v_isShared_1697_ == 0)
{
lean_ctor_set(v___x_1696_, 0, v___x_1698_);
v___x_1700_ = v___x_1696_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v___x_1698_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
else
{
lean_object* v_a_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1711_; 
v_a_1704_ = lean_ctor_get(v___x_1694_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1694_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1706_ = v___x_1694_;
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_a_1704_);
lean_dec(v___x_1694_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1709_; 
if (v_isShared_1707_ == 0)
{
v___x_1709_ = v___x_1706_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_a_1704_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
}
v___jp_1712_:
{
lean_object* v___x_1718_; 
v___x_1718_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg(v___y_1716_, v___y_1715_, v___y_1713_, v___y_1717_);
lean_dec(v___y_1717_);
lean_dec(v___y_1716_);
v___y_1690_ = v___y_1714_;
v___y_1691_ = v___x_1718_;
goto v___jp_1689_;
}
v___jp_1719_:
{
uint8_t v___x_1725_; 
v___x_1725_ = lean_nat_dec_le(v___y_1724_, v___y_1723_);
if (v___x_1725_ == 0)
{
lean_dec(v___y_1723_);
lean_inc(v___y_1724_);
v___y_1713_ = v___y_1724_;
v___y_1714_ = v___y_1720_;
v___y_1715_ = v___y_1722_;
v___y_1716_ = v___y_1721_;
v___y_1717_ = v___y_1724_;
goto v___jp_1712_;
}
else
{
v___y_1713_ = v___y_1724_;
v___y_1714_ = v___y_1720_;
v___y_1715_ = v___y_1722_;
v___y_1716_ = v___y_1721_;
v___y_1717_ = v___y_1723_;
goto v___jp_1712_;
}
}
v___jp_1726_:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; uint8_t v___x_1731_; 
v___x_1728_ = lean_unsigned_to_nat(0u);
v___x_1729_ = ((lean_object*)(l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1___closed__0));
v___x_1730_ = lean_array_get_size(v___y_1727_);
v___x_1731_ = lean_nat_dec_eq(v___x_1730_, v___x_1728_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; lean_object* v___x_1733_; uint8_t v___x_1734_; 
v___x_1732_ = lean_unsigned_to_nat(1u);
v___x_1733_ = lean_nat_sub(v___x_1730_, v___x_1732_);
v___x_1734_ = lean_nat_dec_le(v___x_1728_, v___x_1733_);
if (v___x_1734_ == 0)
{
lean_inc(v___x_1733_);
v___y_1720_ = v___x_1729_;
v___y_1721_ = v___x_1730_;
v___y_1722_ = v___y_1727_;
v___y_1723_ = v___x_1733_;
v___y_1724_ = v___x_1733_;
goto v___jp_1719_;
}
else
{
v___y_1720_ = v___x_1729_;
v___y_1721_ = v___x_1730_;
v___y_1722_ = v___y_1727_;
v___y_1723_ = v___x_1733_;
v___y_1724_ = v___x_1728_;
goto v___jp_1719_;
}
}
else
{
v___y_1690_ = v___x_1729_;
v___y_1691_ = v___y_1727_;
goto v___jp_1689_;
}
}
v_resetjp_1737_:
{
lean_object* v___x_1740_; uint8_t v___y_1742_; lean_object* v___x_1769_; uint8_t v___x_1770_; 
v___x_1740_ = lean_st_ref_get(v___y_1687_);
v___x_1769_ = l_Lean_Linter_Extra_linter_extra_unnecessarySeqFocus;
v___x_1770_ = l_Lean_Linter_getLinterValue(v___x_1769_, v_a_1736_);
lean_dec(v_a_1736_);
if (v___x_1770_ == 0)
{
lean_dec(v___x_1740_);
v___y_1742_ = v___x_1770_;
goto v___jp_1741_;
}
else
{
lean_object* v_infoState_1771_; uint8_t v_enabled_1772_; 
v_infoState_1771_ = lean_ctor_get(v___x_1740_, 8);
lean_inc_ref(v_infoState_1771_);
lean_dec(v___x_1740_);
v_enabled_1772_ = lean_ctor_get_uint8(v_infoState_1771_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1771_);
v___y_1742_ = v_enabled_1772_;
goto v___jp_1741_;
}
v___jp_1741_:
{
if (v___y_1742_ == 0)
{
lean_object* v___x_1743_; lean_object* v___x_1745_; 
lean_dec(v_stx_1685_);
v___x_1743_ = lean_box(0);
if (v_isShared_1739_ == 0)
{
lean_ctor_set(v___x_1738_, 0, v___x_1743_);
v___x_1745_ = v___x_1738_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v___x_1743_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
else
{
lean_object* v___x_1747_; lean_object* v_messages_1748_; uint8_t v___x_1749_; 
v___x_1747_ = lean_st_ref_get(v___y_1687_);
v_messages_1748_ = lean_ctor_get(v___x_1747_, 1);
lean_inc_ref(v_messages_1748_);
lean_dec(v___x_1747_);
v___x_1749_ = l_Lean_MessageLog_hasErrors(v_messages_1748_);
lean_dec_ref(v_messages_1748_);
if (v___x_1749_ == 0)
{
lean_object* v___x_1750_; lean_object* v_a_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___f_1754_; lean_object* v___x_1755_; lean_object* v_snd_1756_; lean_object* v_buckets_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; uint8_t v___x_1761_; 
lean_del_object(v___x_1738_);
v___x_1750_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3___redArg(v___y_1687_);
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
lean_inc(v_a_1751_);
lean_dec_ref(v___x_1750_);
v___x_1752_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_multigoalKindsRef;
v___x_1753_ = lean_st_ref_get(v___x_1752_);
v___f_1754_ = lean_alloc_closure((void*)(l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1754_, 0, v_stx_1685_);
lean_closure_set(v___f_1754_, 1, v___x_1753_);
lean_closure_set(v___f_1754_, 2, v_a_1751_);
v___x_1755_ = l_runST___redArg(v___f_1754_);
v_snd_1756_ = lean_ctor_get(v___x_1755_, 1);
lean_inc(v_snd_1756_);
lean_dec(v___x_1755_);
v_buckets_1757_ = lean_ctor_get(v_snd_1756_, 1);
lean_inc_ref(v_buckets_1757_);
lean_dec(v_snd_1756_);
v___x_1758_ = lean_unsigned_to_nat(0u);
v___x_1759_ = ((lean_object*)(l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1___closed__1));
v___x_1760_ = lean_array_get_size(v_buckets_1757_);
v___x_1761_ = lean_nat_dec_lt(v___x_1758_, v___x_1760_);
if (v___x_1761_ == 0)
{
lean_dec_ref(v_buckets_1757_);
v___y_1727_ = v___x_1759_;
goto v___jp_1726_;
}
else
{
size_t v___x_1762_; size_t v___x_1763_; lean_object* v___x_1764_; 
v___x_1762_ = ((size_t)0ULL);
v___x_1763_ = lean_usize_of_nat(v___x_1760_);
v___x_1764_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__7(v___x_1749_, v_buckets_1757_, v___x_1762_, v___x_1763_, v___x_1759_);
lean_dec_ref(v_buckets_1757_);
v___y_1727_ = v___x_1764_;
goto v___jp_1726_;
}
}
else
{
lean_object* v___x_1765_; lean_object* v___x_1767_; 
lean_dec(v_stx_1685_);
v___x_1765_ = lean_box(0);
if (v_isShared_1739_ == 0)
{
lean_ctor_set(v___x_1738_, 0, v___x_1765_);
v___x_1767_ = v___x_1738_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___x_1765_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1___boxed(lean_object* v_stx_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1(v_stx_1774_, v___y_1775_, v___y_1776_);
lean_dec(v___y_1776_);
lean_dec_ref(v___y_1775_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1(lean_object* v_o_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_){
_start:
{
lean_object* v___x_1798_; 
v___x_1798_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1___redArg(v_o_1794_, v___y_1796_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1___boxed(lean_object* v_o_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_){
_start:
{
lean_object* v_res_1803_; 
v_res_1803_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1(v_o_1799_, v___y_1800_, v___y_1801_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
return v_res_1803_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5(lean_object* v_n_1804_, lean_object* v_as_1805_, lean_object* v_lo_1806_, lean_object* v_hi_1807_, lean_object* v_w_1808_, lean_object* v_hlo_1809_, lean_object* v_hhi_1810_){
_start:
{
lean_object* v___x_1811_; 
v___x_1811_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg(v_n_1804_, v_as_1805_, v_lo_1806_, v_hi_1807_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___boxed(lean_object* v_n_1812_, lean_object* v_as_1813_, lean_object* v_lo_1814_, lean_object* v_hi_1815_, lean_object* v_w_1816_, lean_object* v_hlo_1817_, lean_object* v_hhi_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5(v_n_1812_, v_as_1813_, v_lo_1814_, v_hi_1815_, v_w_1816_, v_hlo_1817_, v_hhi_1818_);
lean_dec(v_hi_1815_);
lean_dec(v_n_1812_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7(lean_object* v_n_1820_, lean_object* v_lo_1821_, lean_object* v_hi_1822_, lean_object* v_hhi_1823_, lean_object* v_pivot_1824_, lean_object* v_as_1825_, lean_object* v_i_1826_, lean_object* v_k_1827_, lean_object* v_ilo_1828_, lean_object* v_ik_1829_, lean_object* v_w_1830_){
_start:
{
lean_object* v___x_1831_; 
v___x_1831_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg(v_hi_1822_, v_pivot_1824_, v_as_1825_, v_i_1826_, v_k_1827_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___boxed(lean_object* v_n_1832_, lean_object* v_lo_1833_, lean_object* v_hi_1834_, lean_object* v_hhi_1835_, lean_object* v_pivot_1836_, lean_object* v_as_1837_, lean_object* v_i_1838_, lean_object* v_k_1839_, lean_object* v_ilo_1840_, lean_object* v_ik_1841_, lean_object* v_w_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7(v_n_1832_, v_lo_1833_, v_hi_1834_, v_hhi_1835_, v_pivot_1836_, v_as_1837_, v_i_1838_, v_k_1839_, v_ilo_1840_, v_ik_1841_, v_w_1842_);
lean_dec(v_hi_1834_);
lean_dec(v_lo_1833_);
lean_dec(v_n_1832_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12(lean_object* v_msgData_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_){
_start:
{
lean_object* v___x_1848_; 
v___x_1848_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg(v_msgData_1844_, v___y_1846_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___boxed(lean_object* v_msgData_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12(v_msgData_1849_, v___y_1850_, v___y_1851_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_3917858151____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1855_ = ((lean_object*)(l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter));
v___x_1856_ = l_Lean_Elab_Command_addLinter(v___x_1855_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_3917858151____hygCtx___hyg_2____boxed(lean_object* v_a_1857_){
_start:
{
lean_object* v_res_1858_; 
v_res_1858_ = l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_3917858151____hygCtx___hyg_2_();
return v_res_1858_;
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
