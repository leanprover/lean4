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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object*);
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
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
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
lean_object* l_instMonadST(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Syntax_instBEqRange_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_instHashableRange_hash___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_runST___redArg(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_withSetOptionIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_withSetOptionIn___boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__0_value)} };
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
v___x_75_ = lean_st_ref_set(v___x_72_, v___x_74_);
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
v___x_103_ = lean_st_ref_set(v___x_99_, v___y_102_);
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
lean_object* v_kind_285_; lean_object* v_args_286_; lean_object* v___f_287_; lean_object* v___y_289_; uint8_t v___y_304_; lean_object* v___x_314_; uint8_t v___x_315_; 
v_kind_285_ = lean_ctor_get(v_stx_281_, 1);
v_args_286_ = lean_ctor_get(v_stx_281_, 2);
lean_inc_ref(v_args_286_);
v___f_287_ = lean_alloc_closure((void*)(l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___lam__0___boxed), 4, 0);
v___x_314_ = ((lean_object*)(l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__1));
v___x_315_ = lean_name_eq(v_kind_285_, v___x_314_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; uint8_t v___x_317_; 
v___x_316_ = ((lean_object*)(l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__3));
v___x_317_ = lean_name_eq(v_kind_285_, v___x_316_);
v___y_304_ = v___x_317_;
goto v___jp_303_;
}
else
{
v___y_304_ = v___x_315_;
goto v___jp_303_;
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
size_t v___x_295_; size_t v___x_296_; lean_object* v___x_749__overap_297_; lean_object* v___x_298_; 
v___x_295_ = ((size_t)0ULL);
v___x_296_ = lean_usize_of_nat(v___x_291_);
v___x_749__overap_297_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_284_, v___f_287_, v_args_286_, v___x_295_, v___x_296_, v___x_292_);
lean_inc(v___y_289_);
v___x_298_ = lean_apply_2(v___x_749__overap_297_, v___y_289_, lean_box(0));
return v___x_298_;
}
}
else
{
size_t v___x_299_; size_t v___x_300_; lean_object* v___x_754__overap_301_; lean_object* v___x_302_; 
v___x_299_ = ((size_t)0ULL);
v___x_300_ = lean_usize_of_nat(v___x_291_);
v___x_754__overap_301_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_284_, v___f_287_, v_args_286_, v___x_299_, v___x_300_, v___x_292_);
lean_inc(v___y_289_);
v___x_302_ = lean_apply_2(v___x_754__overap_301_, v___y_289_, lean_box(0));
return v___x_302_;
}
}
}
v___jp_303_:
{
if (v___y_304_ == 0)
{
lean_dec_ref_known(v_stx_281_, 3);
v___y_289_ = v_a_282_;
goto v___jp_288_;
}
else
{
lean_object* v___x_305_; 
v___x_305_ = l_Lean_Syntax_getRange_x3f(v_stx_281_, v___y_304_);
if (lean_obj_tag(v___x_305_) == 1)
{
lean_object* v_val_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; uint8_t v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v_val_306_ = lean_ctor_get(v___x_305_, 0);
lean_inc(v_val_306_);
lean_dec_ref_known(v___x_305_, 1);
v___x_307_ = lean_st_ref_take(v_a_282_);
v___x_308_ = ((lean_object*)(l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___closed__2));
v___x_309_ = ((lean_object*)(l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___closed__3));
v___x_310_ = 0;
v___x_311_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_311_, 0, v_stx_281_);
lean_ctor_set_uint8(v___x_311_, sizeof(void*)*1, v___x_310_);
v___x_312_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_308_, v___x_309_, v___x_307_, v_val_306_, v___x_311_);
v___x_313_ = lean_st_ref_set(v_a_282_, v___x_312_);
v___y_289_ = v_a_282_;
goto v___jp_288_;
}
else
{
lean_dec(v___x_305_);
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
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v_nbuckets_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_400_ = lean_array_get_size(v_data_399_);
v___x_401_ = lean_unsigned_to_nat(2u);
v_nbuckets_402_ = lean_nat_mul(v___x_400_, v___x_401_);
v___x_403_ = lean_unsigned_to_nat(0u);
v___x_404_ = lean_box(0);
v___x_405_ = lean_mk_array(v_nbuckets_402_, v___x_404_);
v___x_406_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10_spec__13___redArg(v___x_403_, v_data_399_, v___x_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__11___redArg(lean_object* v_a_407_, lean_object* v_b_408_, lean_object* v_x_409_){
_start:
{
if (lean_obj_tag(v_x_409_) == 0)
{
lean_dec(v_b_408_);
lean_dec_ref(v_a_407_);
return v_x_409_;
}
else
{
lean_object* v_key_410_; lean_object* v_value_411_; lean_object* v_tail_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_424_; 
v_key_410_ = lean_ctor_get(v_x_409_, 0);
v_value_411_ = lean_ctor_get(v_x_409_, 1);
v_tail_412_ = lean_ctor_get(v_x_409_, 2);
v_isSharedCheck_424_ = !lean_is_exclusive(v_x_409_);
if (v_isSharedCheck_424_ == 0)
{
v___x_414_ = v_x_409_;
v_isShared_415_ = v_isSharedCheck_424_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_tail_412_);
lean_inc(v_value_411_);
lean_inc(v_key_410_);
lean_dec(v_x_409_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_424_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
uint8_t v___x_416_; 
v___x_416_ = l_Lean_Syntax_instBEqRange_beq(v_key_410_, v_a_407_);
if (v___x_416_ == 0)
{
lean_object* v___x_417_; lean_object* v___x_419_; 
v___x_417_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__11___redArg(v_a_407_, v_b_408_, v_tail_412_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 2, v___x_417_);
v___x_419_ = v___x_414_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_key_410_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v_value_411_);
lean_ctor_set(v_reuseFailAlloc_420_, 2, v___x_417_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
else
{
lean_object* v___x_422_; 
lean_dec(v_value_411_);
lean_dec(v_key_410_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 1, v_b_408_);
lean_ctor_set(v___x_414_, 0, v_a_407_);
v___x_422_ = v___x_414_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_a_407_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v_b_408_);
lean_ctor_set(v_reuseFailAlloc_423_, 2, v_tail_412_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__7___redArg(lean_object* v_a_425_, lean_object* v_x_426_){
_start:
{
if (lean_obj_tag(v_x_426_) == 0)
{
uint8_t v___x_427_; 
v___x_427_ = 0;
return v___x_427_;
}
else
{
lean_object* v_key_428_; lean_object* v_tail_429_; uint8_t v___x_430_; 
v_key_428_ = lean_ctor_get(v_x_426_, 0);
v_tail_429_ = lean_ctor_get(v_x_426_, 2);
v___x_430_ = l_Lean_Syntax_instBEqRange_beq(v_key_428_, v_a_425_);
if (v___x_430_ == 0)
{
v_x_426_ = v_tail_429_;
goto _start;
}
else
{
return v___x_430_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__7___redArg___boxed(lean_object* v_a_432_, lean_object* v_x_433_){
_start:
{
uint8_t v_res_434_; lean_object* v_r_435_; 
v_res_434_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__7___redArg(v_a_432_, v_x_433_);
lean_dec(v_x_433_);
lean_dec_ref(v_a_432_);
v_r_435_ = lean_box(v_res_434_);
return v_r_435_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4___redArg(lean_object* v_m_436_, lean_object* v_a_437_, lean_object* v_b_438_){
_start:
{
lean_object* v_size_439_; lean_object* v_buckets_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_483_; 
v_size_439_ = lean_ctor_get(v_m_436_, 0);
v_buckets_440_ = lean_ctor_get(v_m_436_, 1);
v_isSharedCheck_483_ = !lean_is_exclusive(v_m_436_);
if (v_isSharedCheck_483_ == 0)
{
v___x_442_ = v_m_436_;
v_isShared_443_ = v_isSharedCheck_483_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_buckets_440_);
lean_inc(v_size_439_);
lean_dec(v_m_436_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_483_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_444_; uint64_t v___x_445_; uint64_t v___x_446_; uint64_t v___x_447_; uint64_t v_fold_448_; uint64_t v___x_449_; uint64_t v___x_450_; uint64_t v___x_451_; size_t v___x_452_; size_t v___x_453_; size_t v___x_454_; size_t v___x_455_; size_t v___x_456_; lean_object* v_bkt_457_; uint8_t v___x_458_; 
v___x_444_ = lean_array_get_size(v_buckets_440_);
v___x_445_ = l_Lean_Syntax_instHashableRange_hash(v_a_437_);
v___x_446_ = 32ULL;
v___x_447_ = lean_uint64_shift_right(v___x_445_, v___x_446_);
v_fold_448_ = lean_uint64_xor(v___x_445_, v___x_447_);
v___x_449_ = 16ULL;
v___x_450_ = lean_uint64_shift_right(v_fold_448_, v___x_449_);
v___x_451_ = lean_uint64_xor(v_fold_448_, v___x_450_);
v___x_452_ = lean_uint64_to_usize(v___x_451_);
v___x_453_ = lean_usize_of_nat(v___x_444_);
v___x_454_ = ((size_t)1ULL);
v___x_455_ = lean_usize_sub(v___x_453_, v___x_454_);
v___x_456_ = lean_usize_land(v___x_452_, v___x_455_);
v_bkt_457_ = lean_array_uget_borrowed(v_buckets_440_, v___x_456_);
v___x_458_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__7___redArg(v_a_437_, v_bkt_457_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; lean_object* v_size_x27_460_; lean_object* v___x_461_; lean_object* v_buckets_x27_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; uint8_t v___x_468_; 
v___x_459_ = lean_unsigned_to_nat(1u);
v_size_x27_460_ = lean_nat_add(v_size_439_, v___x_459_);
lean_dec(v_size_439_);
lean_inc(v_bkt_457_);
v___x_461_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_461_, 0, v_a_437_);
lean_ctor_set(v___x_461_, 1, v_b_438_);
lean_ctor_set(v___x_461_, 2, v_bkt_457_);
v_buckets_x27_462_ = lean_array_uset(v_buckets_440_, v___x_456_, v___x_461_);
v___x_463_ = lean_unsigned_to_nat(4u);
v___x_464_ = lean_nat_mul(v_size_x27_460_, v___x_463_);
v___x_465_ = lean_unsigned_to_nat(3u);
v___x_466_ = lean_nat_div(v___x_464_, v___x_465_);
lean_dec(v___x_464_);
v___x_467_ = lean_array_get_size(v_buckets_x27_462_);
v___x_468_ = lean_nat_dec_le(v___x_466_, v___x_467_);
lean_dec(v___x_466_);
if (v___x_468_ == 0)
{
lean_object* v_val_469_; lean_object* v___x_471_; 
v_val_469_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10___redArg(v_buckets_x27_462_);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 1, v_val_469_);
lean_ctor_set(v___x_442_, 0, v_size_x27_460_);
v___x_471_ = v___x_442_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_size_x27_460_);
lean_ctor_set(v_reuseFailAlloc_472_, 1, v_val_469_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
else
{
lean_object* v___x_474_; 
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 1, v_buckets_x27_462_);
lean_ctor_set(v___x_442_, 0, v_size_x27_460_);
v___x_474_ = v___x_442_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_size_x27_460_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v_buckets_x27_462_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
else
{
lean_object* v___x_476_; lean_object* v_buckets_x27_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_481_; 
lean_inc(v_bkt_457_);
v___x_476_ = lean_box(0);
v_buckets_x27_477_ = lean_array_uset(v_buckets_440_, v___x_456_, v___x_476_);
v___x_478_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__11___redArg(v_a_437_, v_b_438_, v_bkt_457_);
v___x_479_ = lean_array_uset(v_buckets_x27_477_, v___x_456_, v___x_478_);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 1, v___x_479_);
v___x_481_ = v___x_442_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_size_439_);
lean_ctor_set(v_reuseFailAlloc_482_, 1, v___x_479_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__8___redArg(lean_object* v_a_484_, lean_object* v_x_485_){
_start:
{
if (lean_obj_tag(v_x_485_) == 0)
{
return v_x_485_;
}
else
{
lean_object* v_key_486_; lean_object* v_value_487_; lean_object* v_tail_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_497_; 
v_key_486_ = lean_ctor_get(v_x_485_, 0);
v_value_487_ = lean_ctor_get(v_x_485_, 1);
v_tail_488_ = lean_ctor_get(v_x_485_, 2);
v_isSharedCheck_497_ = !lean_is_exclusive(v_x_485_);
if (v_isSharedCheck_497_ == 0)
{
v___x_490_ = v_x_485_;
v_isShared_491_ = v_isSharedCheck_497_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_tail_488_);
lean_inc(v_value_487_);
lean_inc(v_key_486_);
lean_dec(v_x_485_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_497_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
uint8_t v___x_492_; 
v___x_492_ = l_Lean_Syntax_instBEqRange_beq(v_key_486_, v_a_484_);
if (v___x_492_ == 0)
{
lean_object* v___x_493_; lean_object* v___x_495_; 
v___x_493_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__8___redArg(v_a_484_, v_tail_488_);
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 2, v___x_493_);
v___x_495_ = v___x_490_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_key_486_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v_value_487_);
lean_ctor_set(v_reuseFailAlloc_496_, 2, v___x_493_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
else
{
lean_del_object(v___x_490_);
lean_dec(v_value_487_);
lean_dec(v_key_486_);
return v_tail_488_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__8___redArg___boxed(lean_object* v_a_498_, lean_object* v_x_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__8___redArg(v_a_498_, v_x_499_);
lean_dec_ref(v_a_498_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3___redArg(lean_object* v_m_501_, lean_object* v_a_502_){
_start:
{
lean_object* v_size_503_; lean_object* v_buckets_504_; lean_object* v___x_505_; uint64_t v___x_506_; uint64_t v___x_507_; uint64_t v___x_508_; uint64_t v_fold_509_; uint64_t v___x_510_; uint64_t v___x_511_; uint64_t v___x_512_; size_t v___x_513_; size_t v___x_514_; size_t v___x_515_; size_t v___x_516_; size_t v___x_517_; lean_object* v_bkt_518_; uint8_t v___x_519_; 
v_size_503_ = lean_ctor_get(v_m_501_, 0);
v_buckets_504_ = lean_ctor_get(v_m_501_, 1);
v___x_505_ = lean_array_get_size(v_buckets_504_);
v___x_506_ = l_Lean_Syntax_instHashableRange_hash(v_a_502_);
v___x_507_ = 32ULL;
v___x_508_ = lean_uint64_shift_right(v___x_506_, v___x_507_);
v_fold_509_ = lean_uint64_xor(v___x_506_, v___x_508_);
v___x_510_ = 16ULL;
v___x_511_ = lean_uint64_shift_right(v_fold_509_, v___x_510_);
v___x_512_ = lean_uint64_xor(v_fold_509_, v___x_511_);
v___x_513_ = lean_uint64_to_usize(v___x_512_);
v___x_514_ = lean_usize_of_nat(v___x_505_);
v___x_515_ = ((size_t)1ULL);
v___x_516_ = lean_usize_sub(v___x_514_, v___x_515_);
v___x_517_ = lean_usize_land(v___x_513_, v___x_516_);
v_bkt_518_ = lean_array_uget_borrowed(v_buckets_504_, v___x_517_);
v___x_519_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__7___redArg(v_a_502_, v_bkt_518_);
if (v___x_519_ == 0)
{
return v_m_501_;
}
else
{
lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_532_; 
lean_inc(v_bkt_518_);
lean_inc_ref(v_buckets_504_);
lean_inc(v_size_503_);
v_isSharedCheck_532_ = !lean_is_exclusive(v_m_501_);
if (v_isSharedCheck_532_ == 0)
{
lean_object* v_unused_533_; lean_object* v_unused_534_; 
v_unused_533_ = lean_ctor_get(v_m_501_, 1);
lean_dec(v_unused_533_);
v_unused_534_ = lean_ctor_get(v_m_501_, 0);
lean_dec(v_unused_534_);
v___x_521_ = v_m_501_;
v_isShared_522_ = v_isSharedCheck_532_;
goto v_resetjp_520_;
}
else
{
lean_dec(v_m_501_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_532_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_523_; lean_object* v_buckets_x27_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_530_; 
v___x_523_ = lean_box(0);
v_buckets_x27_524_ = lean_array_uset(v_buckets_504_, v___x_517_, v___x_523_);
v___x_525_ = lean_unsigned_to_nat(1u);
v___x_526_ = lean_nat_sub(v_size_503_, v___x_525_);
lean_dec(v_size_503_);
v___x_527_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__8___redArg(v_a_502_, v_bkt_518_);
v___x_528_ = lean_array_uset(v_buckets_x27_524_, v___x_517_, v___x_527_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 1, v___x_528_);
lean_ctor_set(v___x_521_, 0, v___x_526_);
v___x_530_ = v___x_521_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_526_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v___x_528_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3___redArg___boxed(lean_object* v_m_535_, lean_object* v_a_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3___redArg(v_m_535_, v_a_536_);
lean_dec_ref(v_a_536_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5___redArg(lean_object* v_a_538_, lean_object* v_x_539_){
_start:
{
if (lean_obj_tag(v_x_539_) == 0)
{
lean_object* v___x_540_; 
v___x_540_ = lean_box(0);
return v___x_540_;
}
else
{
lean_object* v_key_541_; lean_object* v_value_542_; lean_object* v_tail_543_; uint8_t v___x_544_; 
v_key_541_ = lean_ctor_get(v_x_539_, 0);
v_value_542_ = lean_ctor_get(v_x_539_, 1);
v_tail_543_ = lean_ctor_get(v_x_539_, 2);
v___x_544_ = l_Lean_Syntax_instBEqRange_beq(v_key_541_, v_a_538_);
if (v___x_544_ == 0)
{
v_x_539_ = v_tail_543_;
goto _start;
}
else
{
lean_object* v___x_546_; 
lean_inc(v_value_542_);
v___x_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_546_, 0, v_value_542_);
return v___x_546_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5___redArg___boxed(lean_object* v_a_547_, lean_object* v_x_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5___redArg(v_a_547_, v_x_548_);
lean_dec(v_x_548_);
lean_dec_ref(v_a_547_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2___redArg(lean_object* v_m_550_, lean_object* v_a_551_){
_start:
{
lean_object* v_buckets_552_; lean_object* v___x_553_; uint64_t v___x_554_; uint64_t v___x_555_; uint64_t v___x_556_; uint64_t v_fold_557_; uint64_t v___x_558_; uint64_t v___x_559_; uint64_t v___x_560_; size_t v___x_561_; size_t v___x_562_; size_t v___x_563_; size_t v___x_564_; size_t v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v_buckets_552_ = lean_ctor_get(v_m_550_, 1);
v___x_553_ = lean_array_get_size(v_buckets_552_);
v___x_554_ = l_Lean_Syntax_instHashableRange_hash(v_a_551_);
v___x_555_ = 32ULL;
v___x_556_ = lean_uint64_shift_right(v___x_554_, v___x_555_);
v_fold_557_ = lean_uint64_xor(v___x_554_, v___x_556_);
v___x_558_ = 16ULL;
v___x_559_ = lean_uint64_shift_right(v_fold_557_, v___x_558_);
v___x_560_ = lean_uint64_xor(v_fold_557_, v___x_559_);
v___x_561_ = lean_uint64_to_usize(v___x_560_);
v___x_562_ = lean_usize_of_nat(v___x_553_);
v___x_563_ = ((size_t)1ULL);
v___x_564_ = lean_usize_sub(v___x_562_, v___x_563_);
v___x_565_ = lean_usize_land(v___x_561_, v___x_564_);
v___x_566_ = lean_array_uget_borrowed(v_buckets_552_, v___x_565_);
v___x_567_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5___redArg(v_a_551_, v___x_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2___redArg___boxed(lean_object* v_m_568_, lean_object* v_a_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2___redArg(v_m_568_, v_a_569_);
lean_dec_ref(v_a_569_);
lean_dec_ref(v_m_568_);
return v_res_570_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_571_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__4(void){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_572_ = lean_unsigned_to_nat(5u);
v___x_573_ = lean_unsigned_to_nat(0u);
v___x_574_ = lean_nat_mod(v___x_573_, v___x_572_);
return v___x_574_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__5(void){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_575_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__4, &l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__4_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__4);
v___x_576_ = lean_unsigned_to_nat(5u);
v___x_577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
lean_ctor_set(v___x_577_, 1, v___x_575_);
return v___x_577_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__6(void){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_578_ = lean_box(0);
v___x_579_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__5, &l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__5_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__5);
v___x_580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_580_, 0, v___x_579_);
lean_ctor_set(v___x_580_, 1, v___x_578_);
return v___x_580_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__0(void){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_581_ = lean_unsigned_to_nat(1u);
v___x_582_ = lean_unsigned_to_nat(0u);
v___x_583_ = lean_nat_mod(v___x_582_, v___x_581_);
return v___x_583_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1(void){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_584_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__0, &l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__0_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__0);
v___x_585_ = lean_unsigned_to_nat(1u);
v___x_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
lean_ctor_set(v___x_586_, 1, v___x_584_);
return v___x_586_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__7(void){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_587_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__6, &l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__6_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__6);
v___x_588_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1, &l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1);
v___x_589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_589_, 0, v___x_588_);
lean_ctor_set(v___x_589_, 1, v___x_587_);
return v___x_589_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__2(void){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_590_ = lean_unsigned_to_nat(2u);
v___x_591_ = lean_unsigned_to_nat(1u);
v___x_592_ = lean_nat_mod(v___x_591_, v___x_590_);
return v___x_592_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__3(void){
_start:
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_593_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__2, &l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__2_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__2);
v___x_594_ = lean_unsigned_to_nat(2u);
v___x_595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
lean_ctor_set(v___x_595_, 1, v___x_593_);
return v___x_595_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__8(void){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_596_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__7, &l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__7_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__7);
v___x_597_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__3, &l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__3_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__3);
v___x_598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_597_);
lean_ctor_set(v___x_598_, 1, v___x_596_);
return v___x_598_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__9(void){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_599_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__8, &l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__8_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__8);
v___x_600_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1, &l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1);
v___x_601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
lean_ctor_set(v___x_601_, 1, v___x_599_);
return v___x_601_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__11(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_604_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__9, &l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__9_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__9);
v___x_605_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1, &l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1);
v___x_606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
lean_ctor_set(v___x_606_, 1, v___x_604_);
return v___x_606_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__12(void){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_607_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__11, &l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__11_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__11);
v___x_608_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1, &l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1);
v___x_609_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
lean_ctor_set(v___x_609_, 1, v___x_607_);
return v___x_609_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__13(void){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_610_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__12, &l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__12_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__12);
v___x_611_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1, &l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1);
v___x_612_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
lean_ctor_set(v___x_612_, 1, v___x_610_);
return v___x_612_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__14(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_613_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__13, &l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__13_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__13);
v___x_614_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1, &l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1);
v___x_615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
lean_ctor_set(v___x_615_, 1, v___x_613_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg(lean_object* v_multigoals_616_, lean_object* v_x_617_, lean_object* v_a_618_){
_start:
{
switch(lean_obj_tag(v_x_617_))
{
case 0:
{
lean_object* v_t_620_; 
v_t_620_ = lean_ctor_get(v_x_617_, 1);
lean_inc_ref(v_t_620_);
lean_dec_ref_known(v_x_617_, 2);
v_x_617_ = v_t_620_;
goto _start;
}
case 1:
{
lean_object* v_i_622_; lean_object* v_children_623_; lean_object* v_snd_625_; lean_object* v_snd_629_; 
v_i_622_ = lean_ctor_get(v_x_617_, 0);
lean_inc_ref(v_i_622_);
v_children_623_ = lean_ctor_get(v_x_617_, 1);
lean_inc_ref(v_children_623_);
lean_dec_ref_known(v_x_617_, 2);
if (lean_obj_tag(v_i_622_) == 0)
{
lean_object* v_i_632_; lean_object* v_toElabInfo_633_; lean_object* v_goalsBefore_634_; lean_object* v_stx_635_; uint8_t v___x_636_; lean_object* v___x_637_; 
v_i_632_ = lean_ctor_get(v_i_622_, 0);
v_toElabInfo_633_ = lean_ctor_get(v_i_632_, 0);
v_goalsBefore_634_ = lean_ctor_get(v_i_632_, 2);
v_stx_635_ = lean_ctor_get(v_toElabInfo_633_, 1);
v___x_636_ = 1;
v___x_637_ = l_Lean_Syntax_getRange_x3f(v_stx_635_, v___x_636_);
if (lean_obj_tag(v___x_637_) == 1)
{
lean_object* v_val_638_; lean_object* v___y_640_; lean_object* v___x_642_; lean_object* v___x_643_; 
v_val_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_val_638_);
lean_dec_ref_known(v___x_637_, 1);
v___x_642_ = lean_st_ref_get(v_a_618_);
v___x_643_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2___redArg(v___x_642_, v_val_638_);
lean_dec(v___x_642_);
if (lean_obj_tag(v___x_643_) == 1)
{
lean_object* v_val_644_; lean_object* v___y_646_; uint8_t v___y_647_; lean_object* v___x_658_; lean_object* v___x_659_; uint8_t v___x_660_; lean_object* v___y_662_; uint8_t v___y_687_; 
v_val_644_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_val_644_);
lean_dec_ref_known(v___x_643_, 1);
lean_inc(v_stx_635_);
v___x_658_ = l_Lean_Syntax_getKind(v_stx_635_);
v___x_659_ = ((lean_object*)(l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__1));
v___x_660_ = lean_name_eq(v___x_658_, v___x_659_);
if (v___x_660_ == 0)
{
lean_object* v___x_689_; uint8_t v___x_690_; lean_object* v___y_692_; uint8_t v___y_708_; 
v___x_689_ = ((lean_object*)(l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__3));
v___x_690_ = lean_name_eq(v___x_658_, v___x_689_);
lean_dec(v___x_658_);
if (v___x_690_ == 0)
{
lean_object* v___x_710_; 
lean_dec(v_val_644_);
lean_dec(v_val_638_);
lean_dec_ref_known(v_i_622_, 1);
v___x_710_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___redArg(v_multigoals_616_, v_children_623_, v_a_618_);
lean_dec_ref(v_children_623_);
return v___x_710_;
}
else
{
lean_object* v___x_711_; lean_object* v___x_712_; uint8_t v___x_713_; 
v___x_711_ = l_List_lengthTR___redArg(v_goalsBefore_634_);
v___x_712_ = lean_unsigned_to_nat(1u);
v___x_713_ = lean_nat_dec_eq(v___x_711_, v___x_712_);
lean_dec(v___x_711_);
if (v___x_713_ == 0)
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; uint8_t v___x_717_; 
v___x_714_ = lean_unsigned_to_nat(0u);
v___x_715_ = l_Lean_Syntax_getArg(v_stx_635_, v___x_714_);
v___x_716_ = l_Lean_Syntax_getKind(v___x_715_);
v___x_717_ = l_Lean_NameSet_contains(v_multigoals_616_, v___x_716_);
lean_dec(v___x_716_);
if (v___x_717_ == 0)
{
v___y_708_ = v___x_690_;
goto v___jp_707_;
}
else
{
v___y_708_ = v___x_713_;
goto v___jp_707_;
}
}
else
{
goto v___jp_694_;
}
}
v___jp_691_:
{
lean_object* v___x_693_; 
v___x_693_ = lean_st_ref_take(v_a_618_);
if (lean_obj_tag(v___y_692_) == 0)
{
v___y_646_ = v___x_693_;
v___y_647_ = v___x_660_;
goto v___jp_645_;
}
else
{
v___y_646_ = v___x_693_;
v___y_647_ = v___x_690_;
goto v___jp_645_;
}
}
v___jp_694_:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_695_ = lean_unsigned_to_nat(1u);
v___x_696_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__14, &l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__14_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__14);
lean_inc_ref(v_children_623_);
v___x_697_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_getPath(v_i_622_, v_children_623_, v___x_696_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v___x_698_; 
v___x_698_ = lean_box(0);
v___y_692_ = v___x_698_;
goto v___jp_691_;
}
else
{
lean_object* v_val_699_; 
v_val_699_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_val_699_);
lean_dec_ref_known(v___x_697_, 1);
if (lean_obj_tag(v_val_699_) == 0)
{
lean_object* v_i_700_; lean_object* v_goalsAfter_701_; lean_object* v___x_702_; uint8_t v___x_703_; 
v_i_700_ = lean_ctor_get(v_val_699_, 0);
lean_inc_ref(v_i_700_);
lean_dec_ref_known(v_val_699_, 1);
v_goalsAfter_701_ = lean_ctor_get(v_i_700_, 4);
lean_inc(v_goalsAfter_701_);
lean_dec_ref(v_i_700_);
v___x_702_ = l_List_lengthTR___redArg(v_goalsAfter_701_);
lean_dec(v_goalsAfter_701_);
v___x_703_ = lean_nat_dec_eq(v___x_702_, v___x_695_);
lean_dec(v___x_702_);
if (v___x_703_ == 0)
{
lean_object* v___x_704_; 
v___x_704_ = lean_box(0);
v___y_692_ = v___x_704_;
goto v___jp_691_;
}
else
{
lean_object* v___x_705_; 
v___x_705_ = ((lean_object*)(l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__10));
v___y_692_ = v___x_705_;
goto v___jp_691_;
}
}
else
{
lean_object* v___x_706_; 
lean_dec(v_val_699_);
v___x_706_ = lean_box(0);
v___y_692_ = v___x_706_;
goto v___jp_691_;
}
}
}
v___jp_707_:
{
if (v___y_708_ == 0)
{
lean_object* v___x_709_; 
lean_dec_ref_known(v_i_622_, 1);
v___x_709_ = lean_box(0);
v___y_692_ = v___x_709_;
goto v___jp_691_;
}
else
{
goto v___jp_694_;
}
}
}
else
{
lean_object* v___x_718_; lean_object* v___x_719_; uint8_t v___x_720_; 
lean_dec(v___x_658_);
v___x_718_ = l_List_lengthTR___redArg(v_goalsBefore_634_);
v___x_719_ = lean_unsigned_to_nat(1u);
v___x_720_ = lean_nat_dec_eq(v___x_718_, v___x_719_);
lean_dec(v___x_718_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_721_ = lean_unsigned_to_nat(0u);
v___x_722_ = l_Lean_Syntax_getArg(v_stx_635_, v___x_721_);
v___x_723_ = l_Lean_Syntax_getKind(v___x_722_);
v___x_724_ = l_Lean_NameSet_contains(v_multigoals_616_, v___x_723_);
lean_dec(v___x_723_);
if (v___x_724_ == 0)
{
v___y_687_ = v___x_660_;
goto v___jp_686_;
}
else
{
v___y_687_ = v___x_720_;
goto v___jp_686_;
}
}
else
{
goto v___jp_673_;
}
}
v___jp_645_:
{
if (v___y_647_ == 0)
{
lean_object* v___x_648_; 
lean_dec(v_val_644_);
v___x_648_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3___redArg(v___y_646_, v_val_638_);
lean_dec(v_val_638_);
v_snd_629_ = v___x_648_;
goto v___jp_628_;
}
else
{
lean_object* v_stx_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_657_; 
v_stx_649_ = lean_ctor_get(v_val_644_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v_val_644_);
if (v_isSharedCheck_657_ == 0)
{
v___x_651_ = v_val_644_;
v_isShared_652_ = v_isSharedCheck_657_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_stx_649_);
lean_dec(v_val_644_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_657_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_654_; 
if (v_isShared_652_ == 0)
{
v___x_654_ = v___x_651_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_stx_649_);
v___x_654_ = v_reuseFailAlloc_656_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
lean_object* v___x_655_; 
lean_ctor_set_uint8(v___x_654_, sizeof(void*)*1, v___x_636_);
v___x_655_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4___redArg(v___y_646_, v_val_638_, v___x_654_);
v_snd_629_ = v___x_655_;
goto v___jp_628_;
}
}
}
}
v___jp_661_:
{
lean_object* v___x_663_; 
v___x_663_ = lean_st_ref_take(v_a_618_);
if (lean_obj_tag(v___y_662_) == 0)
{
lean_dec(v_val_644_);
v___y_640_ = v___x_663_;
goto v___jp_639_;
}
else
{
if (v___x_660_ == 0)
{
lean_dec(v_val_644_);
v___y_640_ = v___x_663_;
goto v___jp_639_;
}
else
{
lean_object* v_stx_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_672_; 
v_stx_664_ = lean_ctor_get(v_val_644_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v_val_644_);
if (v_isSharedCheck_672_ == 0)
{
v___x_666_ = v_val_644_;
v_isShared_667_ = v_isSharedCheck_672_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_stx_664_);
lean_dec(v_val_644_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_672_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_669_; 
if (v_isShared_667_ == 0)
{
v___x_669_ = v___x_666_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_stx_664_);
v___x_669_ = v_reuseFailAlloc_671_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
lean_object* v___x_670_; 
lean_ctor_set_uint8(v___x_669_, sizeof(void*)*1, v___x_636_);
v___x_670_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4___redArg(v___x_663_, v_val_638_, v___x_669_);
v_snd_625_ = v___x_670_;
goto v___jp_624_;
}
}
}
}
}
v___jp_673_:
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_674_ = lean_unsigned_to_nat(1u);
v___x_675_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__9, &l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__9_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__9);
lean_inc_ref(v_children_623_);
v___x_676_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_getPath(v_i_622_, v_children_623_, v___x_675_);
if (lean_obj_tag(v___x_676_) == 0)
{
lean_object* v___x_677_; 
v___x_677_ = lean_box(0);
v___y_662_ = v___x_677_;
goto v___jp_661_;
}
else
{
lean_object* v_val_678_; 
v_val_678_ = lean_ctor_get(v___x_676_, 0);
lean_inc(v_val_678_);
lean_dec_ref_known(v___x_676_, 1);
if (lean_obj_tag(v_val_678_) == 0)
{
lean_object* v_i_679_; lean_object* v_goalsAfter_680_; lean_object* v___x_681_; uint8_t v___x_682_; 
v_i_679_ = lean_ctor_get(v_val_678_, 0);
lean_inc_ref(v_i_679_);
lean_dec_ref_known(v_val_678_, 1);
v_goalsAfter_680_ = lean_ctor_get(v_i_679_, 4);
lean_inc(v_goalsAfter_680_);
lean_dec_ref(v_i_679_);
v___x_681_ = l_List_lengthTR___redArg(v_goalsAfter_680_);
lean_dec(v_goalsAfter_680_);
v___x_682_ = lean_nat_dec_eq(v___x_681_, v___x_674_);
lean_dec(v___x_681_);
if (v___x_682_ == 0)
{
lean_object* v___x_683_; 
v___x_683_ = lean_box(0);
v___y_662_ = v___x_683_;
goto v___jp_661_;
}
else
{
lean_object* v___x_684_; 
v___x_684_ = ((lean_object*)(l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__10));
v___y_662_ = v___x_684_;
goto v___jp_661_;
}
}
else
{
lean_object* v___x_685_; 
lean_dec(v_val_678_);
v___x_685_ = lean_box(0);
v___y_662_ = v___x_685_;
goto v___jp_661_;
}
}
}
v___jp_686_:
{
if (v___y_687_ == 0)
{
lean_object* v___x_688_; 
lean_dec_ref_known(v_i_622_, 1);
v___x_688_ = lean_box(0);
v___y_662_ = v___x_688_;
goto v___jp_661_;
}
else
{
goto v___jp_673_;
}
}
}
else
{
lean_object* v___x_725_; 
lean_dec(v___x_643_);
lean_dec(v_val_638_);
lean_dec_ref_known(v_i_622_, 1);
v___x_725_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___redArg(v_multigoals_616_, v_children_623_, v_a_618_);
lean_dec_ref(v_children_623_);
return v___x_725_;
}
v___jp_639_:
{
lean_object* v___x_641_; 
v___x_641_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3___redArg(v___y_640_, v_val_638_);
lean_dec(v_val_638_);
v_snd_625_ = v___x_641_;
goto v___jp_624_;
}
}
else
{
lean_object* v___x_726_; 
lean_dec(v___x_637_);
lean_dec_ref_known(v_i_622_, 1);
v___x_726_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___redArg(v_multigoals_616_, v_children_623_, v_a_618_);
lean_dec_ref(v_children_623_);
return v___x_726_;
}
}
else
{
lean_object* v___x_727_; 
lean_dec_ref(v_i_622_);
v___x_727_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___redArg(v_multigoals_616_, v_children_623_, v_a_618_);
lean_dec_ref(v_children_623_);
return v___x_727_;
}
v___jp_624_:
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = lean_st_ref_set(v_a_618_, v_snd_625_);
v___x_627_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___redArg(v_multigoals_616_, v_children_623_, v_a_618_);
lean_dec_ref(v_children_623_);
return v___x_627_;
}
v___jp_628_:
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = lean_st_ref_set(v_a_618_, v_snd_629_);
v___x_631_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___redArg(v_multigoals_616_, v_children_623_, v_a_618_);
lean_dec_ref(v_children_623_);
return v___x_631_;
}
}
default: 
{
lean_object* v___x_728_; 
lean_dec_ref_known(v_x_617_, 1);
v___x_728_ = lean_box(0);
return v___x_728_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(lean_object* v_multigoals_729_, lean_object* v_as_730_, size_t v_i_731_, size_t v_stop_732_, lean_object* v_b_733_, lean_object* v___y_734_){
_start:
{
uint8_t v___x_736_; 
v___x_736_ = lean_usize_dec_eq(v_i_731_, v_stop_732_);
if (v___x_736_ == 0)
{
lean_object* v___x_737_; lean_object* v___x_738_; size_t v___x_739_; size_t v___x_740_; 
v___x_737_ = lean_array_uget_borrowed(v_as_730_, v_i_731_);
lean_inc(v___x_737_);
v___x_738_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg(v_multigoals_729_, v___x_737_, v___y_734_);
v___x_739_ = ((size_t)1ULL);
v___x_740_ = lean_usize_add(v_i_731_, v___x_739_);
v_i_731_ = v___x_740_;
v_b_733_ = v___x_738_;
goto _start;
}
else
{
return v_b_733_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2___redArg(lean_object* v_multigoals_742_, lean_object* v_x_743_, lean_object* v___y_744_){
_start:
{
if (lean_obj_tag(v_x_743_) == 0)
{
lean_object* v_cs_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; uint8_t v___x_750_; 
v_cs_746_ = lean_ctor_get(v_x_743_, 0);
v___x_747_ = lean_unsigned_to_nat(0u);
v___x_748_ = lean_array_get_size(v_cs_746_);
v___x_749_ = lean_box(0);
v___x_750_ = lean_nat_dec_lt(v___x_747_, v___x_748_);
if (v___x_750_ == 0)
{
return v___x_749_;
}
else
{
uint8_t v___x_751_; 
v___x_751_ = lean_nat_dec_le(v___x_748_, v___x_748_);
if (v___x_751_ == 0)
{
if (v___x_750_ == 0)
{
return v___x_749_;
}
else
{
size_t v___x_752_; size_t v___x_753_; lean_object* v___x_754_; 
v___x_752_ = ((size_t)0ULL);
v___x_753_ = lean_usize_of_nat(v___x_748_);
v___x_754_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___redArg(v_multigoals_742_, v_cs_746_, v___x_752_, v___x_753_, v___x_749_, v___y_744_);
return v___x_754_;
}
}
else
{
size_t v___x_755_; size_t v___x_756_; lean_object* v___x_757_; 
v___x_755_ = ((size_t)0ULL);
v___x_756_ = lean_usize_of_nat(v___x_748_);
v___x_757_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___redArg(v_multigoals_742_, v_cs_746_, v___x_755_, v___x_756_, v___x_749_, v___y_744_);
return v___x_757_;
}
}
}
else
{
lean_object* v_vs_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; uint8_t v___x_762_; 
v_vs_758_ = lean_ctor_get(v_x_743_, 0);
v___x_759_ = lean_unsigned_to_nat(0u);
v___x_760_ = lean_array_get_size(v_vs_758_);
v___x_761_ = lean_box(0);
v___x_762_ = lean_nat_dec_lt(v___x_759_, v___x_760_);
if (v___x_762_ == 0)
{
return v___x_761_;
}
else
{
uint8_t v___x_763_; 
v___x_763_ = lean_nat_dec_le(v___x_760_, v___x_760_);
if (v___x_763_ == 0)
{
if (v___x_762_ == 0)
{
return v___x_761_;
}
else
{
size_t v___x_764_; size_t v___x_765_; lean_object* v___x_766_; 
v___x_764_ = ((size_t)0ULL);
v___x_765_ = lean_usize_of_nat(v___x_760_);
v___x_766_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_742_, v_vs_758_, v___x_764_, v___x_765_, v___x_761_, v___y_744_);
return v___x_766_;
}
}
else
{
size_t v___x_767_; size_t v___x_768_; lean_object* v___x_769_; 
v___x_767_ = ((size_t)0ULL);
v___x_768_ = lean_usize_of_nat(v___x_760_);
v___x_769_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_742_, v_vs_758_, v___x_767_, v___x_768_, v___x_761_, v___y_744_);
return v___x_769_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___redArg(lean_object* v_multigoals_770_, lean_object* v_as_771_, size_t v_i_772_, size_t v_stop_773_, lean_object* v_b_774_, lean_object* v___y_775_){
_start:
{
uint8_t v___x_777_; 
v___x_777_ = lean_usize_dec_eq(v_i_772_, v_stop_773_);
if (v___x_777_ == 0)
{
lean_object* v___x_778_; lean_object* v___x_779_; size_t v___x_780_; size_t v___x_781_; 
v___x_778_ = lean_array_uget_borrowed(v_as_771_, v_i_772_);
v___x_779_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2___redArg(v_multigoals_770_, v___x_778_, v___y_775_);
v___x_780_ = ((size_t)1ULL);
v___x_781_ = lean_usize_add(v_i_772_, v___x_780_);
v_i_772_ = v___x_781_;
v_b_774_ = v___x_779_;
goto _start;
}
else
{
return v_b_774_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg(lean_object* v_multigoals_783_, lean_object* v_x_784_, size_t v_x_785_, size_t v_x_786_, lean_object* v___y_787_){
_start:
{
if (lean_obj_tag(v_x_784_) == 0)
{
lean_object* v_cs_789_; lean_object* v___x_790_; size_t v___x_791_; lean_object* v_j_792_; lean_object* v___x_793_; size_t v___x_794_; size_t v___x_795_; size_t v___x_796_; size_t v___x_797_; size_t v___x_798_; size_t v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; uint8_t v___x_805_; 
v_cs_789_ = lean_ctor_get(v_x_784_, 0);
v___x_790_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg___closed__0);
v___x_791_ = lean_usize_shift_right(v_x_785_, v_x_786_);
v_j_792_ = lean_usize_to_nat(v___x_791_);
v___x_793_ = lean_array_get_borrowed(v___x_790_, v_cs_789_, v_j_792_);
v___x_794_ = ((size_t)1ULL);
v___x_795_ = lean_usize_shift_left(v___x_794_, v_x_786_);
v___x_796_ = lean_usize_sub(v___x_795_, v___x_794_);
v___x_797_ = lean_usize_land(v_x_785_, v___x_796_);
v___x_798_ = ((size_t)5ULL);
v___x_799_ = lean_usize_sub(v_x_786_, v___x_798_);
v___x_800_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg(v_multigoals_783_, v___x_793_, v___x_797_, v___x_799_, v___y_787_);
v___x_801_ = lean_unsigned_to_nat(1u);
v___x_802_ = lean_nat_add(v_j_792_, v___x_801_);
lean_dec(v_j_792_);
v___x_803_ = lean_array_get_size(v_cs_789_);
v___x_804_ = lean_box(0);
v___x_805_ = lean_nat_dec_lt(v___x_802_, v___x_803_);
if (v___x_805_ == 0)
{
lean_dec(v___x_802_);
return v___x_804_;
}
else
{
uint8_t v___x_806_; 
v___x_806_ = lean_nat_dec_le(v___x_803_, v___x_803_);
if (v___x_806_ == 0)
{
if (v___x_805_ == 0)
{
lean_dec(v___x_802_);
return v___x_804_;
}
else
{
size_t v___x_807_; size_t v___x_808_; lean_object* v___x_809_; 
v___x_807_ = lean_usize_of_nat(v___x_802_);
lean_dec(v___x_802_);
v___x_808_ = lean_usize_of_nat(v___x_803_);
v___x_809_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___redArg(v_multigoals_783_, v_cs_789_, v___x_807_, v___x_808_, v___x_804_, v___y_787_);
return v___x_809_;
}
}
else
{
size_t v___x_810_; size_t v___x_811_; lean_object* v___x_812_; 
v___x_810_ = lean_usize_of_nat(v___x_802_);
lean_dec(v___x_802_);
v___x_811_ = lean_usize_of_nat(v___x_803_);
v___x_812_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___redArg(v_multigoals_783_, v_cs_789_, v___x_810_, v___x_811_, v___x_804_, v___y_787_);
return v___x_812_;
}
}
}
else
{
lean_object* v_vs_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; uint8_t v___x_817_; 
v_vs_813_ = lean_ctor_get(v_x_784_, 0);
v___x_814_ = lean_usize_to_nat(v_x_785_);
v___x_815_ = lean_array_get_size(v_vs_813_);
v___x_816_ = lean_box(0);
v___x_817_ = lean_nat_dec_lt(v___x_814_, v___x_815_);
if (v___x_817_ == 0)
{
lean_dec(v___x_814_);
return v___x_816_;
}
else
{
uint8_t v___x_818_; 
v___x_818_ = lean_nat_dec_le(v___x_815_, v___x_815_);
if (v___x_818_ == 0)
{
if (v___x_817_ == 0)
{
lean_dec(v___x_814_);
return v___x_816_;
}
else
{
size_t v___x_819_; size_t v___x_820_; lean_object* v___x_821_; 
v___x_819_ = lean_usize_of_nat(v___x_814_);
lean_dec(v___x_814_);
v___x_820_ = lean_usize_of_nat(v___x_815_);
v___x_821_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_783_, v_vs_813_, v___x_819_, v___x_820_, v___x_816_, v___y_787_);
return v___x_821_;
}
}
else
{
size_t v___x_822_; size_t v___x_823_; lean_object* v___x_824_; 
v___x_822_ = lean_usize_of_nat(v___x_814_);
lean_dec(v___x_814_);
v___x_823_ = lean_usize_of_nat(v___x_815_);
v___x_824_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_783_, v_vs_813_, v___x_822_, v___x_823_, v___x_816_, v___y_787_);
return v___x_824_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2___redArg(lean_object* v_multigoals_825_, lean_object* v_t_826_, lean_object* v___y_827_){
_start:
{
lean_object* v_root_829_; lean_object* v_tail_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; uint8_t v___x_835_; 
v_root_829_ = lean_ctor_get(v_t_826_, 0);
v_tail_830_ = lean_ctor_get(v_t_826_, 1);
v___x_831_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2___redArg(v_multigoals_825_, v_root_829_, v___y_827_);
v___x_832_ = lean_unsigned_to_nat(0u);
v___x_833_ = lean_array_get_size(v_tail_830_);
v___x_834_ = lean_box(0);
v___x_835_ = lean_nat_dec_lt(v___x_832_, v___x_833_);
if (v___x_835_ == 0)
{
return v___x_834_;
}
else
{
uint8_t v___x_836_; 
v___x_836_ = lean_nat_dec_le(v___x_833_, v___x_833_);
if (v___x_836_ == 0)
{
if (v___x_835_ == 0)
{
return v___x_834_;
}
else
{
size_t v___x_837_; size_t v___x_838_; lean_object* v___x_839_; 
v___x_837_ = ((size_t)0ULL);
v___x_838_ = lean_usize_of_nat(v___x_833_);
v___x_839_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_825_, v_tail_830_, v___x_837_, v___x_838_, v___x_834_, v___y_827_);
return v___x_839_;
}
}
else
{
size_t v___x_840_; size_t v___x_841_; lean_object* v___x_842_; 
v___x_840_ = ((size_t)0ULL);
v___x_841_ = lean_usize_of_nat(v___x_833_);
v___x_842_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_825_, v_tail_830_, v___x_840_, v___x_841_, v___x_834_, v___y_827_);
return v___x_842_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0___redArg(lean_object* v_multigoals_843_, lean_object* v_t_844_, lean_object* v_start_845_, lean_object* v___y_846_){
_start:
{
lean_object* v___x_848_; uint8_t v___x_849_; 
v___x_848_ = lean_unsigned_to_nat(0u);
v___x_849_ = lean_nat_dec_eq(v_start_845_, v___x_848_);
if (v___x_849_ == 0)
{
lean_object* v_root_850_; lean_object* v_tail_851_; size_t v_shift_852_; lean_object* v_tailOff_853_; uint8_t v___x_854_; 
v_root_850_ = lean_ctor_get(v_t_844_, 0);
v_tail_851_ = lean_ctor_get(v_t_844_, 1);
v_shift_852_ = lean_ctor_get_usize(v_t_844_, 4);
v_tailOff_853_ = lean_ctor_get(v_t_844_, 3);
v___x_854_ = lean_nat_dec_le(v_tailOff_853_, v_start_845_);
if (v___x_854_ == 0)
{
size_t v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; uint8_t v___x_859_; 
v___x_855_ = lean_usize_of_nat(v_start_845_);
v___x_856_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg(v_multigoals_843_, v_root_850_, v___x_855_, v_shift_852_, v___y_846_);
v___x_857_ = lean_array_get_size(v_tail_851_);
v___x_858_ = lean_box(0);
v___x_859_ = lean_nat_dec_lt(v___x_848_, v___x_857_);
if (v___x_859_ == 0)
{
return v___x_858_;
}
else
{
uint8_t v___x_860_; 
v___x_860_ = lean_nat_dec_le(v___x_857_, v___x_857_);
if (v___x_860_ == 0)
{
if (v___x_859_ == 0)
{
return v___x_858_;
}
else
{
size_t v___x_861_; size_t v___x_862_; lean_object* v___x_863_; 
v___x_861_ = ((size_t)0ULL);
v___x_862_ = lean_usize_of_nat(v___x_857_);
v___x_863_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_843_, v_tail_851_, v___x_861_, v___x_862_, v___x_858_, v___y_846_);
return v___x_863_;
}
}
else
{
size_t v___x_864_; size_t v___x_865_; lean_object* v___x_866_; 
v___x_864_ = ((size_t)0ULL);
v___x_865_ = lean_usize_of_nat(v___x_857_);
v___x_866_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_843_, v_tail_851_, v___x_864_, v___x_865_, v___x_858_, v___y_846_);
return v___x_866_;
}
}
}
else
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; uint8_t v___x_870_; 
v___x_867_ = lean_nat_sub(v_start_845_, v_tailOff_853_);
v___x_868_ = lean_array_get_size(v_tail_851_);
v___x_869_ = lean_box(0);
v___x_870_ = lean_nat_dec_lt(v___x_867_, v___x_868_);
if (v___x_870_ == 0)
{
lean_dec(v___x_867_);
return v___x_869_;
}
else
{
uint8_t v___x_871_; 
v___x_871_ = lean_nat_dec_le(v___x_868_, v___x_868_);
if (v___x_871_ == 0)
{
if (v___x_870_ == 0)
{
lean_dec(v___x_867_);
return v___x_869_;
}
else
{
size_t v___x_872_; size_t v___x_873_; lean_object* v___x_874_; 
v___x_872_ = lean_usize_of_nat(v___x_867_);
lean_dec(v___x_867_);
v___x_873_ = lean_usize_of_nat(v___x_868_);
v___x_874_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_843_, v_tail_851_, v___x_872_, v___x_873_, v___x_869_, v___y_846_);
return v___x_874_;
}
}
else
{
size_t v___x_875_; size_t v___x_876_; lean_object* v___x_877_; 
v___x_875_ = lean_usize_of_nat(v___x_867_);
lean_dec(v___x_867_);
v___x_876_ = lean_usize_of_nat(v___x_868_);
v___x_877_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_843_, v_tail_851_, v___x_875_, v___x_876_, v___x_869_, v___y_846_);
return v___x_877_;
}
}
}
}
else
{
lean_object* v___x_878_; 
v___x_878_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2___redArg(v_multigoals_843_, v_t_844_, v___y_846_);
return v___x_878_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___redArg(lean_object* v_multigoals_879_, lean_object* v_trees_880_, lean_object* v_a_881_){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = lean_unsigned_to_nat(0u);
v___x_884_ = l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0___redArg(v_multigoals_879_, v_trees_880_, v___x_883_, v_a_881_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___redArg___boxed(lean_object* v_multigoals_885_, lean_object* v_trees_886_, lean_object* v_a_887_, lean_object* v_a_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___redArg(v_multigoals_885_, v_trees_886_, v_a_887_);
lean_dec(v_a_887_);
lean_dec_ref(v_trees_886_);
lean_dec(v_multigoals_885_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg___boxed(lean_object* v_multigoals_890_, lean_object* v_as_891_, lean_object* v_i_892_, lean_object* v_stop_893_, lean_object* v_b_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
size_t v_i_boxed_897_; size_t v_stop_boxed_898_; lean_object* v_res_899_; 
v_i_boxed_897_ = lean_unbox_usize(v_i_892_);
lean_dec(v_i_892_);
v_stop_boxed_898_ = lean_unbox_usize(v_stop_893_);
lean_dec(v_stop_893_);
v_res_899_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_890_, v_as_891_, v_i_boxed_897_, v_stop_boxed_898_, v_b_894_, v___y_895_);
lean_dec(v___y_895_);
lean_dec_ref(v_as_891_);
lean_dec(v_multigoals_890_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_multigoals_900_, lean_object* v_as_901_, lean_object* v_i_902_, lean_object* v_stop_903_, lean_object* v_b_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
size_t v_i_boxed_907_; size_t v_stop_boxed_908_; lean_object* v_res_909_; 
v_i_boxed_907_ = lean_unbox_usize(v_i_902_);
lean_dec(v_i_902_);
v_stop_boxed_908_ = lean_unbox_usize(v_stop_903_);
lean_dec(v_stop_903_);
v_res_909_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___redArg(v_multigoals_900_, v_as_901_, v_i_boxed_907_, v_stop_boxed_908_, v_b_904_, v___y_905_);
lean_dec(v___y_905_);
lean_dec_ref(v_as_901_);
lean_dec(v_multigoals_900_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2___redArg___boxed(lean_object* v_multigoals_910_, lean_object* v_t_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2___redArg(v_multigoals_910_, v_t_911_, v___y_912_);
lean_dec(v___y_912_);
lean_dec_ref(v_t_911_);
lean_dec(v_multigoals_910_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_multigoals_915_, lean_object* v_x_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2___redArg(v_multigoals_915_, v_x_916_, v___y_917_);
lean_dec(v___y_917_);
lean_dec_ref(v_x_916_);
lean_dec(v_multigoals_915_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0___redArg___boxed(lean_object* v_multigoals_920_, lean_object* v_t_921_, lean_object* v_start_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0___redArg(v_multigoals_920_, v_t_921_, v_start_922_, v___y_923_);
lean_dec(v___y_923_);
lean_dec(v_start_922_);
lean_dec_ref(v_t_921_);
lean_dec(v_multigoals_920_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg___boxed(lean_object* v_multigoals_926_, lean_object* v_x_927_, lean_object* v_x_928_, lean_object* v_x_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
size_t v_x_10205__boxed_932_; size_t v_x_10206__boxed_933_; lean_object* v_res_934_; 
v_x_10205__boxed_932_ = lean_unbox_usize(v_x_928_);
lean_dec(v_x_928_);
v_x_10206__boxed_933_ = lean_unbox_usize(v_x_929_);
lean_dec(v_x_929_);
v_res_934_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg(v_multigoals_926_, v_x_927_, v_x_10205__boxed_932_, v_x_10206__boxed_933_, v___y_930_);
lean_dec(v___y_930_);
lean_dec_ref(v_x_927_);
lean_dec(v_multigoals_926_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___boxed(lean_object* v_multigoals_935_, lean_object* v_x_936_, lean_object* v_a_937_, lean_object* v_a_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg(v_multigoals_935_, v_x_936_, v_a_937_);
lean_dec(v_a_937_);
lean_dec(v_multigoals_935_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList(lean_object* v_multigoals_940_, lean_object* v_00_u03c9_941_, lean_object* v_trees_942_, lean_object* v_a_943_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___redArg(v_multigoals_940_, v_trees_942_, v_a_943_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___boxed(lean_object* v_multigoals_946_, lean_object* v_00_u03c9_947_, lean_object* v_trees_948_, lean_object* v_a_949_, lean_object* v_a_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList(v_multigoals_946_, v_00_u03c9_947_, v_trees_948_, v_a_949_);
lean_dec(v_a_949_);
lean_dec_ref(v_trees_948_);
lean_dec(v_multigoals_946_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics(lean_object* v_multigoals_952_, lean_object* v_00_u03c9_953_, lean_object* v_x_954_, lean_object* v_a_955_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg(v_multigoals_952_, v_x_954_, v_a_955_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___boxed(lean_object* v_multigoals_958_, lean_object* v_00_u03c9_959_, lean_object* v_x_960_, lean_object* v_a_961_, lean_object* v_a_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics(v_multigoals_958_, v_00_u03c9_959_, v_x_960_, v_a_961_);
lean_dec(v_a_961_);
lean_dec(v_multigoals_958_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0(lean_object* v_00_u03c9_964_, lean_object* v_multigoals_965_, lean_object* v_t_966_, lean_object* v_start_967_, lean_object* v___y_968_){
_start:
{
lean_object* v___x_970_; 
v___x_970_ = l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0___redArg(v_multigoals_965_, v_t_966_, v_start_967_, v___y_968_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0___boxed(lean_object* v_00_u03c9_971_, lean_object* v_multigoals_972_, lean_object* v_t_973_, lean_object* v_start_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0(v_00_u03c9_971_, v_multigoals_972_, v_t_973_, v_start_974_, v___y_975_);
lean_dec(v___y_975_);
lean_dec(v_start_974_);
lean_dec_ref(v_t_973_);
lean_dec(v_multigoals_972_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2(lean_object* v_00_u03b2_978_, lean_object* v_m_979_, lean_object* v_a_980_){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2___redArg(v_m_979_, v_a_980_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2___boxed(lean_object* v_00_u03b2_982_, lean_object* v_m_983_, lean_object* v_a_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2(v_00_u03b2_982_, v_m_983_, v_a_984_);
lean_dec_ref(v_a_984_);
lean_dec_ref(v_m_983_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3(lean_object* v_00_u03b2_986_, lean_object* v_m_987_, lean_object* v_a_988_){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3___redArg(v_m_987_, v_a_988_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3___boxed(lean_object* v_00_u03b2_990_, lean_object* v_m_991_, lean_object* v_a_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3(v_00_u03b2_990_, v_m_991_, v_a_992_);
lean_dec_ref(v_a_992_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4(lean_object* v_00_u03b2_994_, lean_object* v_m_995_, lean_object* v_a_996_, lean_object* v_b_997_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4___redArg(v_m_995_, v_a_996_, v_b_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0(lean_object* v_00_u03c9_999_, lean_object* v_multigoals_1000_, lean_object* v_x_1001_, size_t v_x_1002_, size_t v_x_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg(v_multigoals_1000_, v_x_1001_, v_x_1002_, v_x_1003_, v___y_1004_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___boxed(lean_object* v_00_u03c9_1007_, lean_object* v_multigoals_1008_, lean_object* v_x_1009_, lean_object* v_x_1010_, lean_object* v_x_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
size_t v_x_10720__boxed_1014_; size_t v_x_10721__boxed_1015_; lean_object* v_res_1016_; 
v_x_10720__boxed_1014_ = lean_unbox_usize(v_x_1010_);
lean_dec(v_x_1010_);
v_x_10721__boxed_1015_ = lean_unbox_usize(v_x_1011_);
lean_dec(v_x_1011_);
v_res_1016_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0(v_00_u03c9_1007_, v_multigoals_1008_, v_x_1009_, v_x_10720__boxed_1014_, v_x_10721__boxed_1015_, v___y_1012_);
lean_dec(v___y_1012_);
lean_dec_ref(v_x_1009_);
lean_dec(v_multigoals_1008_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1(lean_object* v_00_u03c9_1017_, lean_object* v_multigoals_1018_, lean_object* v_as_1019_, size_t v_i_1020_, size_t v_stop_1021_, lean_object* v_b_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_1018_, v_as_1019_, v_i_1020_, v_stop_1021_, v_b_1022_, v___y_1023_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___boxed(lean_object* v_00_u03c9_1026_, lean_object* v_multigoals_1027_, lean_object* v_as_1028_, lean_object* v_i_1029_, lean_object* v_stop_1030_, lean_object* v_b_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
size_t v_i_boxed_1034_; size_t v_stop_boxed_1035_; lean_object* v_res_1036_; 
v_i_boxed_1034_ = lean_unbox_usize(v_i_1029_);
lean_dec(v_i_1029_);
v_stop_boxed_1035_ = lean_unbox_usize(v_stop_1030_);
lean_dec(v_stop_1030_);
v_res_1036_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1(v_00_u03c9_1026_, v_multigoals_1027_, v_as_1028_, v_i_boxed_1034_, v_stop_boxed_1035_, v_b_1031_, v___y_1032_);
lean_dec(v___y_1032_);
lean_dec_ref(v_as_1028_);
lean_dec(v_multigoals_1027_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2(lean_object* v_00_u03c9_1037_, lean_object* v_multigoals_1038_, lean_object* v_t_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2___redArg(v_multigoals_1038_, v_t_1039_, v___y_1040_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2___boxed(lean_object* v_00_u03c9_1043_, lean_object* v_multigoals_1044_, lean_object* v_t_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2(v_00_u03c9_1043_, v_multigoals_1044_, v_t_1045_, v___y_1046_);
lean_dec(v___y_1046_);
lean_dec_ref(v_t_1045_);
lean_dec(v_multigoals_1044_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5(lean_object* v_00_u03b2_1049_, lean_object* v_a_1050_, lean_object* v_x_1051_){
_start:
{
lean_object* v___x_1052_; 
v___x_1052_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5___redArg(v_a_1050_, v_x_1051_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1053_, lean_object* v_a_1054_, lean_object* v_x_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5(v_00_u03b2_1053_, v_a_1054_, v_x_1055_);
lean_dec(v_x_1055_);
lean_dec_ref(v_a_1054_);
return v_res_1056_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__7(lean_object* v_00_u03b2_1057_, lean_object* v_a_1058_, lean_object* v_x_1059_){
_start:
{
uint8_t v___x_1060_; 
v___x_1060_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__7___redArg(v_a_1058_, v_x_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__7___boxed(lean_object* v_00_u03b2_1061_, lean_object* v_a_1062_, lean_object* v_x_1063_){
_start:
{
uint8_t v_res_1064_; lean_object* v_r_1065_; 
v_res_1064_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__7(v_00_u03b2_1061_, v_a_1062_, v_x_1063_);
lean_dec(v_x_1063_);
lean_dec_ref(v_a_1062_);
v_r_1065_ = lean_box(v_res_1064_);
return v_r_1065_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__8(lean_object* v_00_u03b2_1066_, lean_object* v_a_1067_, lean_object* v_x_1068_){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__8___redArg(v_a_1067_, v_x_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__8___boxed(lean_object* v_00_u03b2_1070_, lean_object* v_a_1071_, lean_object* v_x_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__8(v_00_u03b2_1070_, v_a_1071_, v_x_1072_);
lean_dec_ref(v_a_1071_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10(lean_object* v_00_u03b2_1074_, lean_object* v_data_1075_){
_start:
{
lean_object* v___x_1076_; 
v___x_1076_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10___redArg(v_data_1075_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__11(lean_object* v_00_u03b2_1077_, lean_object* v_a_1078_, lean_object* v_b_1079_, lean_object* v_x_1080_){
_start:
{
lean_object* v___x_1081_; 
v___x_1081_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__11___redArg(v_a_1078_, v_b_1079_, v_x_1080_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2(lean_object* v_00_u03c9_1082_, lean_object* v_multigoals_1083_, lean_object* v_x_1084_, lean_object* v___y_1085_){
_start:
{
lean_object* v___x_1087_; 
v___x_1087_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2___redArg(v_multigoals_1083_, v_x_1084_, v___y_1085_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03c9_1088_, lean_object* v_multigoals_1089_, lean_object* v_x_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2(v_00_u03c9_1088_, v_multigoals_1089_, v_x_1090_, v___y_1091_);
lean_dec(v___y_1091_);
lean_dec_ref(v_x_1090_);
lean_dec(v_multigoals_1089_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3(lean_object* v_00_u03c9_1094_, lean_object* v_multigoals_1095_, lean_object* v_as_1096_, size_t v_i_1097_, size_t v_stop_1098_, lean_object* v_b_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v___x_1102_; 
v___x_1102_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___redArg(v_multigoals_1095_, v_as_1096_, v_i_1097_, v_stop_1098_, v_b_1099_, v___y_1100_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03c9_1103_, lean_object* v_multigoals_1104_, lean_object* v_as_1105_, lean_object* v_i_1106_, lean_object* v_stop_1107_, lean_object* v_b_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
size_t v_i_boxed_1111_; size_t v_stop_boxed_1112_; lean_object* v_res_1113_; 
v_i_boxed_1111_ = lean_unbox_usize(v_i_1106_);
lean_dec(v_i_1106_);
v_stop_boxed_1112_ = lean_unbox_usize(v_stop_1107_);
lean_dec(v_stop_1107_);
v_res_1113_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3(v_00_u03c9_1103_, v_multigoals_1104_, v_as_1105_, v_i_boxed_1111_, v_stop_boxed_1112_, v_b_1108_, v___y_1109_);
lean_dec(v___y_1109_);
lean_dec_ref(v_as_1105_);
lean_dec(v_multigoals_1104_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10_spec__13(lean_object* v_00_u03b2_1114_, lean_object* v_i_1115_, lean_object* v_source_1116_, lean_object* v_target_1117_){
_start:
{
lean_object* v___x_1118_; 
v___x_1118_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10_spec__13___redArg(v_i_1115_, v_source_1116_, v_target_1117_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10_spec__13_spec__14(lean_object* v_00_u03b2_1119_, lean_object* v_x_1120_, lean_object* v_x_1121_){
_start:
{
lean_object* v___x_1122_; 
v___x_1122_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10_spec__13_spec__14___redArg(v_x_1120_, v_x_1121_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__0(lean_object* v_a_1123_){
_start:
{
lean_object* v___x_1124_; 
v___x_1124_ = lean_nat_to_int(v_a_1123_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3___redArg(lean_object* v___y_1125_){
_start:
{
lean_object* v___x_1127_; lean_object* v_infoState_1128_; lean_object* v_trees_1129_; lean_object* v___x_1130_; 
v___x_1127_ = lean_st_ref_get(v___y_1125_);
v_infoState_1128_ = lean_ctor_get(v___x_1127_, 8);
lean_inc_ref(v_infoState_1128_);
lean_dec(v___x_1127_);
v_trees_1129_ = lean_ctor_get(v_infoState_1128_, 2);
lean_inc_ref(v_trees_1129_);
lean_dec_ref(v_infoState_1128_);
v___x_1130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1130_, 0, v_trees_1129_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3___redArg___boxed(lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3___redArg(v___y_1131_);
lean_dec(v___y_1131_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3(lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v___x_1137_; 
v___x_1137_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3___redArg(v___y_1135_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3___boxed(lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3(v___y_1138_, v___y_1139_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
return v_res_1141_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1142_ = lean_box(0);
v___x_1143_ = lean_unsigned_to_nat(16u);
v___x_1144_ = lean_mk_array(v___x_1143_, v___x_1142_);
return v___x_1144_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1145_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__0, &l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__0_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__0);
v___x_1146_ = lean_unsigned_to_nat(0u);
v___x_1147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1146_);
lean_ctor_set(v___x_1147_, 1, v___x_1145_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0(lean_object* v_stx_1148_, lean_object* v_val_1149_, lean_object* v_a_1150_, lean_object* v_x_1151_){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1153_ = lean_obj_once(&l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__1, &l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__1_once, _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__1);
v___x_1154_ = lean_st_mk_ref(v___x_1153_);
v___x_1155_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg(v_stx_1148_, v___x_1154_);
v___x_1156_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___redArg(v_val_1149_, v_a_1150_, v___x_1154_);
v___x_1157_ = lean_st_ref_get(v___x_1154_);
lean_dec(v___x_1154_);
v___x_1158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1156_);
lean_ctor_set(v___x_1158_, 1, v___x_1157_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___boxed(lean_object* v_stx_1159_, lean_object* v_val_1160_, lean_object* v_a_1161_, lean_object* v_x_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0(v_stx_1159_, v_val_1160_, v_a_1161_, v_x_1162_);
lean_dec_ref(v_a_1161_);
lean_dec(v_val_1160_);
return v_res_1164_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___lam__0(uint8_t v___y_1166_, uint8_t v_suppressElabErrors_1167_, lean_object* v_x_1168_){
_start:
{
if (lean_obj_tag(v_x_1168_) == 1)
{
lean_object* v_pre_1169_; 
v_pre_1169_ = lean_ctor_get(v_x_1168_, 0);
if (lean_obj_tag(v_pre_1169_) == 0)
{
lean_object* v_str_1170_; lean_object* v___x_1171_; uint8_t v___x_1172_; 
v_str_1170_ = lean_ctor_get(v_x_1168_, 1);
v___x_1171_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___lam__0___closed__0));
v___x_1172_ = lean_string_dec_eq(v_str_1170_, v___x_1171_);
if (v___x_1172_ == 0)
{
return v___y_1166_;
}
else
{
return v_suppressElabErrors_1167_;
}
}
else
{
return v___y_1166_;
}
}
else
{
return v___y_1166_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___lam__0___boxed(lean_object* v___y_1173_, lean_object* v_suppressElabErrors_1174_, lean_object* v_x_1175_){
_start:
{
uint8_t v___y_8654__boxed_1176_; uint8_t v_suppressElabErrors_boxed_1177_; uint8_t v_res_1178_; lean_object* v_r_1179_; 
v___y_8654__boxed_1176_ = lean_unbox(v___y_1173_);
v_suppressElabErrors_boxed_1177_ = lean_unbox(v_suppressElabErrors_1174_);
v_res_1178_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___lam__0(v___y_8654__boxed_1176_, v_suppressElabErrors_boxed_1177_, v_x_1175_);
lean_dec(v_x_1175_);
v_r_1179_ = lean_box(v_res_1178_);
return v_r_1179_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__13(lean_object* v_opts_1180_, lean_object* v_opt_1181_){
_start:
{
lean_object* v_name_1182_; lean_object* v_defValue_1183_; lean_object* v_map_1184_; lean_object* v___x_1185_; 
v_name_1182_ = lean_ctor_get(v_opt_1181_, 0);
v_defValue_1183_ = lean_ctor_get(v_opt_1181_, 1);
v_map_1184_ = lean_ctor_get(v_opts_1180_, 0);
v___x_1185_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1184_, v_name_1182_);
if (lean_obj_tag(v___x_1185_) == 0)
{
uint8_t v___x_1186_; 
v___x_1186_ = lean_unbox(v_defValue_1183_);
return v___x_1186_;
}
else
{
lean_object* v_val_1187_; 
v_val_1187_ = lean_ctor_get(v___x_1185_, 0);
lean_inc(v_val_1187_);
lean_dec_ref_known(v___x_1185_, 1);
if (lean_obj_tag(v_val_1187_) == 1)
{
uint8_t v_v_1188_; 
v_v_1188_ = lean_ctor_get_uint8(v_val_1187_, 0);
lean_dec_ref_known(v_val_1187_, 0);
return v_v_1188_;
}
else
{
uint8_t v___x_1189_; 
lean_dec(v_val_1187_);
v___x_1189_ = lean_unbox(v_defValue_1183_);
return v___x_1189_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__13___boxed(lean_object* v_opts_1190_, lean_object* v_opt_1191_){
_start:
{
uint8_t v_res_1192_; lean_object* v_r_1193_; 
v_res_1192_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__13(v_opts_1190_, v_opt_1191_);
lean_dec_ref(v_opt_1191_);
lean_dec_ref(v_opts_1190_);
v_r_1193_ = lean_box(v_res_1192_);
return v_r_1193_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_1194_; 
v___x_1194_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1194_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1195_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__0);
v___x_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
return v___x_1196_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1197_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__1);
v___x_1198_ = lean_unsigned_to_nat(0u);
v___x_1199_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
lean_ctor_set(v___x_1199_, 1, v___x_1198_);
lean_ctor_set(v___x_1199_, 2, v___x_1198_);
lean_ctor_set(v___x_1199_, 3, v___x_1198_);
lean_ctor_set(v___x_1199_, 4, v___x_1197_);
lean_ctor_set(v___x_1199_, 5, v___x_1197_);
lean_ctor_set(v___x_1199_, 6, v___x_1197_);
lean_ctor_set(v___x_1199_, 7, v___x_1197_);
lean_ctor_set(v___x_1199_, 8, v___x_1197_);
lean_ctor_set(v___x_1199_, 9, v___x_1197_);
return v___x_1199_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__3(void){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1200_ = lean_unsigned_to_nat(32u);
v___x_1201_ = lean_mk_empty_array_with_capacity(v___x_1200_);
v___x_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1201_);
return v___x_1202_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__4(void){
_start:
{
size_t v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1203_ = ((size_t)5ULL);
v___x_1204_ = lean_unsigned_to_nat(0u);
v___x_1205_ = lean_unsigned_to_nat(32u);
v___x_1206_ = lean_mk_empty_array_with_capacity(v___x_1205_);
v___x_1207_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__3);
v___x_1208_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
lean_ctor_set(v___x_1208_, 1, v___x_1206_);
lean_ctor_set(v___x_1208_, 2, v___x_1204_);
lean_ctor_set(v___x_1208_, 3, v___x_1204_);
lean_ctor_set_usize(v___x_1208_, 4, v___x_1203_);
return v___x_1208_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__5(void){
_start:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1209_ = lean_box(1);
v___x_1210_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__4);
v___x_1211_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__1);
v___x_1212_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1211_);
lean_ctor_set(v___x_1212_, 1, v___x_1210_);
lean_ctor_set(v___x_1212_, 2, v___x_1209_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg(lean_object* v_msgData_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v___x_1216_; lean_object* v_env_1217_; lean_object* v___x_1218_; lean_object* v_scopes_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v_opts_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1216_ = lean_st_ref_get(v___y_1214_);
v_env_1217_ = lean_ctor_get(v___x_1216_, 0);
lean_inc_ref(v_env_1217_);
lean_dec(v___x_1216_);
v___x_1218_ = lean_st_ref_get(v___y_1214_);
v_scopes_1219_ = lean_ctor_get(v___x_1218_, 2);
lean_inc(v_scopes_1219_);
lean_dec(v___x_1218_);
v___x_1220_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1221_ = l_List_head_x21___redArg(v___x_1220_, v_scopes_1219_);
lean_dec(v_scopes_1219_);
v_opts_1222_ = lean_ctor_get(v___x_1221_, 1);
lean_inc_ref(v_opts_1222_);
lean_dec(v___x_1221_);
v___x_1223_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__2);
v___x_1224_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__5);
v___x_1225_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1225_, 0, v_env_1217_);
lean_ctor_set(v___x_1225_, 1, v___x_1223_);
lean_ctor_set(v___x_1225_, 2, v___x_1224_);
lean_ctor_set(v___x_1225_, 3, v_opts_1222_);
v___x_1226_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
lean_ctor_set(v___x_1226_, 1, v_msgData_1213_);
v___x_1227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___boxed(lean_object* v_msgData_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg(v_msgData_1228_, v___y_1229_);
lean_dec(v___y_1229_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10(lean_object* v_ref_1233_, lean_object* v_msgData_1234_, uint8_t v_severity_1235_, uint8_t v_isSilent_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
lean_object* v___y_1241_; lean_object* v___y_1242_; uint8_t v___y_1243_; lean_object* v___y_1244_; uint8_t v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; uint8_t v___y_1304_; lean_object* v___y_1305_; uint8_t v___y_1306_; uint8_t v___y_1307_; lean_object* v___y_1308_; uint8_t v___y_1332_; lean_object* v___y_1333_; uint8_t v___y_1334_; uint8_t v___y_1335_; lean_object* v___y_1336_; uint8_t v___y_1340_; uint8_t v___y_1341_; uint8_t v___y_1342_; uint8_t v___x_1357_; uint8_t v___y_1359_; uint8_t v___y_1360_; uint8_t v___y_1361_; uint8_t v___y_1363_; uint8_t v___x_1375_; 
v___x_1357_ = 2;
v___x_1375_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1235_, v___x_1357_);
if (v___x_1375_ == 0)
{
v___y_1363_ = v___x_1375_;
goto v___jp_1362_;
}
else
{
uint8_t v___x_1376_; 
lean_inc_ref(v_msgData_1234_);
v___x_1376_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1234_);
v___y_1363_ = v___x_1376_;
goto v___jp_1362_;
}
v___jp_1240_:
{
lean_object* v___x_1249_; 
v___x_1249_ = l_Lean_Elab_Command_getScope___redArg(v___y_1248_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v_a_1250_; lean_object* v___x_1251_; 
v_a_1250_ = lean_ctor_get(v___x_1249_, 0);
lean_inc(v_a_1250_);
lean_dec_ref_known(v___x_1249_, 1);
v___x_1251_ = l_Lean_Elab_Command_getScope___redArg(v___y_1248_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v_a_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1286_; 
v_a_1252_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1254_ = v___x_1251_;
v_isShared_1255_ = v_isSharedCheck_1286_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_a_1252_);
lean_dec(v___x_1251_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1286_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1256_; lean_object* v_currNamespace_1257_; lean_object* v_openDecls_1258_; lean_object* v_env_1259_; lean_object* v_messages_1260_; lean_object* v_scopes_1261_; lean_object* v_usedQuotCtxts_1262_; lean_object* v_nextMacroScope_1263_; lean_object* v_maxRecDepth_1264_; lean_object* v_ngen_1265_; lean_object* v_auxDeclNGen_1266_; lean_object* v_infoState_1267_; lean_object* v_traceState_1268_; lean_object* v_snapshotTasks_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1285_; 
v___x_1256_ = lean_st_ref_take(v___y_1248_);
v_currNamespace_1257_ = lean_ctor_get(v_a_1250_, 2);
lean_inc(v_currNamespace_1257_);
lean_dec(v_a_1250_);
v_openDecls_1258_ = lean_ctor_get(v_a_1252_, 3);
lean_inc(v_openDecls_1258_);
lean_dec(v_a_1252_);
v_env_1259_ = lean_ctor_get(v___x_1256_, 0);
v_messages_1260_ = lean_ctor_get(v___x_1256_, 1);
v_scopes_1261_ = lean_ctor_get(v___x_1256_, 2);
v_usedQuotCtxts_1262_ = lean_ctor_get(v___x_1256_, 3);
v_nextMacroScope_1263_ = lean_ctor_get(v___x_1256_, 4);
v_maxRecDepth_1264_ = lean_ctor_get(v___x_1256_, 5);
v_ngen_1265_ = lean_ctor_get(v___x_1256_, 6);
v_auxDeclNGen_1266_ = lean_ctor_get(v___x_1256_, 7);
v_infoState_1267_ = lean_ctor_get(v___x_1256_, 8);
v_traceState_1268_ = lean_ctor_get(v___x_1256_, 9);
v_snapshotTasks_1269_ = lean_ctor_get(v___x_1256_, 10);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1271_ = v___x_1256_;
v_isShared_1272_ = v_isSharedCheck_1285_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_snapshotTasks_1269_);
lean_inc(v_traceState_1268_);
lean_inc(v_infoState_1267_);
lean_inc(v_auxDeclNGen_1266_);
lean_inc(v_ngen_1265_);
lean_inc(v_maxRecDepth_1264_);
lean_inc(v_nextMacroScope_1263_);
lean_inc(v_usedQuotCtxts_1262_);
lean_inc(v_scopes_1261_);
lean_inc(v_messages_1260_);
lean_inc(v_env_1259_);
lean_dec(v___x_1256_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1285_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1278_; 
v___x_1273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1273_, 0, v_currNamespace_1257_);
lean_ctor_set(v___x_1273_, 1, v_openDecls_1258_);
v___x_1274_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1273_);
lean_ctor_set(v___x_1274_, 1, v___y_1244_);
lean_inc_ref(v___y_1241_);
lean_inc_ref(v___y_1246_);
v___x_1275_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1275_, 0, v___y_1246_);
lean_ctor_set(v___x_1275_, 1, v___y_1247_);
lean_ctor_set(v___x_1275_, 2, v___y_1242_);
lean_ctor_set(v___x_1275_, 3, v___y_1241_);
lean_ctor_set(v___x_1275_, 4, v___x_1274_);
lean_ctor_set_uint8(v___x_1275_, sizeof(void*)*5, v___y_1243_);
lean_ctor_set_uint8(v___x_1275_, sizeof(void*)*5 + 1, v___y_1245_);
lean_ctor_set_uint8(v___x_1275_, sizeof(void*)*5 + 2, v_isSilent_1236_);
v___x_1276_ = l_Lean_MessageLog_add(v___x_1275_, v_messages_1260_);
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 1, v___x_1276_);
v___x_1278_ = v___x_1271_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_env_1259_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v___x_1276_);
lean_ctor_set(v_reuseFailAlloc_1284_, 2, v_scopes_1261_);
lean_ctor_set(v_reuseFailAlloc_1284_, 3, v_usedQuotCtxts_1262_);
lean_ctor_set(v_reuseFailAlloc_1284_, 4, v_nextMacroScope_1263_);
lean_ctor_set(v_reuseFailAlloc_1284_, 5, v_maxRecDepth_1264_);
lean_ctor_set(v_reuseFailAlloc_1284_, 6, v_ngen_1265_);
lean_ctor_set(v_reuseFailAlloc_1284_, 7, v_auxDeclNGen_1266_);
lean_ctor_set(v_reuseFailAlloc_1284_, 8, v_infoState_1267_);
lean_ctor_set(v_reuseFailAlloc_1284_, 9, v_traceState_1268_);
lean_ctor_set(v_reuseFailAlloc_1284_, 10, v_snapshotTasks_1269_);
v___x_1278_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1282_; 
v___x_1279_ = lean_st_ref_set(v___y_1248_, v___x_1278_);
v___x_1280_ = lean_box(0);
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 0, v___x_1280_);
v___x_1282_ = v___x_1254_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1280_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
}
}
else
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
lean_dec(v_a_1250_);
lean_dec_ref(v___y_1247_);
lean_dec_ref(v___y_1244_);
lean_dec(v___y_1242_);
v_a_1287_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1289_ = v___x_1251_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1251_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1287_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
else
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
lean_dec_ref(v___y_1247_);
lean_dec_ref(v___y_1244_);
lean_dec(v___y_1242_);
v_a_1295_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1297_ = v___x_1249_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1249_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_a_1295_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
v___jp_1303_:
{
lean_object* v_fileName_1309_; lean_object* v_fileMap_1310_; uint8_t v_suppressElabErrors_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1330_; 
v_fileName_1309_ = lean_ctor_get(v___y_1237_, 0);
v_fileMap_1310_ = lean_ctor_get(v___y_1237_, 1);
v_suppressElabErrors_1311_ = lean_ctor_get_uint8(v___y_1237_, sizeof(void*)*10);
v___x_1312_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1234_);
v___x_1313_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg(v___x_1312_, v___y_1238_);
v_a_1314_ = lean_ctor_get(v___x_1313_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1316_ = v___x_1313_;
v_isShared_1317_ = v_isSharedCheck_1330_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v___x_1313_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1330_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
lean_inc_ref_n(v_fileMap_1310_, 2);
v___x_1318_ = l_Lean_FileMap_toPosition(v_fileMap_1310_, v___y_1305_);
lean_dec(v___y_1305_);
v___x_1319_ = l_Lean_FileMap_toPosition(v_fileMap_1310_, v___y_1308_);
lean_dec(v___y_1308_);
v___x_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
v___x_1321_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___closed__0));
if (v_suppressElabErrors_1311_ == 0)
{
lean_del_object(v___x_1316_);
v___y_1241_ = v___x_1321_;
v___y_1242_ = v___x_1320_;
v___y_1243_ = v___y_1306_;
v___y_1244_ = v_a_1314_;
v___y_1245_ = v___y_1307_;
v___y_1246_ = v_fileName_1309_;
v___y_1247_ = v___x_1318_;
v___y_1248_ = v___y_1238_;
goto v___jp_1240_;
}
else
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___f_1324_; uint8_t v___x_1325_; 
v___x_1322_ = lean_box(v___y_1304_);
v___x_1323_ = lean_box(v_suppressElabErrors_1311_);
v___f_1324_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1324_, 0, v___x_1322_);
lean_closure_set(v___f_1324_, 1, v___x_1323_);
lean_inc(v_a_1314_);
v___x_1325_ = l_Lean_MessageData_hasTag(v___f_1324_, v_a_1314_);
if (v___x_1325_ == 0)
{
lean_object* v___x_1326_; lean_object* v___x_1328_; 
lean_dec_ref_known(v___x_1320_, 1);
lean_dec_ref(v___x_1318_);
lean_dec(v_a_1314_);
v___x_1326_ = lean_box(0);
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 0, v___x_1326_);
v___x_1328_ = v___x_1316_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v___x_1326_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
else
{
lean_del_object(v___x_1316_);
v___y_1241_ = v___x_1321_;
v___y_1242_ = v___x_1320_;
v___y_1243_ = v___y_1306_;
v___y_1244_ = v_a_1314_;
v___y_1245_ = v___y_1307_;
v___y_1246_ = v_fileName_1309_;
v___y_1247_ = v___x_1318_;
v___y_1248_ = v___y_1238_;
goto v___jp_1240_;
}
}
}
}
v___jp_1331_:
{
lean_object* v___x_1337_; 
v___x_1337_ = l_Lean_Syntax_getTailPos_x3f(v___y_1333_, v___y_1334_);
lean_dec(v___y_1333_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_inc(v___y_1336_);
v___y_1304_ = v___y_1332_;
v___y_1305_ = v___y_1336_;
v___y_1306_ = v___y_1334_;
v___y_1307_ = v___y_1335_;
v___y_1308_ = v___y_1336_;
goto v___jp_1303_;
}
else
{
lean_object* v_val_1338_; 
v_val_1338_ = lean_ctor_get(v___x_1337_, 0);
lean_inc(v_val_1338_);
lean_dec_ref_known(v___x_1337_, 1);
v___y_1304_ = v___y_1332_;
v___y_1305_ = v___y_1336_;
v___y_1306_ = v___y_1334_;
v___y_1307_ = v___y_1335_;
v___y_1308_ = v_val_1338_;
goto v___jp_1303_;
}
}
v___jp_1339_:
{
lean_object* v___x_1343_; 
v___x_1343_ = l_Lean_Elab_Command_getRef___redArg(v___y_1237_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v_a_1344_; lean_object* v_ref_1345_; lean_object* v___x_1346_; 
v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
lean_inc(v_a_1344_);
lean_dec_ref_known(v___x_1343_, 1);
v_ref_1345_ = l_Lean_replaceRef(v_ref_1233_, v_a_1344_);
lean_dec(v_a_1344_);
v___x_1346_ = l_Lean_Syntax_getPos_x3f(v_ref_1345_, v___y_1341_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v___x_1347_; 
v___x_1347_ = lean_unsigned_to_nat(0u);
v___y_1332_ = v___y_1340_;
v___y_1333_ = v_ref_1345_;
v___y_1334_ = v___y_1341_;
v___y_1335_ = v___y_1342_;
v___y_1336_ = v___x_1347_;
goto v___jp_1331_;
}
else
{
lean_object* v_val_1348_; 
v_val_1348_ = lean_ctor_get(v___x_1346_, 0);
lean_inc(v_val_1348_);
lean_dec_ref_known(v___x_1346_, 1);
v___y_1332_ = v___y_1340_;
v___y_1333_ = v_ref_1345_;
v___y_1334_ = v___y_1341_;
v___y_1335_ = v___y_1342_;
v___y_1336_ = v_val_1348_;
goto v___jp_1331_;
}
}
else
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1356_; 
lean_dec_ref(v_msgData_1234_);
v_a_1349_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1351_ = v___x_1343_;
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1343_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1354_; 
if (v_isShared_1352_ == 0)
{
v___x_1354_ = v___x_1351_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_a_1349_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
v___jp_1358_:
{
if (v___y_1361_ == 0)
{
v___y_1340_ = v___y_1359_;
v___y_1341_ = v___y_1360_;
v___y_1342_ = v_severity_1235_;
goto v___jp_1339_;
}
else
{
v___y_1340_ = v___y_1359_;
v___y_1341_ = v___y_1360_;
v___y_1342_ = v___x_1357_;
goto v___jp_1339_;
}
}
v___jp_1362_:
{
if (v___y_1363_ == 0)
{
lean_object* v___x_1364_; lean_object* v_scopes_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v_opts_1368_; uint8_t v___x_1369_; uint8_t v___x_1370_; 
v___x_1364_ = lean_st_ref_get(v___y_1238_);
v_scopes_1365_ = lean_ctor_get(v___x_1364_, 2);
lean_inc(v_scopes_1365_);
lean_dec(v___x_1364_);
v___x_1366_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1367_ = l_List_head_x21___redArg(v___x_1366_, v_scopes_1365_);
lean_dec(v_scopes_1365_);
v_opts_1368_ = lean_ctor_get(v___x_1367_, 1);
lean_inc_ref(v_opts_1368_);
lean_dec(v___x_1367_);
v___x_1369_ = 1;
v___x_1370_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1235_, v___x_1369_);
if (v___x_1370_ == 0)
{
lean_dec_ref(v_opts_1368_);
v___y_1359_ = v___y_1363_;
v___y_1360_ = v___y_1363_;
v___y_1361_ = v___x_1370_;
goto v___jp_1358_;
}
else
{
lean_object* v___x_1371_; uint8_t v___x_1372_; 
v___x_1371_ = l_Lean_warningAsError;
v___x_1372_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__13(v_opts_1368_, v___x_1371_);
lean_dec_ref(v_opts_1368_);
v___y_1359_ = v___y_1363_;
v___y_1360_ = v___y_1363_;
v___y_1361_ = v___x_1372_;
goto v___jp_1358_;
}
}
else
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
lean_dec_ref(v_msgData_1234_);
v___x_1373_ = lean_box(0);
v___x_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1373_);
return v___x_1374_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___boxed(lean_object* v_ref_1377_, lean_object* v_msgData_1378_, lean_object* v_severity_1379_, lean_object* v_isSilent_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
uint8_t v_severity_boxed_1384_; uint8_t v_isSilent_boxed_1385_; lean_object* v_res_1386_; 
v_severity_boxed_1384_ = lean_unbox(v_severity_1379_);
v_isSilent_boxed_1385_ = lean_unbox(v_isSilent_1380_);
v_res_1386_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10(v_ref_1377_, v_msgData_1378_, v_severity_boxed_1384_, v_isSilent_boxed_1385_, v___y_1381_, v___y_1382_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec(v_ref_1377_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5(lean_object* v_ref_1387_, lean_object* v_msgData_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
uint8_t v___x_1392_; uint8_t v___x_1393_; lean_object* v___x_1394_; 
v___x_1392_ = 1;
v___x_1393_ = 0;
v___x_1394_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10(v_ref_1387_, v_msgData_1388_, v___x_1392_, v___x_1393_, v___y_1389_, v___y_1390_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5___boxed(lean_object* v_ref_1395_, lean_object* v_msgData_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5(v_ref_1395_, v_msgData_1396_, v___y_1397_, v___y_1398_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
lean_dec(v_ref_1395_);
return v_res_1400_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1402_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__0));
v___x_1403_ = l_Lean_stringToMessageData(v___x_1402_);
return v___x_1403_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1405_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__2));
v___x_1406_ = l_Lean_stringToMessageData(v___x_1405_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3(lean_object* v_linterOption_1407_, lean_object* v_stx_1408_, lean_object* v_msg_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
lean_object* v_name_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1431_; 
v_name_1413_ = lean_ctor_get(v_linterOption_1407_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v_linterOption_1407_);
if (v_isSharedCheck_1431_ == 0)
{
lean_object* v_unused_1432_; 
v_unused_1432_ = lean_ctor_get(v_linterOption_1407_, 1);
lean_dec(v_unused_1432_);
v___x_1415_ = v_linterOption_1407_;
v_isShared_1416_ = v_isSharedCheck_1431_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_name_1413_);
lean_dec(v_linterOption_1407_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1431_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1420_; 
v___x_1417_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__1);
lean_inc(v_name_1413_);
v___x_1418_ = l_Lean_MessageData_ofName(v_name_1413_);
if (v_isShared_1416_ == 0)
{
lean_ctor_set_tag(v___x_1415_, 7);
lean_ctor_set(v___x_1415_, 1, v___x_1418_);
lean_ctor_set(v___x_1415_, 0, v___x_1417_);
v___x_1420_ = v___x_1415_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v___x_1417_);
lean_ctor_set(v_reuseFailAlloc_1430_, 1, v___x_1418_);
v___x_1420_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v_disable_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1421_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__3);
v___x_1422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1420_);
lean_ctor_set(v___x_1422_, 1, v___x_1421_);
v_disable_1423_ = l_Lean_MessageData_note(v___x_1422_);
v___x_1424_ = l_Lean_Linter_linterMessageTag;
v___x_1425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1425_, 0, v_msg_1409_);
lean_ctor_set(v___x_1425_, 1, v_disable_1423_);
v___x_1426_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1426_, 0, v___x_1424_);
lean_ctor_set(v___x_1426_, 1, v___x_1425_);
v___x_1427_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1427_, 0, v_name_1413_);
lean_ctor_set(v___x_1427_, 1, v___x_1426_);
lean_inc(v_stx_1408_);
v___x_1428_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_1428_, 0, v_stx_1408_);
lean_ctor_set(v___x_1428_, 1, v___x_1427_);
v___x_1429_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5(v_stx_1408_, v___x_1428_, v___y_1410_, v___y_1411_);
lean_dec(v_stx_1408_);
return v___x_1429_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___boxed(lean_object* v_linterOption_1433_, lean_object* v_stx_1434_, lean_object* v_msg_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3(v_linterOption_1433_, v_stx_1434_, v_msg_1435_, v___y_1436_, v___y_1437_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1___redArg(lean_object* v_o_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v___x_1443_; lean_object* v_env_1444_; lean_object* v___x_1445_; lean_object* v_toEnvExtension_1446_; lean_object* v_asyncMode_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v_merged_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1459_; 
v___x_1443_ = lean_st_ref_get(v___y_1441_);
v_env_1444_ = lean_ctor_get(v___x_1443_, 0);
lean_inc_ref(v_env_1444_);
lean_dec(v___x_1443_);
v___x_1445_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_1446_ = lean_ctor_get(v___x_1445_, 0);
v_asyncMode_1447_ = lean_ctor_get(v_toEnvExtension_1446_, 2);
v___x_1448_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_1449_ = lean_box(0);
v___x_1450_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1448_, v___x_1445_, v_env_1444_, v_asyncMode_1447_, v___x_1449_);
v_merged_1451_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1459_ == 0)
{
lean_object* v_unused_1460_; 
v_unused_1460_ = lean_ctor_get(v___x_1450_, 1);
lean_dec(v_unused_1460_);
v___x_1453_ = v___x_1450_;
v_isShared_1454_ = v_isSharedCheck_1459_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_merged_1451_);
lean_dec(v___x_1450_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1459_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 1, v_merged_1451_);
lean_ctor_set(v___x_1453_, 0, v_o_1440_);
v___x_1456_ = v___x_1453_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_o_1440_);
lean_ctor_set(v_reuseFailAlloc_1458_, 1, v_merged_1451_);
v___x_1456_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
lean_object* v___x_1457_; 
v___x_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1456_);
return v___x_1457_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1___redArg___boxed(lean_object* v_o_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v_res_1464_; 
v_res_1464_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1___redArg(v_o_1461_, v___y_1462_);
lean_dec(v___y_1462_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1(lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
lean_object* v___x_1468_; lean_object* v_scopes_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v_opts_1472_; lean_object* v___x_1473_; 
v___x_1468_ = lean_st_ref_get(v___y_1466_);
v_scopes_1469_ = lean_ctor_get(v___x_1468_, 2);
lean_inc(v_scopes_1469_);
lean_dec(v___x_1468_);
v___x_1470_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1471_ = l_List_head_x21___redArg(v___x_1470_, v_scopes_1469_);
lean_dec(v_scopes_1469_);
v_opts_1472_ = lean_ctor_get(v___x_1471_, 1);
lean_inc_ref(v_opts_1472_);
lean_dec(v___x_1471_);
v___x_1473_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1___redArg(v_opts_1472_, v___y_1466_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1___boxed(lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1(v___y_1474_, v___y_1475_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2(lean_object* v_linterOption_1478_, lean_object* v_stx_1479_, lean_object* v_msg_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
lean_object* v___x_1484_; lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1495_; 
v___x_1484_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1(v___y_1481_, v___y_1482_);
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1487_ = v___x_1484_;
v_isShared_1488_ = v_isSharedCheck_1495_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1484_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1495_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
uint8_t v___x_1489_; 
v___x_1489_ = l_Lean_Linter_getLinterValue(v_linterOption_1478_, v_a_1485_);
lean_dec(v_a_1485_);
if (v___x_1489_ == 0)
{
lean_object* v___x_1490_; lean_object* v___x_1492_; 
lean_dec_ref(v_msg_1480_);
lean_dec(v_stx_1479_);
lean_dec_ref(v_linterOption_1478_);
v___x_1490_ = lean_box(0);
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 0, v___x_1490_);
v___x_1492_ = v___x_1487_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1490_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
else
{
lean_object* v___x_1494_; 
lean_del_object(v___x_1487_);
v___x_1494_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3(v_linterOption_1478_, v_stx_1479_, v_msg_1480_, v___y_1481_, v___y_1482_);
return v___x_1494_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2___boxed(lean_object* v_linterOption_1496_, lean_object* v_stx_1497_, lean_object* v_msg_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2(v_linterOption_1496_, v_stx_1497_, v_msg_1498_, v___y_1499_, v___y_1500_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
return v_res_1502_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__2(void){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1506_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__1));
v___x_1507_ = l_Lean_MessageData_ofFormat(v___x_1506_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4(lean_object* v_as_1508_, size_t v_sz_1509_, size_t v_i_1510_, lean_object* v_b_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v_a_1516_; uint8_t v___x_1520_; 
v___x_1520_ = lean_usize_dec_lt(v_i_1510_, v_sz_1509_);
if (v___x_1520_ == 0)
{
lean_object* v___x_1521_; 
v___x_1521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1521_, 0, v_b_1511_);
return v___x_1521_;
}
else
{
lean_object* v_a_1522_; lean_object* v_fst_1523_; lean_object* v_snd_1524_; lean_object* v_start_1525_; lean_object* v_stop_1526_; lean_object* v_start_1527_; lean_object* v_stop_1528_; lean_object* v___x_1529_; uint8_t v___y_1531_; uint8_t v___x_1542_; 
v_a_1522_ = lean_array_uget_borrowed(v_as_1508_, v_i_1510_);
v_fst_1523_ = lean_ctor_get(v_a_1522_, 0);
v_snd_1524_ = lean_ctor_get(v_a_1522_, 1);
v_start_1525_ = lean_ctor_get(v_b_1511_, 0);
v_stop_1526_ = lean_ctor_get(v_b_1511_, 1);
v_start_1527_ = lean_ctor_get(v_fst_1523_, 0);
v_stop_1528_ = lean_ctor_get(v_fst_1523_, 1);
v___x_1529_ = l_Lean_Linter_Extra_linter_extra_unnecessarySeqFocus;
v___x_1542_ = lean_nat_dec_le(v_start_1525_, v_start_1527_);
if (v___x_1542_ == 0)
{
v___y_1531_ = v___x_1542_;
goto v___jp_1530_;
}
else
{
uint8_t v___x_1543_; 
v___x_1543_ = lean_nat_dec_le(v_stop_1528_, v_stop_1526_);
v___y_1531_ = v___x_1543_;
goto v___jp_1530_;
}
v___jp_1530_:
{
if (v___y_1531_ == 0)
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
lean_dec_ref(v_b_1511_);
v___x_1532_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__2);
lean_inc(v_snd_1524_);
v___x_1533_ = l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2(v___x_1529_, v_snd_1524_, v___x_1532_, v___y_1512_, v___y_1513_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_dec_ref_known(v___x_1533_, 1);
lean_inc(v_fst_1523_);
v_a_1516_ = v_fst_1523_;
goto v___jp_1515_;
}
else
{
lean_object* v_a_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1541_; 
v_a_1534_ = lean_ctor_get(v___x_1533_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1536_ = v___x_1533_;
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_a_1534_);
lean_dec(v___x_1533_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1539_; 
if (v_isShared_1537_ == 0)
{
v___x_1539_ = v___x_1536_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_a_1534_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
}
}
else
{
v_a_1516_ = v_b_1511_;
goto v___jp_1515_;
}
}
}
v___jp_1515_:
{
size_t v___x_1517_; size_t v___x_1518_; 
v___x_1517_ = ((size_t)1ULL);
v___x_1518_ = lean_usize_add(v_i_1510_, v___x_1517_);
v_i_1510_ = v___x_1518_;
v_b_1511_ = v_a_1516_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___boxed(lean_object* v_as_1544_, lean_object* v_sz_1545_, lean_object* v_i_1546_, lean_object* v_b_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
size_t v_sz_boxed_1551_; size_t v_i_boxed_1552_; lean_object* v_res_1553_; 
v_sz_boxed_1551_ = lean_unbox_usize(v_sz_1545_);
lean_dec(v_sz_1545_);
v_i_boxed_1552_ = lean_unbox_usize(v_i_1546_);
lean_dec(v_i_1546_);
v_res_1553_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4(v_as_1544_, v_sz_boxed_1551_, v_i_boxed_1552_, v_b_1547_, v___y_1548_, v___y_1549_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
lean_dec_ref(v_as_1544_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__0(lean_object* v_r_1554_){
_start:
{
lean_object* v_start_1555_; lean_object* v_stop_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1565_; 
v_start_1555_ = lean_ctor_get(v_r_1554_, 0);
v_stop_1556_ = lean_ctor_get(v_r_1554_, 1);
v_isSharedCheck_1565_ = !lean_is_exclusive(v_r_1554_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1558_ = v_r_1554_;
v_isShared_1559_ = v_isSharedCheck_1565_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_stop_1556_);
lean_inc(v_start_1555_);
lean_dec(v_r_1554_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1565_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1563_; 
v___x_1560_ = lean_nat_to_int(v_stop_1556_);
v___x_1561_ = lean_int_neg(v___x_1560_);
lean_dec(v___x_1560_);
if (v_isShared_1559_ == 0)
{
lean_ctor_set(v___x_1558_, 1, v___x_1561_);
v___x_1563_ = v___x_1558_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_start_1555_);
lean_ctor_set(v_reuseFailAlloc_1564_, 1, v___x_1561_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg(lean_object* v_hi_1568_, lean_object* v_pivot_1569_, lean_object* v_as_1570_, lean_object* v_i_1571_, lean_object* v_k_1572_){
_start:
{
uint8_t v___x_1577_; 
v___x_1577_ = lean_nat_dec_lt(v_k_1572_, v_hi_1568_);
if (v___x_1577_ == 0)
{
lean_object* v___x_1578_; lean_object* v___x_1579_; 
lean_dec(v_k_1572_);
lean_dec_ref(v_pivot_1569_);
v___x_1578_ = lean_array_fswap(v_as_1570_, v_i_1571_, v_hi_1568_);
v___x_1579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1579_, 0, v_i_1571_);
lean_ctor_set(v___x_1579_, 1, v___x_1578_);
return v___x_1579_;
}
else
{
lean_object* v___x_1580_; lean_object* v_fst_1581_; lean_object* v_fst_1582_; lean_object* v___f_1583_; lean_object* v___f_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_8375__overap_1587_; lean_object* v___x_1588_; uint8_t v___x_1589_; 
v___x_1580_ = lean_array_fget_borrowed(v_as_1570_, v_k_1572_);
v_fst_1581_ = lean_ctor_get(v___x_1580_, 0);
v_fst_1582_ = lean_ctor_get(v_pivot_1569_, 0);
v___f_1583_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg___closed__0));
v___f_1584_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg___closed__1));
lean_inc(v_fst_1581_);
v___x_1585_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__0(v_fst_1581_);
lean_inc(v_fst_1582_);
v___x_1586_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__0(v_fst_1582_);
v___x_8375__overap_1587_ = l_lexOrd___redArg(v___f_1583_, v___f_1584_);
v___x_1588_ = lean_apply_2(v___x_8375__overap_1587_, v___x_1585_, v___x_1586_);
v___x_1589_ = lean_unbox(v___x_1588_);
if (v___x_1589_ == 0)
{
if (v___x_1577_ == 0)
{
goto v___jp_1573_;
}
else
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1590_ = lean_array_fswap(v_as_1570_, v_i_1571_, v_k_1572_);
v___x_1591_ = lean_unsigned_to_nat(1u);
v___x_1592_ = lean_nat_add(v_i_1571_, v___x_1591_);
lean_dec(v_i_1571_);
v___x_1593_ = lean_nat_add(v_k_1572_, v___x_1591_);
lean_dec(v_k_1572_);
v_as_1570_ = v___x_1590_;
v_i_1571_ = v___x_1592_;
v_k_1572_ = v___x_1593_;
goto _start;
}
}
else
{
goto v___jp_1573_;
}
}
v___jp_1573_:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1574_ = lean_unsigned_to_nat(1u);
v___x_1575_ = lean_nat_add(v_k_1572_, v___x_1574_);
lean_dec(v_k_1572_);
v_k_1572_ = v___x_1575_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg___boxed(lean_object* v_hi_1595_, lean_object* v_pivot_1596_, lean_object* v_as_1597_, lean_object* v_i_1598_, lean_object* v_k_1599_){
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg(v_hi_1595_, v_pivot_1596_, v_as_1597_, v_i_1598_, v_k_1599_);
lean_dec(v_hi_1595_);
return v_res_1600_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__1(lean_object* v___f_1601_, uint8_t v___x_1602_, lean_object* v_x1_1603_, lean_object* v_x2_1604_){
_start:
{
lean_object* v_fst_1605_; lean_object* v_fst_1606_; lean_object* v___f_1607_; lean_object* v___f_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_8574__overap_1611_; lean_object* v___x_1612_; uint8_t v___x_1613_; 
v_fst_1605_ = lean_ctor_get(v_x1_1603_, 0);
lean_inc(v_fst_1605_);
lean_dec_ref(v_x1_1603_);
v_fst_1606_ = lean_ctor_get(v_x2_1604_, 0);
lean_inc(v_fst_1606_);
lean_dec_ref(v_x2_1604_);
v___f_1607_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg___closed__0));
v___f_1608_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg___closed__1));
lean_inc_ref(v___f_1601_);
v___x_1609_ = lean_apply_1(v___f_1601_, v_fst_1605_);
v___x_1610_ = lean_apply_1(v___f_1601_, v_fst_1606_);
v___x_8574__overap_1611_ = l_lexOrd___redArg(v___f_1607_, v___f_1608_);
v___x_1612_ = lean_apply_2(v___x_8574__overap_1611_, v___x_1609_, v___x_1610_);
v___x_1613_ = lean_unbox(v___x_1612_);
if (v___x_1613_ == 0)
{
return v___x_1602_;
}
else
{
uint8_t v___x_1614_; 
v___x_1614_ = 0;
return v___x_1614_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__1___boxed(lean_object* v___f_1615_, lean_object* v___x_1616_, lean_object* v_x1_1617_, lean_object* v_x2_1618_){
_start:
{
uint8_t v___x_9332__boxed_1619_; uint8_t v_res_1620_; lean_object* v_r_1621_; 
v___x_9332__boxed_1619_ = lean_unbox(v___x_1616_);
v_res_1620_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__1(v___f_1615_, v___x_9332__boxed_1619_, v_x1_1617_, v_x2_1618_);
v_r_1621_ = lean_box(v_res_1620_);
return v_r_1621_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg(lean_object* v_n_1623_, lean_object* v_as_1624_, lean_object* v_lo_1625_, lean_object* v_hi_1626_){
_start:
{
lean_object* v___y_1628_; uint8_t v___x_1638_; 
v___x_1638_ = lean_nat_dec_lt(v_lo_1625_, v_hi_1626_);
if (v___x_1638_ == 0)
{
lean_dec(v_lo_1625_);
return v_as_1624_;
}
else
{
lean_object* v___f_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v_mid_1642_; lean_object* v___y_1644_; lean_object* v___y_1650_; lean_object* v___x_1655_; lean_object* v___x_1656_; uint8_t v___x_1657_; 
v___f_1639_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___closed__0));
v___x_1640_ = lean_nat_add(v_lo_1625_, v_hi_1626_);
v___x_1641_ = lean_unsigned_to_nat(1u);
v_mid_1642_ = lean_nat_shiftr(v___x_1640_, v___x_1641_);
lean_dec(v___x_1640_);
v___x_1655_ = lean_array_fget_borrowed(v_as_1624_, v_mid_1642_);
v___x_1656_ = lean_array_fget_borrowed(v_as_1624_, v_lo_1625_);
lean_inc(v___x_1656_);
lean_inc(v___x_1655_);
v___x_1657_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__1(v___f_1639_, v___x_1638_, v___x_1655_, v___x_1656_);
if (v___x_1657_ == 0)
{
v___y_1650_ = v_as_1624_;
goto v___jp_1649_;
}
else
{
lean_object* v___x_1658_; 
v___x_1658_ = lean_array_fswap(v_as_1624_, v_lo_1625_, v_mid_1642_);
v___y_1650_ = v___x_1658_;
goto v___jp_1649_;
}
v___jp_1643_:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; uint8_t v___x_1647_; 
v___x_1645_ = lean_array_fget_borrowed(v___y_1644_, v_mid_1642_);
v___x_1646_ = lean_array_fget_borrowed(v___y_1644_, v_hi_1626_);
lean_inc(v___x_1646_);
lean_inc(v___x_1645_);
v___x_1647_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__1(v___f_1639_, v___x_1638_, v___x_1645_, v___x_1646_);
if (v___x_1647_ == 0)
{
lean_dec(v_mid_1642_);
v___y_1628_ = v___y_1644_;
goto v___jp_1627_;
}
else
{
lean_object* v___x_1648_; 
v___x_1648_ = lean_array_fswap(v___y_1644_, v_mid_1642_, v_hi_1626_);
lean_dec(v_mid_1642_);
v___y_1628_ = v___x_1648_;
goto v___jp_1627_;
}
}
v___jp_1649_:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; uint8_t v___x_1653_; 
v___x_1651_ = lean_array_fget_borrowed(v___y_1650_, v_hi_1626_);
v___x_1652_ = lean_array_fget_borrowed(v___y_1650_, v_lo_1625_);
lean_inc(v___x_1652_);
lean_inc(v___x_1651_);
v___x_1653_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__1(v___f_1639_, v___x_1638_, v___x_1651_, v___x_1652_);
if (v___x_1653_ == 0)
{
v___y_1644_ = v___y_1650_;
goto v___jp_1643_;
}
else
{
lean_object* v___x_1654_; 
v___x_1654_ = lean_array_fswap(v___y_1650_, v_lo_1625_, v_hi_1626_);
v___y_1644_ = v___x_1654_;
goto v___jp_1643_;
}
}
}
v___jp_1627_:
{
lean_object* v_pivot_1629_; lean_object* v___x_1630_; lean_object* v_fst_1631_; lean_object* v_snd_1632_; uint8_t v___x_1633_; 
v_pivot_1629_ = lean_array_fget(v___y_1628_, v_hi_1626_);
lean_inc_n(v_lo_1625_, 2);
v___x_1630_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg(v_hi_1626_, v_pivot_1629_, v___y_1628_, v_lo_1625_, v_lo_1625_);
v_fst_1631_ = lean_ctor_get(v___x_1630_, 0);
lean_inc(v_fst_1631_);
v_snd_1632_ = lean_ctor_get(v___x_1630_, 1);
lean_inc(v_snd_1632_);
lean_dec_ref(v___x_1630_);
v___x_1633_ = lean_nat_dec_le(v_hi_1626_, v_fst_1631_);
if (v___x_1633_ == 0)
{
lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1634_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg(v_n_1623_, v_snd_1632_, v_lo_1625_, v_fst_1631_);
v___x_1635_ = lean_unsigned_to_nat(1u);
v___x_1636_ = lean_nat_add(v_fst_1631_, v___x_1635_);
lean_dec(v_fst_1631_);
v_as_1624_ = v___x_1634_;
v_lo_1625_ = v___x_1636_;
goto _start;
}
else
{
lean_dec(v_fst_1631_);
lean_dec(v_lo_1625_);
return v_snd_1632_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___boxed(lean_object* v_n_1659_, lean_object* v_as_1660_, lean_object* v_lo_1661_, lean_object* v_hi_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg(v_n_1659_, v_as_1660_, v_lo_1661_, v_hi_1662_);
lean_dec(v_hi_1662_);
lean_dec(v_n_1659_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6(uint8_t v___x_1664_, lean_object* v_x_1665_, lean_object* v_x_1666_){
_start:
{
if (lean_obj_tag(v_x_1666_) == 0)
{
return v_x_1665_;
}
else
{
lean_object* v_value_1667_; uint8_t v_used_1668_; 
v_value_1667_ = lean_ctor_get(v_x_1666_, 1);
v_used_1668_ = lean_ctor_get_uint8(v_value_1667_, sizeof(void*)*1);
if (v_used_1668_ == 0)
{
lean_object* v_tail_1669_; 
v_tail_1669_ = lean_ctor_get(v_x_1666_, 2);
lean_inc(v_tail_1669_);
lean_dec_ref_known(v_x_1666_, 3);
v_x_1666_ = v_tail_1669_;
goto _start;
}
else
{
lean_object* v_key_1671_; lean_object* v_tail_1672_; lean_object* v_stx_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___y_1677_; lean_object* v___x_1681_; 
lean_inc(v_value_1667_);
v_key_1671_ = lean_ctor_get(v_x_1666_, 0);
lean_inc(v_key_1671_);
v_tail_1672_ = lean_ctor_get(v_x_1666_, 2);
lean_inc(v_tail_1672_);
lean_dec_ref_known(v_x_1666_, 3);
v_stx_1673_ = lean_ctor_get(v_value_1667_, 0);
lean_inc(v_stx_1673_);
lean_dec(v_value_1667_);
v___x_1674_ = lean_unsigned_to_nat(1u);
v___x_1675_ = l_Lean_Syntax_getArg(v_stx_1673_, v___x_1674_);
lean_dec(v_stx_1673_);
v___x_1681_ = l_Lean_Syntax_getRange_x3f(v___x_1675_, v___x_1664_);
if (lean_obj_tag(v___x_1681_) == 0)
{
v___y_1677_ = v_key_1671_;
goto v___jp_1676_;
}
else
{
lean_object* v_val_1682_; 
lean_dec(v_key_1671_);
v_val_1682_ = lean_ctor_get(v___x_1681_, 0);
lean_inc(v_val_1682_);
lean_dec_ref_known(v___x_1681_, 1);
v___y_1677_ = v_val_1682_;
goto v___jp_1676_;
}
v___jp_1676_:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1678_, 0, v___y_1677_);
lean_ctor_set(v___x_1678_, 1, v___x_1675_);
v___x_1679_ = lean_array_push(v_x_1665_, v___x_1678_);
v_x_1665_ = v___x_1679_;
v_x_1666_ = v_tail_1672_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6___boxed(lean_object* v___x_1683_, lean_object* v_x_1684_, lean_object* v_x_1685_){
_start:
{
uint8_t v___x_9420__boxed_1686_; lean_object* v_res_1687_; 
v___x_9420__boxed_1686_ = lean_unbox(v___x_1683_);
v_res_1687_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6(v___x_9420__boxed_1686_, v_x_1684_, v_x_1685_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__7(uint8_t v___x_1688_, lean_object* v_as_1689_, size_t v_i_1690_, size_t v_stop_1691_, lean_object* v_b_1692_){
_start:
{
uint8_t v___x_1693_; 
v___x_1693_ = lean_usize_dec_eq(v_i_1690_, v_stop_1691_);
if (v___x_1693_ == 0)
{
lean_object* v___x_1694_; lean_object* v___x_1695_; size_t v___x_1696_; size_t v___x_1697_; 
v___x_1694_ = lean_array_uget_borrowed(v_as_1689_, v_i_1690_);
lean_inc(v___x_1694_);
v___x_1695_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6(v___x_1688_, v_b_1692_, v___x_1694_);
v___x_1696_ = ((size_t)1ULL);
v___x_1697_ = lean_usize_add(v_i_1690_, v___x_1696_);
v_i_1690_ = v___x_1697_;
v_b_1692_ = v___x_1695_;
goto _start;
}
else
{
return v_b_1692_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__7___boxed(lean_object* v___x_1699_, lean_object* v_as_1700_, lean_object* v_i_1701_, lean_object* v_stop_1702_, lean_object* v_b_1703_){
_start:
{
uint8_t v___x_9461__boxed_1704_; size_t v_i_boxed_1705_; size_t v_stop_boxed_1706_; lean_object* v_res_1707_; 
v___x_9461__boxed_1704_ = lean_unbox(v___x_1699_);
v_i_boxed_1705_ = lean_unbox_usize(v_i_1701_);
lean_dec(v_i_1701_);
v_stop_boxed_1706_ = lean_unbox_usize(v_stop_1702_);
lean_dec(v_stop_1702_);
v_res_1707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__7(v___x_9461__boxed_1704_, v_as_1700_, v_i_boxed_1705_, v_stop_boxed_1706_, v_b_1703_);
lean_dec_ref(v_as_1700_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1(lean_object* v_stx_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1740_; lean_object* v___y_1741_; lean_object* v___y_1742_; lean_object* v___y_1743_; lean_object* v___y_1744_; lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___y_1754_; lean_object* v___x_1762_; lean_object* v_a_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1804_; 
v___x_1762_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1(v___y_1713_, v___y_1714_);
v_a_1763_ = lean_ctor_get(v___x_1762_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1765_ = v___x_1762_;
v_isShared_1766_ = v_isSharedCheck_1804_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_a_1763_);
lean_dec(v___x_1762_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1804_;
goto v_resetjp_1764_;
}
v___jp_1716_:
{
size_t v_sz_1719_; size_t v___x_1720_; lean_object* v___x_1721_; 
v_sz_1719_ = lean_array_size(v___y_1718_);
v___x_1720_ = ((size_t)0ULL);
lean_inc_ref(v___y_1717_);
v___x_1721_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4(v___y_1718_, v_sz_1719_, v___x_1720_, v___y_1717_, v___y_1713_, v___y_1714_);
lean_dec_ref(v___y_1718_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1729_; 
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1729_ == 0)
{
lean_object* v_unused_1730_; 
v_unused_1730_ = lean_ctor_get(v___x_1721_, 0);
lean_dec(v_unused_1730_);
v___x_1723_ = v___x_1721_;
v_isShared_1724_ = v_isSharedCheck_1729_;
goto v_resetjp_1722_;
}
else
{
lean_dec(v___x_1721_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1729_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1725_; lean_object* v___x_1727_; 
v___x_1725_ = lean_box(0);
if (v_isShared_1724_ == 0)
{
lean_ctor_set(v___x_1723_, 0, v___x_1725_);
v___x_1727_ = v___x_1723_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1725_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
else
{
lean_object* v_a_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1738_; 
v_a_1731_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1733_ = v___x_1721_;
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_dec(v___x_1721_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1736_; 
if (v_isShared_1734_ == 0)
{
v___x_1736_ = v___x_1733_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_a_1731_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
}
}
v___jp_1739_:
{
lean_object* v___x_1745_; 
v___x_1745_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg(v___y_1742_, v___y_1741_, v___y_1740_, v___y_1744_);
lean_dec(v___y_1744_);
lean_dec(v___y_1742_);
v___y_1717_ = v___y_1743_;
v___y_1718_ = v___x_1745_;
goto v___jp_1716_;
}
v___jp_1746_:
{
uint8_t v___x_1752_; 
v___x_1752_ = lean_nat_dec_le(v___y_1751_, v___y_1747_);
if (v___x_1752_ == 0)
{
lean_dec(v___y_1747_);
lean_inc(v___y_1751_);
v___y_1740_ = v___y_1751_;
v___y_1741_ = v___y_1749_;
v___y_1742_ = v___y_1748_;
v___y_1743_ = v___y_1750_;
v___y_1744_ = v___y_1751_;
goto v___jp_1739_;
}
else
{
v___y_1740_ = v___y_1751_;
v___y_1741_ = v___y_1749_;
v___y_1742_ = v___y_1748_;
v___y_1743_ = v___y_1750_;
v___y_1744_ = v___y_1747_;
goto v___jp_1739_;
}
}
v___jp_1753_:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; uint8_t v___x_1758_; 
v___x_1755_ = lean_unsigned_to_nat(0u);
v___x_1756_ = ((lean_object*)(l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1___closed__0));
v___x_1757_ = lean_array_get_size(v___y_1754_);
v___x_1758_ = lean_nat_dec_eq(v___x_1757_, v___x_1755_);
if (v___x_1758_ == 0)
{
lean_object* v___x_1759_; lean_object* v___x_1760_; uint8_t v___x_1761_; 
v___x_1759_ = lean_unsigned_to_nat(1u);
v___x_1760_ = lean_nat_sub(v___x_1757_, v___x_1759_);
v___x_1761_ = lean_nat_dec_le(v___x_1755_, v___x_1760_);
if (v___x_1761_ == 0)
{
lean_inc(v___x_1760_);
v___y_1747_ = v___x_1760_;
v___y_1748_ = v___x_1757_;
v___y_1749_ = v___y_1754_;
v___y_1750_ = v___x_1756_;
v___y_1751_ = v___x_1760_;
goto v___jp_1746_;
}
else
{
v___y_1747_ = v___x_1760_;
v___y_1748_ = v___x_1757_;
v___y_1749_ = v___y_1754_;
v___y_1750_ = v___x_1756_;
v___y_1751_ = v___x_1755_;
goto v___jp_1746_;
}
}
else
{
v___y_1717_ = v___x_1756_;
v___y_1718_ = v___y_1754_;
goto v___jp_1716_;
}
}
v_resetjp_1764_:
{
lean_object* v___x_1767_; uint8_t v___y_1769_; lean_object* v___x_1800_; uint8_t v___x_1801_; 
v___x_1767_ = lean_st_ref_get(v___y_1714_);
v___x_1800_ = l_Lean_Linter_Extra_linter_extra_unnecessarySeqFocus;
v___x_1801_ = l_Lean_Linter_getLinterValue(v___x_1800_, v_a_1763_);
lean_dec(v_a_1763_);
if (v___x_1801_ == 0)
{
lean_dec(v___x_1767_);
v___y_1769_ = v___x_1801_;
goto v___jp_1768_;
}
else
{
lean_object* v_infoState_1802_; uint8_t v_enabled_1803_; 
v_infoState_1802_ = lean_ctor_get(v___x_1767_, 8);
lean_inc_ref(v_infoState_1802_);
lean_dec(v___x_1767_);
v_enabled_1803_ = lean_ctor_get_uint8(v_infoState_1802_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1802_);
v___y_1769_ = v_enabled_1803_;
goto v___jp_1768_;
}
v___jp_1768_:
{
if (v___y_1769_ == 0)
{
lean_object* v___x_1770_; lean_object* v___x_1772_; 
lean_dec(v_stx_1712_);
v___x_1770_ = lean_box(0);
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 0, v___x_1770_);
v___x_1772_ = v___x_1765_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v___x_1770_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
else
{
lean_object* v___x_1774_; lean_object* v_messages_1775_; uint8_t v___x_1776_; 
v___x_1774_ = lean_st_ref_get(v___y_1714_);
v_messages_1775_ = lean_ctor_get(v___x_1774_, 1);
lean_inc_ref(v_messages_1775_);
lean_dec(v___x_1774_);
v___x_1776_ = l_Lean_MessageLog_hasErrors(v_messages_1775_);
lean_dec_ref(v_messages_1775_);
if (v___x_1776_ == 0)
{
lean_object* v___x_1777_; lean_object* v_a_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___f_1781_; lean_object* v___x_1782_; lean_object* v_snd_1783_; lean_object* v_buckets_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; uint8_t v___x_1788_; 
lean_del_object(v___x_1765_);
v___x_1777_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3___redArg(v___y_1714_);
v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
lean_inc(v_a_1778_);
lean_dec_ref(v___x_1777_);
v___x_1779_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_multigoalKindsRef;
v___x_1780_ = lean_st_ref_get(v___x_1779_);
v___f_1781_ = lean_alloc_closure((void*)(l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1781_, 0, v_stx_1712_);
lean_closure_set(v___f_1781_, 1, v___x_1780_);
lean_closure_set(v___f_1781_, 2, v_a_1778_);
v___x_1782_ = l_runST___redArg(v___f_1781_);
v_snd_1783_ = lean_ctor_get(v___x_1782_, 1);
lean_inc(v_snd_1783_);
lean_dec(v___x_1782_);
v_buckets_1784_ = lean_ctor_get(v_snd_1783_, 1);
lean_inc_ref(v_buckets_1784_);
lean_dec(v_snd_1783_);
v___x_1785_ = lean_unsigned_to_nat(0u);
v___x_1786_ = ((lean_object*)(l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1___closed__1));
v___x_1787_ = lean_array_get_size(v_buckets_1784_);
v___x_1788_ = lean_nat_dec_lt(v___x_1785_, v___x_1787_);
if (v___x_1788_ == 0)
{
lean_dec_ref(v_buckets_1784_);
v___y_1754_ = v___x_1786_;
goto v___jp_1753_;
}
else
{
uint8_t v___x_1789_; 
v___x_1789_ = lean_nat_dec_le(v___x_1787_, v___x_1787_);
if (v___x_1789_ == 0)
{
if (v___x_1788_ == 0)
{
lean_dec_ref(v_buckets_1784_);
v___y_1754_ = v___x_1786_;
goto v___jp_1753_;
}
else
{
size_t v___x_1790_; size_t v___x_1791_; lean_object* v___x_1792_; 
v___x_1790_ = ((size_t)0ULL);
v___x_1791_ = lean_usize_of_nat(v___x_1787_);
v___x_1792_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__7(v___x_1776_, v_buckets_1784_, v___x_1790_, v___x_1791_, v___x_1786_);
lean_dec_ref(v_buckets_1784_);
v___y_1754_ = v___x_1792_;
goto v___jp_1753_;
}
}
else
{
size_t v___x_1793_; size_t v___x_1794_; lean_object* v___x_1795_; 
v___x_1793_ = ((size_t)0ULL);
v___x_1794_ = lean_usize_of_nat(v___x_1787_);
v___x_1795_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__7(v___x_1776_, v_buckets_1784_, v___x_1793_, v___x_1794_, v___x_1786_);
lean_dec_ref(v_buckets_1784_);
v___y_1754_ = v___x_1795_;
goto v___jp_1753_;
}
}
}
else
{
lean_object* v___x_1796_; lean_object* v___x_1798_; 
lean_dec(v_stx_1712_);
v___x_1796_ = lean_box(0);
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 0, v___x_1796_);
v___x_1798_ = v___x_1765_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v___x_1796_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1___boxed(lean_object* v_stx_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1(v_stx_1805_, v___y_1806_, v___y_1807_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1(lean_object* v_o_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v___x_1829_; 
v___x_1829_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1___redArg(v_o_1825_, v___y_1827_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1___boxed(lean_object* v_o_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
lean_object* v_res_1834_; 
v_res_1834_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1(v_o_1830_, v___y_1831_, v___y_1832_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
return v_res_1834_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5(lean_object* v_n_1835_, lean_object* v_as_1836_, lean_object* v_lo_1837_, lean_object* v_hi_1838_, lean_object* v_w_1839_, lean_object* v_hlo_1840_, lean_object* v_hhi_1841_){
_start:
{
lean_object* v___x_1842_; 
v___x_1842_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg(v_n_1835_, v_as_1836_, v_lo_1837_, v_hi_1838_);
return v___x_1842_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___boxed(lean_object* v_n_1843_, lean_object* v_as_1844_, lean_object* v_lo_1845_, lean_object* v_hi_1846_, lean_object* v_w_1847_, lean_object* v_hlo_1848_, lean_object* v_hhi_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5(v_n_1843_, v_as_1844_, v_lo_1845_, v_hi_1846_, v_w_1847_, v_hlo_1848_, v_hhi_1849_);
lean_dec(v_hi_1846_);
lean_dec(v_n_1843_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7(lean_object* v_n_1851_, lean_object* v_lo_1852_, lean_object* v_hi_1853_, lean_object* v_hhi_1854_, lean_object* v_pivot_1855_, lean_object* v_as_1856_, lean_object* v_i_1857_, lean_object* v_k_1858_, lean_object* v_ilo_1859_, lean_object* v_ik_1860_, lean_object* v_w_1861_){
_start:
{
lean_object* v___x_1862_; 
v___x_1862_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg(v_hi_1853_, v_pivot_1855_, v_as_1856_, v_i_1857_, v_k_1858_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___boxed(lean_object* v_n_1863_, lean_object* v_lo_1864_, lean_object* v_hi_1865_, lean_object* v_hhi_1866_, lean_object* v_pivot_1867_, lean_object* v_as_1868_, lean_object* v_i_1869_, lean_object* v_k_1870_, lean_object* v_ilo_1871_, lean_object* v_ik_1872_, lean_object* v_w_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7(v_n_1863_, v_lo_1864_, v_hi_1865_, v_hhi_1866_, v_pivot_1867_, v_as_1868_, v_i_1869_, v_k_1870_, v_ilo_1871_, v_ik_1872_, v_w_1873_);
lean_dec(v_hi_1865_);
lean_dec(v_lo_1864_);
lean_dec(v_n_1863_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12(lean_object* v_msgData_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v___x_1879_; 
v___x_1879_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg(v_msgData_1875_, v___y_1877_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___boxed(lean_object* v_msgData_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12(v_msgData_1880_, v___y_1881_, v___y_1882_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_3917858151____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1886_ = ((lean_object*)(l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter));
v___x_1887_ = l_Lean_Elab_Command_addLinter(v___x_1886_);
return v___x_1887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_3917858151____hygCtx___hyg_2____boxed(lean_object* v_a_1888_){
_start:
{
lean_object* v_res_1889_; 
v_res_1889_ = l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_3917858151____hygCtx___hyg_2_();
return v_res_1889_;
}
}
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_Extra_UnnecessarySeqFocus(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
