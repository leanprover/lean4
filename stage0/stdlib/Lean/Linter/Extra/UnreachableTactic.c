// Lean compiler output
// Module: Lean.Linter.Extra.UnreachableTactic
// Imports: public import Lean.Elab.Command public import Lean.Linter.Basic public import Lean.Parser.Syntax public import Init.Try
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
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
uint64_t l_Lean_Syntax_instHashableRange_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t l_Lean_Syntax_instBEqRange_beq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_clearCell___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Syntax_instBEqRange_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_instHashableRange_hash___boxed(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_NameHashSet_contains(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
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
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l_instOrdNat___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instOrdInt___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_lexOrd___redArg(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
extern lean_object* l_Lean_Parser_parserExtension;
extern lean_object* l_Lean_Parser_ParserExtension_instInhabitedState_default;
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameHashSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_withSetOptionIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addLinter(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "extra"};
static const lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "unreachableTactic"};
static const lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(33, 183, 205, 183, 92, 15, 88, 116)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(136, 56, 214, 109, 29, 26, 244, 93)}};
static const lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "enable the 'unreachable tactic' linter"};
static const lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__5_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__5_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__5_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__7_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__7_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__7_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__8_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Extra"};
static const lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__8_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__8_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__7_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__8_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(179, 148, 165, 15, 81, 68, 12, 199)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(98, 33, 172, 180, 73, 123, 191, 116)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(105, 61, 181, 137, 182, 231, 65, 137)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value_aux_4),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(160, 216, 142, 110, 226, 73, 5, 212)}};
static const lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_linter_extra_unreachableTactic;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__0_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__0_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__1_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__1_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__2_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__2_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__3_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__3_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__3_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__4_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "discharger"};
static const lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__4_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__4_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__5_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "registerTryTactic"};
static const lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__5_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__5_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mixfix"};
static const lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__7_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__7_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__7_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__8_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "notation"};
static const lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__8_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__8_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__3_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__7_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__8_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(13, 34, 53, 7, 182, 20, 8, 182)}};
static const lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__10_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "tacticStop_"};
static const lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__10_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__10_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__11_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__11_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__11_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__12_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "quotSeq"};
static const lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__12_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__12_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__13_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__13_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__13_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__3_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__13_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__13_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__11_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__13_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__13_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__12_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(171, 67, 133, 150, 48, 85, 223, 184)}};
static const lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__13_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__13_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__14_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__14_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__14_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__15_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "binderTactic"};
static const lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__15_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__15_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__16_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__16_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__16_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__3_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__16_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__16_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__14_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__16_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__16_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__15_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(17, 181, 78, 34, 190, 12, 180, 92)}};
static const lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__16_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__16_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__17_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__17_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__18_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "dynamicQuot"};
static const lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__18_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__18_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__19_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__19_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__19_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__3_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__19_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__19_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__14_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__19_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__19_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__18_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(116, 123, 139, 164, 173, 191, 116, 242)}};
static const lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__19_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__19_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__20_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__20_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__21_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__21_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__22_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__22_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__23_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__23_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_ignoreTacticKindsRef;
static const lean_string_object l_Lean_Linter_Extra_UnreachableTactic_isIgnoreTacticKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "quot"};
static const lean_object* l_Lean_Linter_Extra_UnreachableTactic_isIgnoreTacticKind___closed__0 = (const lean_object*)&l_Lean_Linter_Extra_UnreachableTactic_isIgnoreTacticKind___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Linter_Extra_UnreachableTactic_isIgnoreTacticKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_isIgnoreTacticKind___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_addIgnoreTacticKind(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_addIgnoreTacticKind___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__0;
static lean_once_cell_t l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__1;
static const lean_closure_object l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_instBEqRange_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__2 = (const lean_object*)&l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__2_value;
static const lean_closure_object l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_instHashableRange_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__3 = (const lean_object*)&l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_getTactics___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_getTactics(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_getTactics___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_getTactics___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5_spec__8_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5_spec__8_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5_spec__8_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8_spec__13_spec__16___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8_spec__13_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8_spec__13___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__15_spec__19_spec__21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__15_spec__19_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__15_spec__19___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__15_spec__19___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__15___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__15___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__16(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___lam__0(lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instOrdNat___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___lam__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___lam__1___closed__0_value;
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instOrdInt___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___lam__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___lam__1___closed__1_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__20(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__20___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "This linter can be disabled with `set_option "};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__0 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__0_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__1;
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " false`"};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__2 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__2_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "this tactic is never executed"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__0 = (const lean_object*)&l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_object* l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__1 = (const lean_object*)&l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__1_value;
static const lean_string_object l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "conv"};
static const lean_object* l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__2 = (const lean_object*)&l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(232, 67, 39, 189, 45, 247, 54, 81)}};
static const lean_object* l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__3 = (const lean_object*)&l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__4;
static lean_once_cell_t l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__5;
static lean_once_cell_t l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__6;
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__0 = (const lean_object*)&l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__0_value;
static const lean_closure_object l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_withSetOptionIn___boxed, .m_arity = 6, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__0_value)} };
static const lean_object* l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__1 = (const lean_object*)&l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__1_value;
static const lean_string_object l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "UnreachableTactic"};
static const lean_object* l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__2 = (const lean_object*)&l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__2_value;
static const lean_string_object l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "unreachableTacticLinter"};
static const lean_object* l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__3 = (const lean_object*)&l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__3_value;
static const lean_ctor_object l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__7_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__8_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(179, 148, 165, 15, 81, 68, 12, 199)}};
static const lean_ctor_object l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__4_value_aux_2),((lean_object*)&l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__2_value),LEAN_SCALAR_PTR_LITERAL(140, 193, 179, 4, 1, 11, 28, 35)}};
static const lean_ctor_object l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__4_value_aux_3),((lean_object*)&l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__3_value),LEAN_SCALAR_PTR_LITERAL(242, 29, 169, 147, 81, 15, 32, 76)}};
static const lean_object* l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__4 = (const lean_object*)&l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__4_value;
static const lean_ctor_object l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__1_value),((lean_object*)&l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__4_value)}};
static const lean_object* l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__5 = (const lean_object*)&l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter = (const lean_object*)&l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8_spec__13(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__15(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__15___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8_spec__13_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8_spec__13_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__15_spec__19(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__15_spec__19___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__15_spec__19_spec__21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__15_spec__19_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_1366347041____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_1366347041____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_58_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4_));
v___x_59_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__5_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4_));
v___x_60_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4_));
v___x_61_ = l_Lean_Option_register___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__spec__0(v___x_58_, v___x_59_, v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4____boxed(lean_object* v_a_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4_();
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_m_64_, lean_object* v_query_65_, lean_object* v_x_66_, lean_object* v_x_67_, lean_object* v_x_68_){
_start:
{
lean_object* v_zero_69_; uint8_t v_isZero_70_; 
v_zero_69_ = lean_unsigned_to_nat(0u);
v_isZero_70_ = lean_nat_dec_eq(v_x_67_, v_zero_69_);
if (v_isZero_70_ == 1)
{
lean_dec(v_x_68_);
lean_dec(v_x_67_);
if (lean_obj_tag(v_x_66_) == 0)
{
lean_object* v___x_71_; 
v___x_71_ = lean_box(2);
return v___x_71_;
}
else
{
lean_object* v_val_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_79_; 
v_val_72_ = lean_ctor_get(v_x_66_, 0);
v_isSharedCheck_79_ = !lean_is_exclusive(v_x_66_);
if (v_isSharedCheck_79_ == 0)
{
v___x_74_ = v_x_66_;
v_isShared_75_ = v_isSharedCheck_79_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_val_72_);
lean_dec(v_x_66_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_79_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
lean_object* v___x_77_; 
if (v_isShared_75_ == 0)
{
v___x_77_ = v___x_74_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v_val_72_);
v___x_77_ = v_reuseFailAlloc_78_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
return v___x_77_;
}
}
}
}
else
{
lean_object* v_keyArray_80_; lean_object* v_valueArray_81_; lean_object* v___x_82_; uint8_t v_isSome_83_; 
v_keyArray_80_ = lean_ctor_get(v_m_64_, 1);
v_valueArray_81_ = lean_ctor_get(v_m_64_, 2);
v___x_82_ = lean_array_fget_borrowed(v_keyArray_80_, v_x_68_);
v_isSome_83_ = lean_noption_is_some(v___x_82_);
if (v_isSome_83_ == 0)
{
lean_dec(v_x_67_);
if (lean_obj_tag(v_x_66_) == 0)
{
lean_object* v___x_84_; 
v___x_84_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_84_, 0, v_x_68_);
return v___x_84_;
}
else
{
lean_object* v_val_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_92_; 
lean_dec(v_x_68_);
v_val_85_ = lean_ctor_get(v_x_66_, 0);
v_isSharedCheck_92_ = !lean_is_exclusive(v_x_66_);
if (v_isSharedCheck_92_ == 0)
{
v___x_87_ = v_x_66_;
v_isShared_88_ = v_isSharedCheck_92_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_val_85_);
lean_dec(v_x_66_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_92_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v___x_90_; 
if (v_isShared_88_ == 0)
{
v___x_90_ = v___x_87_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v_val_85_);
v___x_90_ = v_reuseFailAlloc_91_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
return v___x_90_;
}
}
}
}
else
{
lean_object* v_one_93_; lean_object* v_n_94_; lean_object* v___y_96_; 
v_one_93_ = lean_unsigned_to_nat(1u);
v_n_94_ = lean_nat_sub(v_x_67_, v_one_93_);
lean_dec(v_x_67_);
if (v_isSome_83_ == 0)
{
goto v___jp_102_;
}
else
{
lean_object* v___x_104_; uint8_t v_isSome_105_; 
v___x_104_ = lean_array_fget_borrowed(v_valueArray_81_, v_x_68_);
v_isSome_105_ = lean_noption_is_some(v___x_104_);
if (v_isSome_105_ == 0)
{
goto v___jp_102_;
}
else
{
lean_object* v_val_106_; uint8_t v___x_107_; 
lean_inc(v___x_82_);
v_val_106_ = lean_noption_get(v___x_82_);
v___x_107_ = lean_name_eq(v_val_106_, v_query_65_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; lean_object* v___x_109_; uint8_t v___x_110_; 
lean_dec(v_val_106_);
v___x_108_ = lean_array_get_size(v_keyArray_80_);
v___x_109_ = lean_nat_add(v_x_68_, v_one_93_);
lean_dec(v_x_68_);
v___x_110_ = lean_nat_dec_lt(v___x_109_, v___x_108_);
if (v___x_110_ == 0)
{
lean_dec(v___x_109_);
v_x_67_ = v_n_94_;
v_x_68_ = v_zero_69_;
goto _start;
}
else
{
v_x_67_ = v_n_94_;
v_x_68_ = v___x_109_;
goto _start;
}
}
else
{
lean_object* v_val_113_; lean_object* v___x_114_; 
lean_dec(v_n_94_);
lean_dec(v_x_66_);
lean_inc(v___x_104_);
v_val_113_ = lean_noption_get(v___x_104_);
v___x_114_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_114_, 0, v_x_68_);
lean_ctor_set(v___x_114_, 1, v_val_106_);
lean_ctor_set(v___x_114_, 2, v_val_113_);
return v___x_114_;
}
}
}
v___jp_95_:
{
lean_object* v___x_97_; lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_97_ = lean_array_get_size(v_keyArray_80_);
v___x_98_ = lean_nat_add(v_x_68_, v_one_93_);
lean_dec(v_x_68_);
v___x_99_ = lean_nat_dec_lt(v___x_98_, v___x_97_);
if (v___x_99_ == 0)
{
lean_dec(v___x_98_);
v_x_66_ = v___y_96_;
v_x_67_ = v_n_94_;
v_x_68_ = v_zero_69_;
goto _start;
}
else
{
v_x_66_ = v___y_96_;
v_x_67_ = v_n_94_;
v_x_68_ = v___x_98_;
goto _start;
}
}
v___jp_102_:
{
if (lean_obj_tag(v_x_66_) == 0)
{
lean_object* v___x_103_; 
lean_inc(v_x_68_);
v___x_103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_103_, 0, v_x_68_);
v___y_96_ = v___x_103_;
goto v___jp_95_;
}
else
{
v___y_96_ = v_x_66_;
goto v___jp_95_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_m_115_, lean_object* v_query_116_, lean_object* v_x_117_, lean_object* v_x_118_, lean_object* v_x_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0___redArg(v_m_115_, v_query_116_, v_x_117_, v_x_118_, v_x_119_);
lean_dec(v_query_116_);
lean_dec_ref(v_m_115_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(lean_object* v_m_121_, lean_object* v_query_122_){
_start:
{
lean_object* v_keyArray_123_; lean_object* v___x_124_; uint64_t v___y_126_; 
v_keyArray_123_ = lean_ctor_get(v_m_121_, 1);
v___x_124_ = lean_array_get_size(v_keyArray_123_);
if (lean_obj_tag(v_query_122_) == 0)
{
uint64_t v___x_141_; 
v___x_141_ = 1723ULL;
v___y_126_ = v___x_141_;
goto v___jp_125_;
}
else
{
uint64_t v_hash_142_; 
v_hash_142_ = lean_ctor_get_uint64(v_query_122_, sizeof(void*)*2);
v___y_126_ = v_hash_142_;
goto v___jp_125_;
}
v___jp_125_:
{
uint64_t v___x_127_; uint64_t v___x_128_; uint64_t v_fold_129_; uint64_t v___x_130_; uint64_t v___x_131_; uint64_t v___x_132_; size_t v___x_133_; size_t v___x_134_; size_t v___x_135_; size_t v___x_136_; size_t v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_127_ = 32ULL;
v___x_128_ = lean_uint64_shift_right(v___y_126_, v___x_127_);
v_fold_129_ = lean_uint64_xor(v___y_126_, v___x_128_);
v___x_130_ = 16ULL;
v___x_131_ = lean_uint64_shift_right(v_fold_129_, v___x_130_);
v___x_132_ = lean_uint64_xor(v_fold_129_, v___x_131_);
v___x_133_ = lean_uint64_to_usize(v___x_132_);
v___x_134_ = lean_usize_of_nat(v___x_124_);
v___x_135_ = ((size_t)1ULL);
v___x_136_ = lean_usize_sub(v___x_134_, v___x_135_);
v___x_137_ = lean_usize_land(v___x_133_, v___x_136_);
v___x_138_ = lean_usize_to_nat(v___x_137_);
v___x_139_ = lean_box(0);
v___x_140_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0___redArg(v_m_121_, v_query_122_, v___x_139_, v___x_124_, v___x_138_);
return v___x_140_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_m_143_, lean_object* v_query_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v_m_143_, v_query_144_);
lean_dec(v_query_144_);
lean_dec_ref(v_m_143_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(lean_object* v_b_146_, lean_object* v_acc_147_, lean_object* v_i_148_){
_start:
{
lean_object* v___y_150_; lean_object* v_keyArray_158_; lean_object* v_valueArray_159_; lean_object* v___x_160_; uint8_t v___x_161_; 
v_keyArray_158_ = lean_ctor_get(v_b_146_, 1);
v_valueArray_159_ = lean_ctor_get(v_b_146_, 2);
v___x_160_ = lean_array_get_size(v_keyArray_158_);
v___x_161_ = lean_nat_dec_lt(v_i_148_, v___x_160_);
if (v___x_161_ == 0)
{
lean_dec(v_i_148_);
return v_acc_147_;
}
else
{
lean_object* v___x_162_; uint8_t v_isSome_163_; 
v___x_162_ = lean_array_fget_borrowed(v_keyArray_158_, v_i_148_);
v_isSome_163_ = lean_noption_is_some(v___x_162_);
if (v_isSome_163_ == 0)
{
goto v___jp_154_;
}
else
{
lean_object* v___x_164_; uint8_t v_isSome_165_; 
v___x_164_ = lean_array_fget_borrowed(v_valueArray_159_, v_i_148_);
v_isSome_165_ = lean_noption_is_some(v___x_164_);
if (v_isSome_165_ == 0)
{
goto v___jp_154_;
}
else
{
lean_object* v_val_166_; lean_object* v_val_167_; lean_object* v_i_169_; lean_object* v___x_174_; 
lean_inc(v___x_162_);
v_val_166_ = lean_noption_get(v___x_162_);
lean_inc(v___x_164_);
v_val_167_ = lean_noption_get(v___x_164_);
v___x_174_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v_acc_147_, v_val_166_);
switch(lean_obj_tag(v___x_174_))
{
case 0:
{
lean_object* v_index_175_; lean_object* v_size_176_; lean_object* v___x_177_; 
v_index_175_ = lean_ctor_get(v___x_174_, 0);
lean_inc(v_index_175_);
lean_dec_ref_known(v___x_174_, 3);
v_size_176_ = lean_ctor_get(v_acc_147_, 0);
lean_inc(v_size_176_);
v___x_177_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_147_, v_size_176_, v_index_175_, v_val_166_, v_val_167_);
lean_dec(v_index_175_);
v___y_150_ = v___x_177_;
goto v___jp_149_;
}
case 1:
{
lean_object* v_index_178_; 
v_index_178_ = lean_ctor_get(v___x_174_, 0);
lean_inc(v_index_178_);
lean_dec_ref_known(v___x_174_, 1);
v_i_169_ = v_index_178_;
goto v___jp_168_;
}
default: 
{
lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_179_ = lean_unsigned_to_nat(0u);
v___x_180_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_147_, v___x_179_);
if (lean_obj_tag(v___x_180_) == 0)
{
lean_object* v_index_181_; 
v_index_181_ = lean_ctor_get(v___x_180_, 0);
lean_inc(v_index_181_);
lean_dec_ref_known(v___x_180_, 1);
v_i_169_ = v_index_181_;
goto v___jp_168_;
}
else
{
lean_dec(v_val_167_);
lean_dec(v_val_166_);
v___y_150_ = v_acc_147_;
goto v___jp_149_;
}
}
}
v___jp_168_:
{
lean_object* v_size_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v_size_170_ = lean_ctor_get(v_acc_147_, 0);
v___x_171_ = lean_unsigned_to_nat(1u);
v___x_172_ = lean_nat_add(v_size_170_, v___x_171_);
v___x_173_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_147_, v___x_172_, v_i_169_, v_val_166_, v_val_167_);
lean_dec(v_i_169_);
v___y_150_ = v___x_173_;
goto v___jp_149_;
}
}
}
}
v___jp_149_:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = lean_unsigned_to_nat(1u);
v___x_152_ = lean_nat_add(v_i_148_, v___x_151_);
lean_dec(v_i_148_);
v_acc_147_ = v___y_150_;
v_i_148_ = v___x_152_;
goto _start;
}
v___jp_154_:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = lean_unsigned_to_nat(1u);
v___x_156_ = lean_nat_add(v_i_148_, v___x_155_);
lean_dec(v_i_148_);
v_i_148_ = v___x_156_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_b_182_, lean_object* v_acc_183_, lean_object* v_i_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v_b_182_, v_acc_183_, v_i_184_);
lean_dec_ref(v_b_182_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_init_186_, lean_object* v_b_187_){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = lean_unsigned_to_nat(0u);
v___x_189_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v_b_187_, v_init_186_, v___x_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_init_190_, lean_object* v_b_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1_spec__2___redArg(v_init_190_, v_b_191_);
lean_dec_ref(v_b_191_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1___redArg(lean_object* v_m_193_){
_start:
{
lean_object* v_keyArray_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v_cellCount_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v_target_201_; lean_object* v___x_202_; 
v_keyArray_194_ = lean_ctor_get(v_m_193_, 1);
v___x_195_ = lean_array_get_size(v_keyArray_194_);
v___x_196_ = lean_unsigned_to_nat(2u);
v_cellCount_197_ = lean_nat_mul(v___x_195_, v___x_196_);
v___x_198_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_197_);
v___x_199_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_197_);
v___x_200_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_197_);
v_target_201_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_201_, 0, v___x_198_);
lean_ctor_set(v_target_201_, 1, v___x_199_);
lean_ctor_set(v_target_201_, 2, v___x_200_);
v___x_202_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1_spec__2___redArg(v_target_201_, v_m_193_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_m_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1___redArg(v_m_203_);
lean_dec_ref(v_m_203_);
return v_res_204_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__0_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_(void){
_start:
{
lean_object* v_cellCount_205_; lean_object* v___x_206_; 
v_cellCount_205_ = lean_unsigned_to_nat(16u);
v___x_206_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_205_);
return v___x_206_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__1_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_(void){
_start:
{
lean_object* v_cellCount_207_; lean_object* v___x_208_; 
v_cellCount_207_ = lean_unsigned_to_nat(16u);
v___x_208_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_207_);
return v___x_208_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__2_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_209_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__1_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__1_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__1_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
v___x_210_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__0_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__0_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__0_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
v___x_211_ = lean_unsigned_to_nat(0u);
v___x_212_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
lean_ctor_set(v___x_212_, 1, v___x_210_);
lean_ctor_set(v___x_212_, 2, v___x_209_);
return v___x_212_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__17_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_239_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__16_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_));
v___x_240_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__2_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__2_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__2_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
v___x_241_ = l_Lean_NameHashSet_insert(v___x_240_, v___x_239_);
return v___x_241_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__20_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__17_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__17_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__17_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
v___x_249_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1___redArg(v___x_248_);
return v___x_249_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__21_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_250_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__19_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_));
v___x_251_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__20_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__20_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__20_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
v___x_252_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___x_251_, v___x_250_);
return v___x_252_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__22_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_253_ = lean_unsigned_to_nat(0u);
v___x_254_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__20_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__20_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__20_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
v___x_255_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_254_, v___x_253_);
return v___x_255_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__23_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_256_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__19_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_));
v___x_257_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__17_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__17_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__17_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
v___x_258_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___x_257_, v___x_256_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_(){
_start:
{
lean_object* v___y_261_; lean_object* v___y_265_; lean_object* v___y_266_; lean_object* v___y_267_; lean_object* v_i_268_; lean_object* v___y_274_; lean_object* v___y_275_; lean_object* v___y_276_; lean_object* v_i_277_; lean_object* v___x_282_; lean_object* v___y_284_; lean_object* v___y_285_; lean_object* v___y_286_; lean_object* v___y_295_; lean_object* v___y_296_; lean_object* v___y_297_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___y_309_; lean_object* v___y_310_; lean_object* v___y_342_; lean_object* v___y_343_; lean_object* v___y_344_; lean_object* v___y_345_; lean_object* v_i_346_; lean_object* v___y_352_; lean_object* v___y_353_; lean_object* v___y_354_; lean_object* v___y_355_; lean_object* v___y_364_; lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v___y_367_; lean_object* v_i_368_; lean_object* v___y_374_; lean_object* v___y_375_; lean_object* v___y_376_; lean_object* v___y_377_; lean_object* v___y_387_; lean_object* v___y_388_; lean_object* v___y_389_; lean_object* v___y_421_; lean_object* v___y_422_; lean_object* v___y_423_; lean_object* v___y_424_; lean_object* v___y_425_; lean_object* v_i_426_; lean_object* v___y_432_; lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v___y_435_; lean_object* v___y_436_; lean_object* v___y_445_; lean_object* v___y_446_; lean_object* v___y_447_; lean_object* v___y_448_; lean_object* v___y_449_; lean_object* v_i_450_; lean_object* v___y_456_; lean_object* v___y_457_; lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v___y_460_; lean_object* v___y_470_; lean_object* v___y_471_; lean_object* v___y_472_; lean_object* v___y_504_; lean_object* v___y_505_; lean_object* v___y_506_; lean_object* v___y_507_; lean_object* v___y_508_; lean_object* v_i_509_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v_i_533_; lean_object* v___y_539_; lean_object* v___y_540_; lean_object* v___y_541_; lean_object* v___y_542_; lean_object* v___y_543_; lean_object* v___y_553_; lean_object* v___y_554_; lean_object* v___y_586_; lean_object* v___y_587_; lean_object* v___y_588_; lean_object* v___y_589_; lean_object* v_i_590_; lean_object* v___y_596_; lean_object* v___y_597_; lean_object* v___y_598_; lean_object* v___y_599_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v___y_611_; lean_object* v_i_612_; lean_object* v___y_618_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v_i_668_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v_i_690_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v___y_709_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___y_744_; lean_object* v_i_745_; lean_object* v___y_751_; lean_object* v___y_760_; lean_object* v_i_761_; lean_object* v___x_775_; 
v___x_282_ = lean_unsigned_to_nat(0u);
v___x_306_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4_));
v___x_307_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__3_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_));
v___x_740_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__17_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__17_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__17_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
v___x_741_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__19_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_));
v___x_742_ = lean_box(0);
v___x_775_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__23_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__23_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__23_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
switch(lean_obj_tag(v___x_775_))
{
case 0:
{
v___y_709_ = v___x_740_;
goto v___jp_708_;
}
case 1:
{
lean_object* v_index_776_; lean_object* v_size_777_; lean_object* v_keyArray_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; uint8_t v___x_782_; 
v_index_776_ = lean_ctor_get(v___x_775_, 0);
v_size_777_ = lean_ctor_get(v___x_740_, 0);
v_keyArray_778_ = lean_ctor_get(v___x_740_, 1);
v___x_779_ = lean_unsigned_to_nat(1u);
v___x_780_ = lean_nat_add(v_size_777_, v___x_779_);
v___x_781_ = lean_array_get_size(v_keyArray_778_);
v___x_782_ = lean_nat_dec_lt(v___x_780_, v___x_781_);
if (v___x_782_ == 0)
{
lean_dec(v___x_780_);
goto v___jp_766_;
}
else
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; uint8_t v___x_787_; 
v___x_783_ = lean_unsigned_to_nat(4u);
v___x_784_ = lean_nat_mul(v___x_780_, v___x_783_);
v___x_785_ = lean_unsigned_to_nat(3u);
v___x_786_ = lean_nat_mul(v___x_781_, v___x_785_);
v___x_787_ = lean_nat_dec_le(v___x_784_, v___x_786_);
lean_dec(v___x_786_);
lean_dec(v___x_784_);
if (v___x_787_ == 0)
{
lean_dec(v___x_780_);
goto v___jp_766_;
}
else
{
lean_object* v___x_788_; 
v___x_788_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_740_, v___x_780_, v_index_776_, v___x_741_, v___x_742_);
v___y_709_ = v___x_788_;
goto v___jp_708_;
}
}
}
default: 
{
lean_object* v_size_789_; lean_object* v_keyArray_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; uint8_t v___x_794_; 
v_size_789_ = lean_ctor_get(v___x_740_, 0);
v_keyArray_790_ = lean_ctor_get(v___x_740_, 1);
v___x_791_ = lean_unsigned_to_nat(1u);
v___x_792_ = lean_nat_add(v_size_789_, v___x_791_);
v___x_793_ = lean_array_get_size(v_keyArray_790_);
v___x_794_ = lean_nat_dec_lt(v___x_792_, v___x_793_);
if (v___x_794_ == 0)
{
lean_object* v___x_795_; 
lean_dec(v___x_792_);
v___x_795_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__20_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__20_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__20_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
v___y_751_ = v___x_795_;
goto v___jp_750_;
}
else
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; uint8_t v___x_800_; 
v___x_796_ = lean_unsigned_to_nat(4u);
v___x_797_ = lean_nat_mul(v___x_792_, v___x_796_);
lean_dec(v___x_792_);
v___x_798_ = lean_unsigned_to_nat(3u);
v___x_799_ = lean_nat_mul(v___x_793_, v___x_798_);
v___x_800_ = lean_nat_dec_le(v___x_797_, v___x_799_);
lean_dec(v___x_799_);
lean_dec(v___x_797_);
if (v___x_800_ == 0)
{
lean_object* v___x_801_; 
v___x_801_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__20_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__20_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__20_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
v___y_751_ = v___x_801_;
goto v___jp_750_;
}
else
{
v___y_751_ = v___x_740_;
goto v___jp_750_;
}
}
}
}
v___jp_260_:
{
lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_262_ = lean_st_mk_ref(v___y_261_);
v___x_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
return v___x_263_;
}
v___jp_264_:
{
lean_object* v_size_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v_size_269_ = lean_ctor_get(v___y_266_, 0);
v___x_270_ = lean_unsigned_to_nat(1u);
v___x_271_ = lean_nat_add(v_size_269_, v___x_270_);
v___x_272_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_266_, v___x_271_, v_i_268_, v___y_267_, v___y_265_);
lean_dec(v_i_268_);
v___y_261_ = v___x_272_;
goto v___jp_260_;
}
v___jp_273_:
{
lean_object* v_size_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v_size_278_ = lean_ctor_get(v___y_274_, 0);
v___x_279_ = lean_unsigned_to_nat(1u);
v___x_280_ = lean_nat_add(v_size_278_, v___x_279_);
v___x_281_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_274_, v___x_280_, v_i_277_, v___y_276_, v___y_275_);
lean_dec(v_i_277_);
v___y_261_ = v___x_281_;
goto v___jp_260_;
}
v___jp_283_:
{
lean_object* v___x_287_; 
v___x_287_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___y_286_, v___y_285_);
switch(lean_obj_tag(v___x_287_))
{
case 0:
{
lean_object* v_index_288_; lean_object* v_size_289_; lean_object* v___x_290_; 
v_index_288_ = lean_ctor_get(v___x_287_, 0);
lean_inc(v_index_288_);
lean_dec_ref_known(v___x_287_, 3);
v_size_289_ = lean_ctor_get(v___y_286_, 0);
lean_inc(v_size_289_);
v___x_290_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_286_, v_size_289_, v_index_288_, v___y_285_, v___y_284_);
lean_dec(v_index_288_);
v___y_261_ = v___x_290_;
goto v___jp_260_;
}
case 1:
{
lean_object* v_index_291_; 
v_index_291_ = lean_ctor_get(v___x_287_, 0);
lean_inc(v_index_291_);
lean_dec_ref_known(v___x_287_, 1);
v___y_265_ = v___y_284_;
v___y_266_ = v___y_286_;
v___y_267_ = v___y_285_;
v_i_268_ = v_index_291_;
goto v___jp_264_;
}
default: 
{
lean_object* v___x_292_; 
v___x_292_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_286_, v___x_282_);
if (lean_obj_tag(v___x_292_) == 0)
{
lean_object* v_index_293_; 
v_index_293_ = lean_ctor_get(v___x_292_, 0);
lean_inc(v_index_293_);
lean_dec_ref_known(v___x_292_, 1);
v___y_265_ = v___y_284_;
v___y_266_ = v___y_286_;
v___y_267_ = v___y_285_;
v_i_268_ = v_index_293_;
goto v___jp_264_;
}
else
{
lean_dec(v___y_285_);
v___y_261_ = v___y_286_;
goto v___jp_260_;
}
}
}
}
v___jp_294_:
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1___redArg(v___y_296_);
lean_dec_ref(v___y_296_);
v___x_299_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___x_298_, v___y_297_);
switch(lean_obj_tag(v___x_299_))
{
case 0:
{
lean_object* v_index_300_; lean_object* v_size_301_; lean_object* v___x_302_; 
v_index_300_ = lean_ctor_get(v___x_299_, 0);
lean_inc(v_index_300_);
lean_dec_ref_known(v___x_299_, 3);
v_size_301_ = lean_ctor_get(v___x_298_, 0);
lean_inc(v_size_301_);
v___x_302_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_298_, v_size_301_, v_index_300_, v___y_297_, v___y_295_);
lean_dec(v_index_300_);
v___y_261_ = v___x_302_;
goto v___jp_260_;
}
case 1:
{
lean_object* v_index_303_; 
v_index_303_ = lean_ctor_get(v___x_299_, 0);
lean_inc(v_index_303_);
lean_dec_ref_known(v___x_299_, 1);
v___y_274_ = v___x_298_;
v___y_275_ = v___y_295_;
v___y_276_ = v___y_297_;
v_i_277_ = v_index_303_;
goto v___jp_273_;
}
default: 
{
lean_object* v___x_304_; 
v___x_304_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_298_, v___x_282_);
if (lean_obj_tag(v___x_304_) == 0)
{
lean_object* v_index_305_; 
v_index_305_ = lean_ctor_get(v___x_304_, 0);
lean_inc(v_index_305_);
lean_dec_ref_known(v___x_304_, 1);
v___y_274_ = v___x_298_;
v___y_275_ = v___y_295_;
v___y_276_ = v___y_297_;
v_i_277_ = v_index_305_;
goto v___jp_273_;
}
else
{
lean_dec(v___y_297_);
v___y_261_ = v___x_298_;
goto v___jp_260_;
}
}
}
}
v___jp_308_:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_311_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__4_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_));
lean_inc_ref(v___y_309_);
v___x_312_ = l_Lean_Name_mkStr4(v___x_306_, v___x_307_, v___y_309_, v___x_311_);
v___x_313_ = lean_box(0);
v___x_314_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___y_310_, v___x_312_);
switch(lean_obj_tag(v___x_314_))
{
case 0:
{
lean_dec_ref_known(v___x_314_, 3);
lean_dec(v___x_312_);
v___y_261_ = v___y_310_;
goto v___jp_260_;
}
case 1:
{
lean_object* v_index_315_; lean_object* v_size_316_; lean_object* v_keyArray_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; uint8_t v___x_321_; 
v_index_315_ = lean_ctor_get(v___x_314_, 0);
lean_inc(v_index_315_);
lean_dec_ref_known(v___x_314_, 1);
v_size_316_ = lean_ctor_get(v___y_310_, 0);
v_keyArray_317_ = lean_ctor_get(v___y_310_, 1);
v___x_318_ = lean_unsigned_to_nat(1u);
v___x_319_ = lean_nat_add(v_size_316_, v___x_318_);
v___x_320_ = lean_array_get_size(v_keyArray_317_);
v___x_321_ = lean_nat_dec_lt(v___x_319_, v___x_320_);
if (v___x_321_ == 0)
{
lean_dec(v___x_319_);
lean_dec(v_index_315_);
v___y_295_ = v___x_313_;
v___y_296_ = v___y_310_;
v___y_297_ = v___x_312_;
goto v___jp_294_;
}
else
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; uint8_t v___x_326_; 
v___x_322_ = lean_unsigned_to_nat(4u);
v___x_323_ = lean_nat_mul(v___x_319_, v___x_322_);
v___x_324_ = lean_unsigned_to_nat(3u);
v___x_325_ = lean_nat_mul(v___x_320_, v___x_324_);
v___x_326_ = lean_nat_dec_le(v___x_323_, v___x_325_);
lean_dec(v___x_325_);
lean_dec(v___x_323_);
if (v___x_326_ == 0)
{
lean_dec(v___x_319_);
lean_dec(v_index_315_);
v___y_295_ = v___x_313_;
v___y_296_ = v___y_310_;
v___y_297_ = v___x_312_;
goto v___jp_294_;
}
else
{
lean_object* v___x_327_; 
v___x_327_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_310_, v___x_319_, v_index_315_, v___x_312_, v___x_313_);
lean_dec(v_index_315_);
v___y_261_ = v___x_327_;
goto v___jp_260_;
}
}
}
default: 
{
lean_object* v_size_328_; lean_object* v_keyArray_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; uint8_t v___x_333_; 
v_size_328_ = lean_ctor_get(v___y_310_, 0);
v_keyArray_329_ = lean_ctor_get(v___y_310_, 1);
v___x_330_ = lean_unsigned_to_nat(1u);
v___x_331_ = lean_nat_add(v_size_328_, v___x_330_);
v___x_332_ = lean_array_get_size(v_keyArray_329_);
v___x_333_ = lean_nat_dec_lt(v___x_331_, v___x_332_);
if (v___x_333_ == 0)
{
lean_object* v___x_334_; 
lean_dec(v___x_331_);
v___x_334_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1___redArg(v___y_310_);
lean_dec_ref(v___y_310_);
v___y_284_ = v___x_313_;
v___y_285_ = v___x_312_;
v___y_286_ = v___x_334_;
goto v___jp_283_;
}
else
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_335_ = lean_unsigned_to_nat(4u);
v___x_336_ = lean_nat_mul(v___x_331_, v___x_335_);
lean_dec(v___x_331_);
v___x_337_ = lean_unsigned_to_nat(3u);
v___x_338_ = lean_nat_mul(v___x_332_, v___x_337_);
v___x_339_ = lean_nat_dec_le(v___x_336_, v___x_338_);
lean_dec(v___x_338_);
lean_dec(v___x_336_);
if (v___x_339_ == 0)
{
lean_object* v___x_340_; 
v___x_340_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1___redArg(v___y_310_);
lean_dec_ref(v___y_310_);
v___y_284_ = v___x_313_;
v___y_285_ = v___x_312_;
v___y_286_ = v___x_340_;
goto v___jp_283_;
}
else
{
v___y_284_ = v___x_313_;
v___y_285_ = v___x_312_;
v___y_286_ = v___y_310_;
goto v___jp_283_;
}
}
}
}
}
v___jp_341_:
{
lean_object* v_size_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v_size_347_ = lean_ctor_get(v___y_345_, 0);
v___x_348_ = lean_unsigned_to_nat(1u);
v___x_349_ = lean_nat_add(v_size_347_, v___x_348_);
v___x_350_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_345_, v___x_349_, v_i_346_, v___y_344_, v___y_342_);
lean_dec(v_i_346_);
v___y_309_ = v___y_343_;
v___y_310_ = v___x_350_;
goto v___jp_308_;
}
v___jp_351_:
{
lean_object* v___x_356_; 
v___x_356_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___y_355_, v___y_354_);
switch(lean_obj_tag(v___x_356_))
{
case 0:
{
lean_object* v_index_357_; lean_object* v_size_358_; lean_object* v___x_359_; 
v_index_357_ = lean_ctor_get(v___x_356_, 0);
lean_inc(v_index_357_);
lean_dec_ref_known(v___x_356_, 3);
v_size_358_ = lean_ctor_get(v___y_355_, 0);
lean_inc(v_size_358_);
v___x_359_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_355_, v_size_358_, v_index_357_, v___y_354_, v___y_352_);
lean_dec(v_index_357_);
v___y_309_ = v___y_353_;
v___y_310_ = v___x_359_;
goto v___jp_308_;
}
case 1:
{
lean_object* v_index_360_; 
v_index_360_ = lean_ctor_get(v___x_356_, 0);
lean_inc(v_index_360_);
lean_dec_ref_known(v___x_356_, 1);
v___y_342_ = v___y_352_;
v___y_343_ = v___y_353_;
v___y_344_ = v___y_354_;
v___y_345_ = v___y_355_;
v_i_346_ = v_index_360_;
goto v___jp_341_;
}
default: 
{
lean_object* v___x_361_; 
v___x_361_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_355_, v___x_282_);
if (lean_obj_tag(v___x_361_) == 0)
{
lean_object* v_index_362_; 
v_index_362_ = lean_ctor_get(v___x_361_, 0);
lean_inc(v_index_362_);
lean_dec_ref_known(v___x_361_, 1);
v___y_342_ = v___y_352_;
v___y_343_ = v___y_353_;
v___y_344_ = v___y_354_;
v___y_345_ = v___y_355_;
v_i_346_ = v_index_362_;
goto v___jp_341_;
}
else
{
lean_dec(v___y_354_);
v___y_309_ = v___y_353_;
v___y_310_ = v___y_355_;
goto v___jp_308_;
}
}
}
}
v___jp_363_:
{
lean_object* v_size_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v_size_369_ = lean_ctor_get(v___y_367_, 0);
v___x_370_ = lean_unsigned_to_nat(1u);
v___x_371_ = lean_nat_add(v_size_369_, v___x_370_);
v___x_372_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_367_, v___x_371_, v_i_368_, v___y_366_, v___y_364_);
lean_dec(v_i_368_);
v___y_309_ = v___y_365_;
v___y_310_ = v___x_372_;
goto v___jp_308_;
}
v___jp_373_:
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1___redArg(v___y_376_);
lean_dec_ref(v___y_376_);
v___x_379_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___x_378_, v___y_377_);
switch(lean_obj_tag(v___x_379_))
{
case 0:
{
lean_object* v_index_380_; lean_object* v_size_381_; lean_object* v___x_382_; 
v_index_380_ = lean_ctor_get(v___x_379_, 0);
lean_inc(v_index_380_);
lean_dec_ref_known(v___x_379_, 3);
v_size_381_ = lean_ctor_get(v___x_378_, 0);
lean_inc(v_size_381_);
v___x_382_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_378_, v_size_381_, v_index_380_, v___y_377_, v___y_374_);
lean_dec(v_index_380_);
v___y_309_ = v___y_375_;
v___y_310_ = v___x_382_;
goto v___jp_308_;
}
case 1:
{
lean_object* v_index_383_; 
v_index_383_ = lean_ctor_get(v___x_379_, 0);
lean_inc(v_index_383_);
lean_dec_ref_known(v___x_379_, 1);
v___y_364_ = v___y_374_;
v___y_365_ = v___y_375_;
v___y_366_ = v___y_377_;
v___y_367_ = v___x_378_;
v_i_368_ = v_index_383_;
goto v___jp_363_;
}
default: 
{
lean_object* v___x_384_; 
v___x_384_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_378_, v___x_282_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_index_385_; 
v_index_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc(v_index_385_);
lean_dec_ref_known(v___x_384_, 1);
v___y_364_ = v___y_374_;
v___y_365_ = v___y_375_;
v___y_366_ = v___y_377_;
v___y_367_ = v___x_378_;
v_i_368_ = v_index_385_;
goto v___jp_363_;
}
else
{
lean_dec(v___y_377_);
v___y_309_ = v___y_375_;
v___y_310_ = v___x_378_;
goto v___jp_308_;
}
}
}
}
v___jp_386_:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_390_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__5_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_));
lean_inc_ref(v___y_387_);
v___x_391_ = l_Lean_Name_mkStr4(v___x_306_, v___x_307_, v___y_387_, v___x_390_);
v___x_392_ = lean_box(0);
v___x_393_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___y_389_, v___x_391_);
switch(lean_obj_tag(v___x_393_))
{
case 0:
{
lean_dec_ref_known(v___x_393_, 3);
lean_dec(v___x_391_);
v___y_309_ = v___y_388_;
v___y_310_ = v___y_389_;
goto v___jp_308_;
}
case 1:
{
lean_object* v_index_394_; lean_object* v_size_395_; lean_object* v_keyArray_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; uint8_t v___x_400_; 
v_index_394_ = lean_ctor_get(v___x_393_, 0);
lean_inc(v_index_394_);
lean_dec_ref_known(v___x_393_, 1);
v_size_395_ = lean_ctor_get(v___y_389_, 0);
v_keyArray_396_ = lean_ctor_get(v___y_389_, 1);
v___x_397_ = lean_unsigned_to_nat(1u);
v___x_398_ = lean_nat_add(v_size_395_, v___x_397_);
v___x_399_ = lean_array_get_size(v_keyArray_396_);
v___x_400_ = lean_nat_dec_lt(v___x_398_, v___x_399_);
if (v___x_400_ == 0)
{
lean_dec(v___x_398_);
lean_dec(v_index_394_);
v___y_374_ = v___x_392_;
v___y_375_ = v___y_388_;
v___y_376_ = v___y_389_;
v___y_377_ = v___x_391_;
goto v___jp_373_;
}
else
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; uint8_t v___x_405_; 
v___x_401_ = lean_unsigned_to_nat(4u);
v___x_402_ = lean_nat_mul(v___x_398_, v___x_401_);
v___x_403_ = lean_unsigned_to_nat(3u);
v___x_404_ = lean_nat_mul(v___x_399_, v___x_403_);
v___x_405_ = lean_nat_dec_le(v___x_402_, v___x_404_);
lean_dec(v___x_404_);
lean_dec(v___x_402_);
if (v___x_405_ == 0)
{
lean_dec(v___x_398_);
lean_dec(v_index_394_);
v___y_374_ = v___x_392_;
v___y_375_ = v___y_388_;
v___y_376_ = v___y_389_;
v___y_377_ = v___x_391_;
goto v___jp_373_;
}
else
{
lean_object* v___x_406_; 
v___x_406_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_389_, v___x_398_, v_index_394_, v___x_391_, v___x_392_);
lean_dec(v_index_394_);
v___y_309_ = v___y_388_;
v___y_310_ = v___x_406_;
goto v___jp_308_;
}
}
}
default: 
{
lean_object* v_size_407_; lean_object* v_keyArray_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; uint8_t v___x_412_; 
v_size_407_ = lean_ctor_get(v___y_389_, 0);
v_keyArray_408_ = lean_ctor_get(v___y_389_, 1);
v___x_409_ = lean_unsigned_to_nat(1u);
v___x_410_ = lean_nat_add(v_size_407_, v___x_409_);
v___x_411_ = lean_array_get_size(v_keyArray_408_);
v___x_412_ = lean_nat_dec_lt(v___x_410_, v___x_411_);
if (v___x_412_ == 0)
{
lean_object* v___x_413_; 
lean_dec(v___x_410_);
v___x_413_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1___redArg(v___y_389_);
lean_dec_ref(v___y_389_);
v___y_352_ = v___x_392_;
v___y_353_ = v___y_388_;
v___y_354_ = v___x_391_;
v___y_355_ = v___x_413_;
goto v___jp_351_;
}
else
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; uint8_t v___x_418_; 
v___x_414_ = lean_unsigned_to_nat(4u);
v___x_415_ = lean_nat_mul(v___x_410_, v___x_414_);
lean_dec(v___x_410_);
v___x_416_ = lean_unsigned_to_nat(3u);
v___x_417_ = lean_nat_mul(v___x_411_, v___x_416_);
v___x_418_ = lean_nat_dec_le(v___x_415_, v___x_417_);
lean_dec(v___x_417_);
lean_dec(v___x_415_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; 
v___x_419_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1___redArg(v___y_389_);
lean_dec_ref(v___y_389_);
v___y_352_ = v___x_392_;
v___y_353_ = v___y_388_;
v___y_354_ = v___x_391_;
v___y_355_ = v___x_419_;
goto v___jp_351_;
}
else
{
v___y_352_ = v___x_392_;
v___y_353_ = v___y_388_;
v___y_354_ = v___x_391_;
v___y_355_ = v___y_389_;
goto v___jp_351_;
}
}
}
}
}
v___jp_420_:
{
lean_object* v_size_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v_size_427_ = lean_ctor_get(v___y_423_, 0);
v___x_428_ = lean_unsigned_to_nat(1u);
v___x_429_ = lean_nat_add(v_size_427_, v___x_428_);
v___x_430_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_423_, v___x_429_, v_i_426_, v___y_424_, v___y_425_);
lean_dec(v_i_426_);
v___y_387_ = v___y_421_;
v___y_388_ = v___y_422_;
v___y_389_ = v___x_430_;
goto v___jp_386_;
}
v___jp_431_:
{
lean_object* v___x_437_; 
v___x_437_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___y_436_, v___y_434_);
switch(lean_obj_tag(v___x_437_))
{
case 0:
{
lean_object* v_index_438_; lean_object* v_size_439_; lean_object* v___x_440_; 
v_index_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_index_438_);
lean_dec_ref_known(v___x_437_, 3);
v_size_439_ = lean_ctor_get(v___y_436_, 0);
lean_inc(v_size_439_);
v___x_440_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_436_, v_size_439_, v_index_438_, v___y_434_, v___y_435_);
lean_dec(v_index_438_);
v___y_387_ = v___y_432_;
v___y_388_ = v___y_433_;
v___y_389_ = v___x_440_;
goto v___jp_386_;
}
case 1:
{
lean_object* v_index_441_; 
v_index_441_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_index_441_);
lean_dec_ref_known(v___x_437_, 1);
v___y_421_ = v___y_432_;
v___y_422_ = v___y_433_;
v___y_423_ = v___y_436_;
v___y_424_ = v___y_434_;
v___y_425_ = v___y_435_;
v_i_426_ = v_index_441_;
goto v___jp_420_;
}
default: 
{
lean_object* v___x_442_; 
v___x_442_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_436_, v___x_282_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v_index_443_; 
v_index_443_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_index_443_);
lean_dec_ref_known(v___x_442_, 1);
v___y_421_ = v___y_432_;
v___y_422_ = v___y_433_;
v___y_423_ = v___y_436_;
v___y_424_ = v___y_434_;
v___y_425_ = v___y_435_;
v_i_426_ = v_index_443_;
goto v___jp_420_;
}
else
{
lean_dec(v___y_434_);
v___y_387_ = v___y_432_;
v___y_388_ = v___y_433_;
v___y_389_ = v___y_436_;
goto v___jp_386_;
}
}
}
}
v___jp_444_:
{
lean_object* v_size_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v_size_451_ = lean_ctor_get(v___y_449_, 0);
v___x_452_ = lean_unsigned_to_nat(1u);
v___x_453_ = lean_nat_add(v_size_451_, v___x_452_);
v___x_454_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_449_, v___x_453_, v_i_450_, v___y_447_, v___y_448_);
lean_dec(v_i_450_);
v___y_387_ = v___y_445_;
v___y_388_ = v___y_446_;
v___y_389_ = v___x_454_;
goto v___jp_386_;
}
v___jp_455_:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1___redArg(v___y_458_);
lean_dec_ref(v___y_458_);
v___x_462_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___x_461_, v___y_459_);
switch(lean_obj_tag(v___x_462_))
{
case 0:
{
lean_object* v_index_463_; lean_object* v_size_464_; lean_object* v___x_465_; 
v_index_463_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_index_463_);
lean_dec_ref_known(v___x_462_, 3);
v_size_464_ = lean_ctor_get(v___x_461_, 0);
lean_inc(v_size_464_);
v___x_465_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_461_, v_size_464_, v_index_463_, v___y_459_, v___y_460_);
lean_dec(v_index_463_);
v___y_387_ = v___y_456_;
v___y_388_ = v___y_457_;
v___y_389_ = v___x_465_;
goto v___jp_386_;
}
case 1:
{
lean_object* v_index_466_; 
v_index_466_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_index_466_);
lean_dec_ref_known(v___x_462_, 1);
v___y_445_ = v___y_456_;
v___y_446_ = v___y_457_;
v___y_447_ = v___y_459_;
v___y_448_ = v___y_460_;
v___y_449_ = v___x_461_;
v_i_450_ = v_index_466_;
goto v___jp_444_;
}
default: 
{
lean_object* v___x_467_; 
v___x_467_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_461_, v___x_282_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v_index_468_; 
v_index_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc(v_index_468_);
lean_dec_ref_known(v___x_467_, 1);
v___y_445_ = v___y_456_;
v___y_446_ = v___y_457_;
v___y_447_ = v___y_459_;
v___y_448_ = v___y_460_;
v___y_449_ = v___x_461_;
v_i_450_ = v_index_468_;
goto v___jp_444_;
}
else
{
lean_dec(v___y_459_);
v___y_387_ = v___y_456_;
v___y_388_ = v___y_457_;
v___y_389_ = v___x_461_;
goto v___jp_386_;
}
}
}
}
v___jp_469_:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_473_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_));
lean_inc_ref(v___y_470_);
v___x_474_ = l_Lean_Name_mkStr4(v___x_306_, v___x_307_, v___y_470_, v___x_473_);
v___x_475_ = lean_box(0);
v___x_476_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___y_472_, v___x_474_);
switch(lean_obj_tag(v___x_476_))
{
case 0:
{
lean_dec_ref_known(v___x_476_, 3);
lean_dec(v___x_474_);
v___y_387_ = v___y_470_;
v___y_388_ = v___y_471_;
v___y_389_ = v___y_472_;
goto v___jp_386_;
}
case 1:
{
lean_object* v_index_477_; lean_object* v_size_478_; lean_object* v_keyArray_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; uint8_t v___x_483_; 
v_index_477_ = lean_ctor_get(v___x_476_, 0);
lean_inc(v_index_477_);
lean_dec_ref_known(v___x_476_, 1);
v_size_478_ = lean_ctor_get(v___y_472_, 0);
v_keyArray_479_ = lean_ctor_get(v___y_472_, 1);
v___x_480_ = lean_unsigned_to_nat(1u);
v___x_481_ = lean_nat_add(v_size_478_, v___x_480_);
v___x_482_ = lean_array_get_size(v_keyArray_479_);
v___x_483_ = lean_nat_dec_lt(v___x_481_, v___x_482_);
if (v___x_483_ == 0)
{
lean_dec(v___x_481_);
lean_dec(v_index_477_);
v___y_456_ = v___y_470_;
v___y_457_ = v___y_471_;
v___y_458_ = v___y_472_;
v___y_459_ = v___x_474_;
v___y_460_ = v___x_475_;
goto v___jp_455_;
}
else
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; uint8_t v___x_488_; 
v___x_484_ = lean_unsigned_to_nat(4u);
v___x_485_ = lean_nat_mul(v___x_481_, v___x_484_);
v___x_486_ = lean_unsigned_to_nat(3u);
v___x_487_ = lean_nat_mul(v___x_482_, v___x_486_);
v___x_488_ = lean_nat_dec_le(v___x_485_, v___x_487_);
lean_dec(v___x_487_);
lean_dec(v___x_485_);
if (v___x_488_ == 0)
{
lean_dec(v___x_481_);
lean_dec(v_index_477_);
v___y_456_ = v___y_470_;
v___y_457_ = v___y_471_;
v___y_458_ = v___y_472_;
v___y_459_ = v___x_474_;
v___y_460_ = v___x_475_;
goto v___jp_455_;
}
else
{
lean_object* v___x_489_; 
v___x_489_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_472_, v___x_481_, v_index_477_, v___x_474_, v___x_475_);
lean_dec(v_index_477_);
v___y_387_ = v___y_470_;
v___y_388_ = v___y_471_;
v___y_389_ = v___x_489_;
goto v___jp_386_;
}
}
}
default: 
{
lean_object* v_size_490_; lean_object* v_keyArray_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; uint8_t v___x_495_; 
v_size_490_ = lean_ctor_get(v___y_472_, 0);
v_keyArray_491_ = lean_ctor_get(v___y_472_, 1);
v___x_492_ = lean_unsigned_to_nat(1u);
v___x_493_ = lean_nat_add(v_size_490_, v___x_492_);
v___x_494_ = lean_array_get_size(v_keyArray_491_);
v___x_495_ = lean_nat_dec_lt(v___x_493_, v___x_494_);
if (v___x_495_ == 0)
{
lean_object* v___x_496_; 
lean_dec(v___x_493_);
v___x_496_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1___redArg(v___y_472_);
lean_dec_ref(v___y_472_);
v___y_432_ = v___y_470_;
v___y_433_ = v___y_471_;
v___y_434_ = v___x_474_;
v___y_435_ = v___x_475_;
v___y_436_ = v___x_496_;
goto v___jp_431_;
}
else
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; uint8_t v___x_501_; 
v___x_497_ = lean_unsigned_to_nat(4u);
v___x_498_ = lean_nat_mul(v___x_493_, v___x_497_);
lean_dec(v___x_493_);
v___x_499_ = lean_unsigned_to_nat(3u);
v___x_500_ = lean_nat_mul(v___x_494_, v___x_499_);
v___x_501_ = lean_nat_dec_le(v___x_498_, v___x_500_);
lean_dec(v___x_500_);
lean_dec(v___x_498_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; 
v___x_502_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1___redArg(v___y_472_);
lean_dec_ref(v___y_472_);
v___y_432_ = v___y_470_;
v___y_433_ = v___y_471_;
v___y_434_ = v___x_474_;
v___y_435_ = v___x_475_;
v___y_436_ = v___x_502_;
goto v___jp_431_;
}
else
{
v___y_432_ = v___y_470_;
v___y_433_ = v___y_471_;
v___y_434_ = v___x_474_;
v___y_435_ = v___x_475_;
v___y_436_ = v___y_472_;
goto v___jp_431_;
}
}
}
}
}
v___jp_503_:
{
lean_object* v_size_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v_size_510_ = lean_ctor_get(v___y_507_, 0);
v___x_511_ = lean_unsigned_to_nat(1u);
v___x_512_ = lean_nat_add(v_size_510_, v___x_511_);
v___x_513_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_507_, v___x_512_, v_i_509_, v___y_508_, v___y_505_);
lean_dec(v_i_509_);
v___y_470_ = v___y_504_;
v___y_471_ = v___y_506_;
v___y_472_ = v___x_513_;
goto v___jp_469_;
}
v___jp_514_:
{
lean_object* v___x_520_; 
v___x_520_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___y_519_, v___y_518_);
switch(lean_obj_tag(v___x_520_))
{
case 0:
{
lean_object* v_index_521_; lean_object* v_size_522_; lean_object* v___x_523_; 
v_index_521_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_index_521_);
lean_dec_ref_known(v___x_520_, 3);
v_size_522_ = lean_ctor_get(v___y_519_, 0);
lean_inc(v_size_522_);
v___x_523_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_519_, v_size_522_, v_index_521_, v___y_518_, v___y_516_);
lean_dec(v_index_521_);
v___y_470_ = v___y_515_;
v___y_471_ = v___y_517_;
v___y_472_ = v___x_523_;
goto v___jp_469_;
}
case 1:
{
lean_object* v_index_524_; 
v_index_524_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_index_524_);
lean_dec_ref_known(v___x_520_, 1);
v___y_504_ = v___y_515_;
v___y_505_ = v___y_516_;
v___y_506_ = v___y_517_;
v___y_507_ = v___y_519_;
v___y_508_ = v___y_518_;
v_i_509_ = v_index_524_;
goto v___jp_503_;
}
default: 
{
lean_object* v___x_525_; 
v___x_525_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_519_, v___x_282_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_index_526_; 
v_index_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_index_526_);
lean_dec_ref_known(v___x_525_, 1);
v___y_504_ = v___y_515_;
v___y_505_ = v___y_516_;
v___y_506_ = v___y_517_;
v___y_507_ = v___y_519_;
v___y_508_ = v___y_518_;
v_i_509_ = v_index_526_;
goto v___jp_503_;
}
else
{
lean_dec(v___y_518_);
v___y_470_ = v___y_515_;
v___y_471_ = v___y_517_;
v___y_472_ = v___y_519_;
goto v___jp_469_;
}
}
}
}
v___jp_527_:
{
lean_object* v_size_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v_size_534_ = lean_ctor_get(v___y_532_, 0);
v___x_535_ = lean_unsigned_to_nat(1u);
v___x_536_ = lean_nat_add(v_size_534_, v___x_535_);
v___x_537_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_532_, v___x_536_, v_i_533_, v___y_531_, v___y_529_);
lean_dec(v_i_533_);
v___y_470_ = v___y_528_;
v___y_471_ = v___y_530_;
v___y_472_ = v___x_537_;
goto v___jp_469_;
}
v___jp_538_:
{
lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_544_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1___redArg(v___y_543_);
lean_dec_ref(v___y_543_);
v___x_545_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___x_544_, v___y_542_);
switch(lean_obj_tag(v___x_545_))
{
case 0:
{
lean_object* v_index_546_; lean_object* v_size_547_; lean_object* v___x_548_; 
v_index_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_index_546_);
lean_dec_ref_known(v___x_545_, 3);
v_size_547_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_size_547_);
v___x_548_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_544_, v_size_547_, v_index_546_, v___y_542_, v___y_540_);
lean_dec(v_index_546_);
v___y_470_ = v___y_539_;
v___y_471_ = v___y_541_;
v___y_472_ = v___x_548_;
goto v___jp_469_;
}
case 1:
{
lean_object* v_index_549_; 
v_index_549_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_index_549_);
lean_dec_ref_known(v___x_545_, 1);
v___y_528_ = v___y_539_;
v___y_529_ = v___y_540_;
v___y_530_ = v___y_541_;
v___y_531_ = v___y_542_;
v___y_532_ = v___x_544_;
v_i_533_ = v_index_549_;
goto v___jp_527_;
}
default: 
{
lean_object* v___x_550_; 
v___x_550_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_544_, v___x_282_);
if (lean_obj_tag(v___x_550_) == 0)
{
lean_object* v_index_551_; 
v_index_551_ = lean_ctor_get(v___x_550_, 0);
lean_inc(v_index_551_);
lean_dec_ref_known(v___x_550_, 1);
v___y_528_ = v___y_539_;
v___y_529_ = v___y_540_;
v___y_530_ = v___y_541_;
v___y_531_ = v___y_542_;
v___y_532_ = v___x_544_;
v_i_533_ = v_index_551_;
goto v___jp_527_;
}
else
{
lean_dec(v___y_542_);
v___y_470_ = v___y_539_;
v___y_471_ = v___y_541_;
v___y_472_ = v___x_544_;
goto v___jp_469_;
}
}
}
}
v___jp_552_:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_555_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__7_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_));
v___x_556_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_));
v___x_557_ = lean_box(0);
v___x_558_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___y_554_, v___x_556_);
switch(lean_obj_tag(v___x_558_))
{
case 0:
{
lean_dec_ref_known(v___x_558_, 3);
v___y_470_ = v___x_555_;
v___y_471_ = v___y_553_;
v___y_472_ = v___y_554_;
goto v___jp_469_;
}
case 1:
{
lean_object* v_index_559_; lean_object* v_size_560_; lean_object* v_keyArray_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; uint8_t v___x_565_; 
v_index_559_ = lean_ctor_get(v___x_558_, 0);
lean_inc(v_index_559_);
lean_dec_ref_known(v___x_558_, 1);
v_size_560_ = lean_ctor_get(v___y_554_, 0);
v_keyArray_561_ = lean_ctor_get(v___y_554_, 1);
v___x_562_ = lean_unsigned_to_nat(1u);
v___x_563_ = lean_nat_add(v_size_560_, v___x_562_);
v___x_564_ = lean_array_get_size(v_keyArray_561_);
v___x_565_ = lean_nat_dec_lt(v___x_563_, v___x_564_);
if (v___x_565_ == 0)
{
lean_dec(v___x_563_);
lean_dec(v_index_559_);
v___y_539_ = v___x_555_;
v___y_540_ = v___x_557_;
v___y_541_ = v___y_553_;
v___y_542_ = v___x_556_;
v___y_543_ = v___y_554_;
goto v___jp_538_;
}
else
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; uint8_t v___x_570_; 
v___x_566_ = lean_unsigned_to_nat(4u);
v___x_567_ = lean_nat_mul(v___x_563_, v___x_566_);
v___x_568_ = lean_unsigned_to_nat(3u);
v___x_569_ = lean_nat_mul(v___x_564_, v___x_568_);
v___x_570_ = lean_nat_dec_le(v___x_567_, v___x_569_);
lean_dec(v___x_569_);
lean_dec(v___x_567_);
if (v___x_570_ == 0)
{
lean_dec(v___x_563_);
lean_dec(v_index_559_);
v___y_539_ = v___x_555_;
v___y_540_ = v___x_557_;
v___y_541_ = v___y_553_;
v___y_542_ = v___x_556_;
v___y_543_ = v___y_554_;
goto v___jp_538_;
}
else
{
lean_object* v___x_571_; 
v___x_571_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_554_, v___x_563_, v_index_559_, v___x_556_, v___x_557_);
lean_dec(v_index_559_);
v___y_470_ = v___x_555_;
v___y_471_ = v___y_553_;
v___y_472_ = v___x_571_;
goto v___jp_469_;
}
}
}
default: 
{
lean_object* v_size_572_; lean_object* v_keyArray_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; uint8_t v___x_577_; 
v_size_572_ = lean_ctor_get(v___y_554_, 0);
v_keyArray_573_ = lean_ctor_get(v___y_554_, 1);
v___x_574_ = lean_unsigned_to_nat(1u);
v___x_575_ = lean_nat_add(v_size_572_, v___x_574_);
v___x_576_ = lean_array_get_size(v_keyArray_573_);
v___x_577_ = lean_nat_dec_lt(v___x_575_, v___x_576_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; 
lean_dec(v___x_575_);
v___x_578_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1___redArg(v___y_554_);
lean_dec_ref(v___y_554_);
v___y_515_ = v___x_555_;
v___y_516_ = v___x_557_;
v___y_517_ = v___y_553_;
v___y_518_ = v___x_556_;
v___y_519_ = v___x_578_;
goto v___jp_514_;
}
else
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; uint8_t v___x_583_; 
v___x_579_ = lean_unsigned_to_nat(4u);
v___x_580_ = lean_nat_mul(v___x_575_, v___x_579_);
lean_dec(v___x_575_);
v___x_581_ = lean_unsigned_to_nat(3u);
v___x_582_ = lean_nat_mul(v___x_576_, v___x_581_);
v___x_583_ = lean_nat_dec_le(v___x_580_, v___x_582_);
lean_dec(v___x_582_);
lean_dec(v___x_580_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; 
v___x_584_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1___redArg(v___y_554_);
lean_dec_ref(v___y_554_);
v___y_515_ = v___x_555_;
v___y_516_ = v___x_557_;
v___y_517_ = v___y_553_;
v___y_518_ = v___x_556_;
v___y_519_ = v___x_584_;
goto v___jp_514_;
}
else
{
v___y_515_ = v___x_555_;
v___y_516_ = v___x_557_;
v___y_517_ = v___y_553_;
v___y_518_ = v___x_556_;
v___y_519_ = v___y_554_;
goto v___jp_514_;
}
}
}
}
}
v___jp_585_:
{
lean_object* v_size_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v_size_591_ = lean_ctor_get(v___y_587_, 0);
v___x_592_ = lean_unsigned_to_nat(1u);
v___x_593_ = lean_nat_add(v_size_591_, v___x_592_);
v___x_594_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_587_, v___x_593_, v_i_590_, v___y_588_, v___y_589_);
lean_dec(v_i_590_);
v___y_553_ = v___y_586_;
v___y_554_ = v___x_594_;
goto v___jp_552_;
}
v___jp_595_:
{
lean_object* v___x_600_; 
v___x_600_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___y_599_, v___y_597_);
switch(lean_obj_tag(v___x_600_))
{
case 0:
{
lean_object* v_index_601_; lean_object* v_size_602_; lean_object* v___x_603_; 
v_index_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_index_601_);
lean_dec_ref_known(v___x_600_, 3);
v_size_602_ = lean_ctor_get(v___y_599_, 0);
lean_inc(v_size_602_);
v___x_603_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_599_, v_size_602_, v_index_601_, v___y_597_, v___y_598_);
lean_dec(v_index_601_);
v___y_553_ = v___y_596_;
v___y_554_ = v___x_603_;
goto v___jp_552_;
}
case 1:
{
lean_object* v_index_604_; 
v_index_604_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_index_604_);
lean_dec_ref_known(v___x_600_, 1);
v___y_586_ = v___y_596_;
v___y_587_ = v___y_599_;
v___y_588_ = v___y_597_;
v___y_589_ = v___y_598_;
v_i_590_ = v_index_604_;
goto v___jp_585_;
}
default: 
{
lean_object* v___x_605_; 
v___x_605_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_599_, v___x_282_);
if (lean_obj_tag(v___x_605_) == 0)
{
lean_object* v_index_606_; 
v_index_606_ = lean_ctor_get(v___x_605_, 0);
lean_inc(v_index_606_);
lean_dec_ref_known(v___x_605_, 1);
v___y_586_ = v___y_596_;
v___y_587_ = v___y_599_;
v___y_588_ = v___y_597_;
v___y_589_ = v___y_598_;
v_i_590_ = v_index_606_;
goto v___jp_585_;
}
else
{
lean_dec(v___y_597_);
v___y_553_ = v___y_596_;
v___y_554_ = v___y_599_;
goto v___jp_552_;
}
}
}
}
v___jp_607_:
{
lean_object* v_size_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v_size_613_ = lean_ctor_get(v___y_609_, 0);
v___x_614_ = lean_unsigned_to_nat(1u);
v___x_615_ = lean_nat_add(v_size_613_, v___x_614_);
v___x_616_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_609_, v___x_615_, v_i_612_, v___y_610_, v___y_611_);
lean_dec(v_i_612_);
v___y_553_ = v___y_608_;
v___y_554_ = v___x_616_;
goto v___jp_552_;
}
v___jp_617_:
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1___redArg(v___y_620_);
lean_dec_ref(v___y_620_);
v___x_623_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___x_622_, v___y_619_);
switch(lean_obj_tag(v___x_623_))
{
case 0:
{
lean_object* v_index_624_; lean_object* v_size_625_; lean_object* v___x_626_; 
v_index_624_ = lean_ctor_get(v___x_623_, 0);
lean_inc(v_index_624_);
lean_dec_ref_known(v___x_623_, 3);
v_size_625_ = lean_ctor_get(v___x_622_, 0);
lean_inc(v_size_625_);
v___x_626_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_622_, v_size_625_, v_index_624_, v___y_619_, v___y_621_);
lean_dec(v_index_624_);
v___y_553_ = v___y_618_;
v___y_554_ = v___x_626_;
goto v___jp_552_;
}
case 1:
{
lean_object* v_index_627_; 
v_index_627_ = lean_ctor_get(v___x_623_, 0);
lean_inc(v_index_627_);
lean_dec_ref_known(v___x_623_, 1);
v___y_608_ = v___y_618_;
v___y_609_ = v___x_622_;
v___y_610_ = v___y_619_;
v___y_611_ = v___y_621_;
v_i_612_ = v_index_627_;
goto v___jp_607_;
}
default: 
{
lean_object* v___x_628_; 
v___x_628_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_622_, v___x_282_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v_index_629_; 
v_index_629_ = lean_ctor_get(v___x_628_, 0);
lean_inc(v_index_629_);
lean_dec_ref_known(v___x_628_, 1);
v___y_608_ = v___y_618_;
v___y_609_ = v___x_622_;
v___y_610_ = v___y_619_;
v___y_611_ = v___y_621_;
v_i_612_ = v_index_629_;
goto v___jp_607_;
}
else
{
lean_dec(v___y_619_);
v___y_553_ = v___y_618_;
v___y_554_ = v___x_622_;
goto v___jp_552_;
}
}
}
}
v___jp_630_:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_633_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__10_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_));
lean_inc_ref(v___y_631_);
v___x_634_ = l_Lean_Name_mkStr4(v___x_306_, v___x_307_, v___y_631_, v___x_633_);
v___x_635_ = lean_box(0);
v___x_636_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___y_632_, v___x_634_);
switch(lean_obj_tag(v___x_636_))
{
case 0:
{
lean_dec_ref_known(v___x_636_, 3);
lean_dec(v___x_634_);
v___y_553_ = v___y_631_;
v___y_554_ = v___y_632_;
goto v___jp_552_;
}
case 1:
{
lean_object* v_index_637_; lean_object* v_size_638_; lean_object* v_keyArray_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; uint8_t v___x_643_; 
v_index_637_ = lean_ctor_get(v___x_636_, 0);
lean_inc(v_index_637_);
lean_dec_ref_known(v___x_636_, 1);
v_size_638_ = lean_ctor_get(v___y_632_, 0);
v_keyArray_639_ = lean_ctor_get(v___y_632_, 1);
v___x_640_ = lean_unsigned_to_nat(1u);
v___x_641_ = lean_nat_add(v_size_638_, v___x_640_);
v___x_642_ = lean_array_get_size(v_keyArray_639_);
v___x_643_ = lean_nat_dec_lt(v___x_641_, v___x_642_);
if (v___x_643_ == 0)
{
lean_dec(v___x_641_);
lean_dec(v_index_637_);
v___y_618_ = v___y_631_;
v___y_619_ = v___x_634_;
v___y_620_ = v___y_632_;
v___y_621_ = v___x_635_;
goto v___jp_617_;
}
else
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_644_ = lean_unsigned_to_nat(4u);
v___x_645_ = lean_nat_mul(v___x_641_, v___x_644_);
v___x_646_ = lean_unsigned_to_nat(3u);
v___x_647_ = lean_nat_mul(v___x_642_, v___x_646_);
v___x_648_ = lean_nat_dec_le(v___x_645_, v___x_647_);
lean_dec(v___x_647_);
lean_dec(v___x_645_);
if (v___x_648_ == 0)
{
lean_dec(v___x_641_);
lean_dec(v_index_637_);
v___y_618_ = v___y_631_;
v___y_619_ = v___x_634_;
v___y_620_ = v___y_632_;
v___y_621_ = v___x_635_;
goto v___jp_617_;
}
else
{
lean_object* v___x_649_; 
v___x_649_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_632_, v___x_641_, v_index_637_, v___x_634_, v___x_635_);
lean_dec(v_index_637_);
v___y_553_ = v___y_631_;
v___y_554_ = v___x_649_;
goto v___jp_552_;
}
}
}
default: 
{
lean_object* v_size_650_; lean_object* v_keyArray_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; uint8_t v___x_655_; 
v_size_650_ = lean_ctor_get(v___y_632_, 0);
v_keyArray_651_ = lean_ctor_get(v___y_632_, 1);
v___x_652_ = lean_unsigned_to_nat(1u);
v___x_653_ = lean_nat_add(v_size_650_, v___x_652_);
v___x_654_ = lean_array_get_size(v_keyArray_651_);
v___x_655_ = lean_nat_dec_lt(v___x_653_, v___x_654_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; 
lean_dec(v___x_653_);
v___x_656_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1___redArg(v___y_632_);
lean_dec_ref(v___y_632_);
v___y_596_ = v___y_631_;
v___y_597_ = v___x_634_;
v___y_598_ = v___x_635_;
v___y_599_ = v___x_656_;
goto v___jp_595_;
}
else
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; uint8_t v___x_661_; 
v___x_657_ = lean_unsigned_to_nat(4u);
v___x_658_ = lean_nat_mul(v___x_653_, v___x_657_);
lean_dec(v___x_653_);
v___x_659_ = lean_unsigned_to_nat(3u);
v___x_660_ = lean_nat_mul(v___x_654_, v___x_659_);
v___x_661_ = lean_nat_dec_le(v___x_658_, v___x_660_);
lean_dec(v___x_660_);
lean_dec(v___x_658_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; 
v___x_662_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1___redArg(v___y_632_);
lean_dec_ref(v___y_632_);
v___y_596_ = v___y_631_;
v___y_597_ = v___x_634_;
v___y_598_ = v___x_635_;
v___y_599_ = v___x_662_;
goto v___jp_595_;
}
else
{
v___y_596_ = v___y_631_;
v___y_597_ = v___x_634_;
v___y_598_ = v___x_635_;
v___y_599_ = v___y_632_;
goto v___jp_595_;
}
}
}
}
}
v___jp_663_:
{
lean_object* v_size_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v_size_669_ = lean_ctor_get(v___y_664_, 0);
v___x_670_ = lean_unsigned_to_nat(1u);
v___x_671_ = lean_nat_add(v_size_669_, v___x_670_);
v___x_672_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_664_, v___x_671_, v_i_668_, v___y_667_, v___y_666_);
lean_dec(v_i_668_);
v___y_631_ = v___y_665_;
v___y_632_ = v___x_672_;
goto v___jp_630_;
}
v___jp_673_:
{
lean_object* v___x_678_; 
v___x_678_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___y_677_, v___y_676_);
switch(lean_obj_tag(v___x_678_))
{
case 0:
{
lean_object* v_index_679_; lean_object* v_size_680_; lean_object* v___x_681_; 
v_index_679_ = lean_ctor_get(v___x_678_, 0);
lean_inc(v_index_679_);
lean_dec_ref_known(v___x_678_, 3);
v_size_680_ = lean_ctor_get(v___y_677_, 0);
lean_inc(v_size_680_);
v___x_681_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_677_, v_size_680_, v_index_679_, v___y_676_, v___y_675_);
lean_dec(v_index_679_);
v___y_631_ = v___y_674_;
v___y_632_ = v___x_681_;
goto v___jp_630_;
}
case 1:
{
lean_object* v_index_682_; 
v_index_682_ = lean_ctor_get(v___x_678_, 0);
lean_inc(v_index_682_);
lean_dec_ref_known(v___x_678_, 1);
v___y_664_ = v___y_677_;
v___y_665_ = v___y_674_;
v___y_666_ = v___y_675_;
v___y_667_ = v___y_676_;
v_i_668_ = v_index_682_;
goto v___jp_663_;
}
default: 
{
lean_object* v___x_683_; 
v___x_683_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_677_, v___x_282_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v_index_684_; 
v_index_684_ = lean_ctor_get(v___x_683_, 0);
lean_inc(v_index_684_);
lean_dec_ref_known(v___x_683_, 1);
v___y_664_ = v___y_677_;
v___y_665_ = v___y_674_;
v___y_666_ = v___y_675_;
v___y_667_ = v___y_676_;
v_i_668_ = v_index_684_;
goto v___jp_663_;
}
else
{
lean_dec(v___y_676_);
v___y_631_ = v___y_674_;
v___y_632_ = v___y_677_;
goto v___jp_630_;
}
}
}
}
v___jp_685_:
{
lean_object* v_size_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v_size_691_ = lean_ctor_get(v___y_689_, 0);
v___x_692_ = lean_unsigned_to_nat(1u);
v___x_693_ = lean_nat_add(v_size_691_, v___x_692_);
v___x_694_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_689_, v___x_693_, v_i_690_, v___y_688_, v___y_687_);
lean_dec(v_i_690_);
v___y_631_ = v___y_686_;
v___y_632_ = v___x_694_;
goto v___jp_630_;
}
v___jp_695_:
{
lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_700_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1___redArg(v___y_698_);
lean_dec_ref(v___y_698_);
v___x_701_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___x_700_, v___y_699_);
switch(lean_obj_tag(v___x_701_))
{
case 0:
{
lean_object* v_index_702_; lean_object* v_size_703_; lean_object* v___x_704_; 
v_index_702_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_index_702_);
lean_dec_ref_known(v___x_701_, 3);
v_size_703_ = lean_ctor_get(v___x_700_, 0);
lean_inc(v_size_703_);
v___x_704_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_700_, v_size_703_, v_index_702_, v___y_699_, v___y_697_);
lean_dec(v_index_702_);
v___y_631_ = v___y_696_;
v___y_632_ = v___x_704_;
goto v___jp_630_;
}
case 1:
{
lean_object* v_index_705_; 
v_index_705_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_index_705_);
lean_dec_ref_known(v___x_701_, 1);
v___y_686_ = v___y_696_;
v___y_687_ = v___y_697_;
v___y_688_ = v___y_699_;
v___y_689_ = v___x_700_;
v_i_690_ = v_index_705_;
goto v___jp_685_;
}
default: 
{
lean_object* v___x_706_; 
v___x_706_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_700_, v___x_282_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_index_707_; 
v_index_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_index_707_);
lean_dec_ref_known(v___x_706_, 1);
v___y_686_ = v___y_696_;
v___y_687_ = v___y_697_;
v___y_688_ = v___y_699_;
v___y_689_ = v___x_700_;
v_i_690_ = v_index_707_;
goto v___jp_685_;
}
else
{
lean_dec(v___y_699_);
v___y_631_ = v___y_696_;
v___y_632_ = v___x_700_;
goto v___jp_630_;
}
}
}
}
v___jp_708_:
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_710_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__11_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_));
v___x_711_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__13_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_));
v___x_712_ = lean_box(0);
v___x_713_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___y_709_, v___x_711_);
switch(lean_obj_tag(v___x_713_))
{
case 0:
{
lean_dec_ref_known(v___x_713_, 3);
v___y_631_ = v___x_710_;
v___y_632_ = v___y_709_;
goto v___jp_630_;
}
case 1:
{
lean_object* v_index_714_; lean_object* v_size_715_; lean_object* v_keyArray_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; uint8_t v___x_720_; 
v_index_714_ = lean_ctor_get(v___x_713_, 0);
lean_inc(v_index_714_);
lean_dec_ref_known(v___x_713_, 1);
v_size_715_ = lean_ctor_get(v___y_709_, 0);
v_keyArray_716_ = lean_ctor_get(v___y_709_, 1);
v___x_717_ = lean_unsigned_to_nat(1u);
v___x_718_ = lean_nat_add(v_size_715_, v___x_717_);
v___x_719_ = lean_array_get_size(v_keyArray_716_);
v___x_720_ = lean_nat_dec_lt(v___x_718_, v___x_719_);
if (v___x_720_ == 0)
{
lean_dec(v___x_718_);
lean_dec(v_index_714_);
v___y_696_ = v___x_710_;
v___y_697_ = v___x_712_;
v___y_698_ = v___y_709_;
v___y_699_ = v___x_711_;
goto v___jp_695_;
}
else
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; uint8_t v___x_725_; 
v___x_721_ = lean_unsigned_to_nat(4u);
v___x_722_ = lean_nat_mul(v___x_718_, v___x_721_);
v___x_723_ = lean_unsigned_to_nat(3u);
v___x_724_ = lean_nat_mul(v___x_719_, v___x_723_);
v___x_725_ = lean_nat_dec_le(v___x_722_, v___x_724_);
lean_dec(v___x_724_);
lean_dec(v___x_722_);
if (v___x_725_ == 0)
{
lean_dec(v___x_718_);
lean_dec(v_index_714_);
v___y_696_ = v___x_710_;
v___y_697_ = v___x_712_;
v___y_698_ = v___y_709_;
v___y_699_ = v___x_711_;
goto v___jp_695_;
}
else
{
lean_object* v___x_726_; 
v___x_726_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_709_, v___x_718_, v_index_714_, v___x_711_, v___x_712_);
lean_dec(v_index_714_);
v___y_631_ = v___x_710_;
v___y_632_ = v___x_726_;
goto v___jp_630_;
}
}
}
default: 
{
lean_object* v_size_727_; lean_object* v_keyArray_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; uint8_t v___x_732_; 
v_size_727_ = lean_ctor_get(v___y_709_, 0);
v_keyArray_728_ = lean_ctor_get(v___y_709_, 1);
v___x_729_ = lean_unsigned_to_nat(1u);
v___x_730_ = lean_nat_add(v_size_727_, v___x_729_);
v___x_731_ = lean_array_get_size(v_keyArray_728_);
v___x_732_ = lean_nat_dec_lt(v___x_730_, v___x_731_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; 
lean_dec(v___x_730_);
v___x_733_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1___redArg(v___y_709_);
lean_dec_ref(v___y_709_);
v___y_674_ = v___x_710_;
v___y_675_ = v___x_712_;
v___y_676_ = v___x_711_;
v___y_677_ = v___x_733_;
goto v___jp_673_;
}
else
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; uint8_t v___x_738_; 
v___x_734_ = lean_unsigned_to_nat(4u);
v___x_735_ = lean_nat_mul(v___x_730_, v___x_734_);
lean_dec(v___x_730_);
v___x_736_ = lean_unsigned_to_nat(3u);
v___x_737_ = lean_nat_mul(v___x_731_, v___x_736_);
v___x_738_ = lean_nat_dec_le(v___x_735_, v___x_737_);
lean_dec(v___x_737_);
lean_dec(v___x_735_);
if (v___x_738_ == 0)
{
lean_object* v___x_739_; 
v___x_739_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1___redArg(v___y_709_);
lean_dec_ref(v___y_709_);
v___y_674_ = v___x_710_;
v___y_675_ = v___x_712_;
v___y_676_ = v___x_711_;
v___y_677_ = v___x_739_;
goto v___jp_673_;
}
else
{
v___y_674_ = v___x_710_;
v___y_675_ = v___x_712_;
v___y_676_ = v___x_711_;
v___y_677_ = v___y_709_;
goto v___jp_673_;
}
}
}
}
}
v___jp_743_:
{
lean_object* v_size_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v_size_746_ = lean_ctor_get(v___y_744_, 0);
v___x_747_ = lean_unsigned_to_nat(1u);
v___x_748_ = lean_nat_add(v_size_746_, v___x_747_);
v___x_749_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_744_, v___x_748_, v_i_745_, v___x_741_, v___x_742_);
lean_dec(v_i_745_);
v___y_709_ = v___x_749_;
goto v___jp_708_;
}
v___jp_750_:
{
lean_object* v___x_752_; 
v___x_752_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___y_751_, v___x_741_);
switch(lean_obj_tag(v___x_752_))
{
case 0:
{
lean_object* v_index_753_; lean_object* v_size_754_; lean_object* v___x_755_; 
v_index_753_ = lean_ctor_get(v___x_752_, 0);
lean_inc(v_index_753_);
lean_dec_ref_known(v___x_752_, 3);
v_size_754_ = lean_ctor_get(v___y_751_, 0);
lean_inc(v_size_754_);
v___x_755_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_751_, v_size_754_, v_index_753_, v___x_741_, v___x_742_);
lean_dec(v_index_753_);
v___y_709_ = v___x_755_;
goto v___jp_708_;
}
case 1:
{
lean_object* v_index_756_; 
v_index_756_ = lean_ctor_get(v___x_752_, 0);
lean_inc(v_index_756_);
lean_dec_ref_known(v___x_752_, 1);
v___y_744_ = v___y_751_;
v_i_745_ = v_index_756_;
goto v___jp_743_;
}
default: 
{
lean_object* v___x_757_; 
v___x_757_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_751_, v___x_282_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v_index_758_; 
v_index_758_ = lean_ctor_get(v___x_757_, 0);
lean_inc(v_index_758_);
lean_dec_ref_known(v___x_757_, 1);
v___y_744_ = v___y_751_;
v_i_745_ = v_index_758_;
goto v___jp_743_;
}
else
{
v___y_709_ = v___y_751_;
goto v___jp_708_;
}
}
}
}
v___jp_759_:
{
lean_object* v_size_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v_size_762_ = lean_ctor_get(v___y_760_, 0);
v___x_763_ = lean_unsigned_to_nat(1u);
v___x_764_ = lean_nat_add(v_size_762_, v___x_763_);
v___x_765_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_760_, v___x_764_, v_i_761_, v___x_741_, v___x_742_);
v___y_709_ = v___x_765_;
goto v___jp_708_;
}
v___jp_766_:
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__20_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__20_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__20_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
v___x_768_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__21_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__21_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__21_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
switch(lean_obj_tag(v___x_768_))
{
case 0:
{
lean_object* v_index_769_; lean_object* v_size_770_; lean_object* v___x_771_; 
v_index_769_ = lean_ctor_get(v___x_768_, 0);
v_size_770_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_size_770_);
v___x_771_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_767_, v_size_770_, v_index_769_, v___x_741_, v___x_742_);
v___y_709_ = v___x_771_;
goto v___jp_708_;
}
case 1:
{
lean_object* v_index_772_; 
v_index_772_ = lean_ctor_get(v___x_768_, 0);
v___y_760_ = v___x_767_;
v_i_761_ = v_index_772_;
goto v___jp_759_;
}
default: 
{
lean_object* v___x_773_; 
v___x_773_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__22_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__22_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__22_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v_index_774_; 
v_index_774_ = lean_ctor_get(v___x_773_, 0);
v___y_760_ = v___x_767_;
v_i_761_ = v_index_774_;
goto v___jp_759_;
}
else
{
v___y_709_ = v___x_767_;
goto v___jp_708_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2____boxed(lean_object* v_a_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_();
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_804_, lean_object* v_m_805_, lean_object* v_query_806_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v_m_805_, v_query_806_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b2_808_, lean_object* v_m_809_, lean_object* v_query_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0(v_00_u03b2_808_, v_m_809_, v_query_810_);
lean_dec(v_query_810_);
lean_dec_ref(v_m_809_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_812_, lean_object* v_m_813_){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1___redArg(v_m_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b2_815_, lean_object* v_m_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1(v_00_u03b2_815_, v_m_816_);
lean_dec_ref(v_m_816_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_818_, lean_object* v_m_819_, lean_object* v_query_820_, lean_object* v_x_821_, lean_object* v_x_822_, lean_object* v_x_823_, lean_object* v_x_824_){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0___redArg(v_m_819_, v_query_820_, v_x_821_, v_x_822_, v_x_823_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_826_, lean_object* v_m_827_, lean_object* v_query_828_, lean_object* v_x_829_, lean_object* v_x_830_, lean_object* v_x_831_, lean_object* v_x_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_826_, v_m_827_, v_query_828_, v_x_829_, v_x_830_, v_x_831_, v_x_832_);
lean_dec(v_query_828_);
lean_dec_ref(v_m_827_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03b2_834_, lean_object* v_init_835_, lean_object* v_b_836_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1_spec__2___redArg(v_init_835_, v_b_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03b2_838_, lean_object* v_init_839_, lean_object* v_b_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1_spec__2(v_00_u03b2_838_, v_init_839_, v_b_840_);
lean_dec_ref(v_b_840_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1_spec__2_spec__3(lean_object* v_00_u03b2_842_, lean_object* v_b_843_, lean_object* v_acc_844_, lean_object* v_i_845_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v_b_843_, v_acc_844_, v_i_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_847_, lean_object* v_b_848_, lean_object* v_acc_849_, lean_object* v_i_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__1_spec__2_spec__3(v_00_u03b2_847_, v_b_848_, v_acc_849_, v_i_850_);
lean_dec_ref(v_b_848_);
return v_res_851_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_Extra_UnreachableTactic_isIgnoreTacticKind(lean_object* v_ignoreTacticKinds_853_, lean_object* v_k_854_){
_start:
{
if (lean_obj_tag(v_k_854_) == 1)
{
lean_object* v_str_855_; lean_object* v___x_856_; uint8_t v___x_857_; 
v_str_855_ = lean_ctor_get(v_k_854_, 1);
v___x_856_ = ((lean_object*)(l_Lean_Linter_Extra_UnreachableTactic_isIgnoreTacticKind___closed__0));
v___x_857_ = lean_string_dec_eq(v_str_855_, v___x_856_);
if (v___x_857_ == 0)
{
uint8_t v___x_858_; 
v___x_858_ = l_Lean_NameHashSet_contains(v_ignoreTacticKinds_853_, v_k_854_);
return v___x_858_;
}
else
{
return v___x_857_;
}
}
else
{
uint8_t v___x_859_; 
v___x_859_ = l_Lean_NameHashSet_contains(v_ignoreTacticKinds_853_, v_k_854_);
return v___x_859_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_isIgnoreTacticKind___boxed(lean_object* v_ignoreTacticKinds_860_, lean_object* v_k_861_){
_start:
{
uint8_t v_res_862_; lean_object* v_r_863_; 
v_res_862_ = l_Lean_Linter_Extra_UnreachableTactic_isIgnoreTacticKind(v_ignoreTacticKinds_860_, v_k_861_);
lean_dec(v_k_861_);
lean_dec_ref(v_ignoreTacticKinds_860_);
v_r_863_ = lean_box(v_res_862_);
return v_r_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_addIgnoreTacticKind(lean_object* v_kind_864_){
_start:
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_866_ = l_Lean_Linter_Extra_UnreachableTactic_ignoreTacticKindsRef;
v___x_867_ = lean_st_ref_take(v___x_866_);
v___x_868_ = l_Lean_NameHashSet_insert(v___x_867_, v_kind_864_);
v___x_869_ = lean_st_ref_put(v___x_866_, v___x_868_);
v___x_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_addIgnoreTacticKind___boxed(lean_object* v_kind_871_, lean_object* v_a_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Lean_Linter_Extra_UnreachableTactic_addIgnoreTacticKind(v_kind_871_);
return v_res_873_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__0(void){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = l_instMonadEIO(lean_box(0));
return v___x_874_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__1(void){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = lean_obj_once(&l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__0, &l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__0_once, _init_l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__0);
v___x_876_ = l_StateRefT_x27_instMonad___redArg(v___x_875_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_getTactics___lam__0___boxed(lean_object* v_ignoreTacticKinds_879_, lean_object* v_isTacKind_880_, lean_object* v_x_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Lean_Linter_Extra_UnreachableTactic_getTactics___lam__0(v_ignoreTacticKinds_879_, v_isTacKind_880_, v_x_881_, v___y_882_, v___y_883_);
lean_dec(v___y_883_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_getTactics(lean_object* v_ignoreTacticKinds_886_, lean_object* v_isTacKind_887_, lean_object* v_stx_888_, lean_object* v_a_889_){
_start:
{
lean_object* v___y_892_; lean_object* v___y_893_; lean_object* v___y_894_; lean_object* v___y_898_; lean_object* v___y_899_; lean_object* v___y_900_; lean_object* v___y_901_; lean_object* v_i_902_; lean_object* v___y_908_; lean_object* v___y_909_; lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v___y_912_; lean_object* v___y_913_; lean_object* v___y_923_; lean_object* v___y_924_; lean_object* v___y_925_; lean_object* v___y_926_; lean_object* v_i_927_; lean_object* v___y_933_; lean_object* v___y_934_; lean_object* v___y_935_; lean_object* v___y_936_; lean_object* v___y_937_; lean_object* v___y_938_; lean_object* v___x_948_; 
v___x_948_ = lean_obj_once(&l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__1, &l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__1_once, _init_l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__1);
if (lean_obj_tag(v_stx_888_) == 1)
{
lean_object* v_kind_949_; lean_object* v_args_950_; lean_object* v___y_952_; lean_object* v___y_997_; uint8_t v___x_998_; 
v_kind_949_ = lean_ctor_get(v_stx_888_, 1);
v_args_950_ = lean_ctor_get(v_stx_888_, 2);
v___x_998_ = l_Lean_Linter_Extra_UnreachableTactic_isIgnoreTacticKind(v_ignoreTacticKinds_886_, v_kind_949_);
if (v___x_998_ == 0)
{
lean_object* v___x_999_; lean_object* v___x_1000_; uint8_t v___x_1001_; 
v___x_999_ = lean_unsigned_to_nat(0u);
v___x_1000_ = lean_array_get_size(v_args_950_);
v___x_1001_ = lean_nat_dec_lt(v___x_999_, v___x_1000_);
if (v___x_1001_ == 0)
{
lean_dec_ref(v_ignoreTacticKinds_886_);
v___y_952_ = v_a_889_;
goto v___jp_951_;
}
else
{
lean_object* v___f_1002_; lean_object* v___x_1003_; uint8_t v___x_1004_; 
lean_inc_ref(v_isTacKind_887_);
v___f_1002_ = lean_alloc_closure((void*)(l_Lean_Linter_Extra_UnreachableTactic_getTactics___lam__0___boxed), 6, 2);
lean_closure_set(v___f_1002_, 0, v_ignoreTacticKinds_886_);
lean_closure_set(v___f_1002_, 1, v_isTacKind_887_);
v___x_1003_ = lean_box(0);
v___x_1004_ = lean_nat_dec_le(v___x_1000_, v___x_1000_);
if (v___x_1004_ == 0)
{
if (v___x_1001_ == 0)
{
lean_dec_ref(v___f_1002_);
v___y_952_ = v_a_889_;
goto v___jp_951_;
}
else
{
size_t v___x_1005_; size_t v___x_1006_; lean_object* v___x_1876__overap_1007_; lean_object* v___x_1008_; 
v___x_1005_ = ((size_t)0ULL);
v___x_1006_ = lean_usize_of_nat(v___x_1000_);
lean_inc_ref(v_args_950_);
v___x_1876__overap_1007_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_948_, v___f_1002_, v_args_950_, v___x_1005_, v___x_1006_, v___x_1003_);
lean_inc(v_a_889_);
v___x_1008_ = lean_apply_2(v___x_1876__overap_1007_, v_a_889_, lean_box(0));
v___y_997_ = v___x_1008_;
goto v___jp_996_;
}
}
else
{
size_t v___x_1009_; size_t v___x_1010_; lean_object* v___x_1880__overap_1011_; lean_object* v___x_1012_; 
v___x_1009_ = ((size_t)0ULL);
v___x_1010_ = lean_usize_of_nat(v___x_1000_);
lean_inc_ref(v_args_950_);
v___x_1880__overap_1011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_948_, v___f_1002_, v_args_950_, v___x_1009_, v___x_1010_, v___x_1003_);
lean_inc(v_a_889_);
v___x_1012_ = lean_apply_2(v___x_1880__overap_1011_, v_a_889_, lean_box(0));
v___y_997_ = v___x_1012_;
goto v___jp_996_;
}
}
}
else
{
lean_dec_ref(v_ignoreTacticKinds_886_);
v___y_952_ = v_a_889_;
goto v___jp_951_;
}
v___jp_951_:
{
lean_object* v___x_953_; uint8_t v___x_954_; 
lean_inc(v_kind_949_);
v___x_953_ = lean_apply_1(v_isTacKind_887_, v_kind_949_);
v___x_954_ = lean_unbox(v___x_953_);
if (v___x_954_ == 0)
{
lean_object* v___x_955_; lean_object* v___x_956_; 
lean_dec_ref_known(v_stx_888_, 3);
v___x_955_ = lean_box(0);
v___x_956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_956_, 0, v___x_955_);
return v___x_956_;
}
else
{
uint8_t v___x_957_; lean_object* v___x_958_; 
v___x_957_ = lean_unbox(v___x_953_);
v___x_958_ = l_Lean_Syntax_getRange_x3f(v_stx_888_, v___x_957_);
if (lean_obj_tag(v___x_958_) == 1)
{
lean_object* v_val_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v_val_959_ = lean_ctor_get(v___x_958_, 0);
lean_inc_n(v_val_959_, 2);
lean_dec_ref_known(v___x_958_, 1);
v___x_960_ = lean_st_ref_take(v___y_952_);
v___x_961_ = lean_box(0);
v___x_962_ = ((lean_object*)(l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__2));
v___x_963_ = ((lean_object*)(l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__3));
v___x_964_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_962_, v___x_963_, v___x_960_, v_val_959_);
switch(lean_obj_tag(v___x_964_))
{
case 0:
{
lean_object* v_index_965_; lean_object* v_size_966_; lean_object* v___x_967_; 
v_index_965_ = lean_ctor_get(v___x_964_, 0);
lean_inc(v_index_965_);
lean_dec_ref_known(v___x_964_, 3);
v_size_966_ = lean_ctor_get(v___x_960_, 0);
lean_inc(v_size_966_);
v___x_967_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_960_, v_size_966_, v_index_965_, v_val_959_, v_stx_888_);
lean_dec(v_index_965_);
v___y_892_ = v___y_952_;
v___y_893_ = v___x_961_;
v___y_894_ = v___x_967_;
goto v___jp_891_;
}
case 1:
{
lean_object* v_index_968_; lean_object* v_size_969_; lean_object* v_keyArray_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; uint8_t v___x_974_; 
v_index_968_ = lean_ctor_get(v___x_964_, 0);
lean_inc(v_index_968_);
lean_dec_ref_known(v___x_964_, 1);
v_size_969_ = lean_ctor_get(v___x_960_, 0);
lean_inc(v_size_969_);
v_keyArray_970_ = lean_ctor_get(v___x_960_, 1);
lean_inc_ref(v_keyArray_970_);
v___x_971_ = lean_unsigned_to_nat(1u);
v___x_972_ = lean_nat_add(v_size_969_, v___x_971_);
lean_dec(v_size_969_);
v___x_973_ = lean_array_get_size(v_keyArray_970_);
lean_dec_ref(v_keyArray_970_);
v___x_974_ = lean_nat_dec_lt(v___x_972_, v___x_973_);
if (v___x_974_ == 0)
{
lean_dec(v___x_972_);
lean_dec(v_index_968_);
v___y_933_ = v___x_960_;
v___y_934_ = v_val_959_;
v___y_935_ = v___x_962_;
v___y_936_ = v___y_952_;
v___y_937_ = v___x_961_;
v___y_938_ = v___x_963_;
goto v___jp_932_;
}
else
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; uint8_t v___x_979_; 
v___x_975_ = lean_unsigned_to_nat(4u);
v___x_976_ = lean_nat_mul(v___x_972_, v___x_975_);
v___x_977_ = lean_unsigned_to_nat(3u);
v___x_978_ = lean_nat_mul(v___x_973_, v___x_977_);
v___x_979_ = lean_nat_dec_le(v___x_976_, v___x_978_);
lean_dec(v___x_978_);
lean_dec(v___x_976_);
if (v___x_979_ == 0)
{
lean_dec(v___x_972_);
lean_dec(v_index_968_);
v___y_933_ = v___x_960_;
v___y_934_ = v_val_959_;
v___y_935_ = v___x_962_;
v___y_936_ = v___y_952_;
v___y_937_ = v___x_961_;
v___y_938_ = v___x_963_;
goto v___jp_932_;
}
else
{
lean_object* v___x_980_; 
v___x_980_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_960_, v___x_972_, v_index_968_, v_val_959_, v_stx_888_);
lean_dec(v_index_968_);
v___y_892_ = v___y_952_;
v___y_893_ = v___x_961_;
v___y_894_ = v___x_980_;
goto v___jp_891_;
}
}
}
default: 
{
lean_object* v_size_981_; lean_object* v_keyArray_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; uint8_t v___x_986_; 
v_size_981_ = lean_ctor_get(v___x_960_, 0);
lean_inc(v_size_981_);
v_keyArray_982_ = lean_ctor_get(v___x_960_, 1);
lean_inc_ref(v_keyArray_982_);
v___x_983_ = lean_unsigned_to_nat(1u);
v___x_984_ = lean_nat_add(v_size_981_, v___x_983_);
lean_dec(v_size_981_);
v___x_985_ = lean_array_get_size(v_keyArray_982_);
lean_dec_ref(v_keyArray_982_);
v___x_986_ = lean_nat_dec_lt(v___x_984_, v___x_985_);
if (v___x_986_ == 0)
{
lean_object* v___x_987_; 
lean_dec(v___x_984_);
v___x_987_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_962_, v___x_963_, v___x_960_);
v___y_908_ = v_val_959_;
v___y_909_ = v___x_962_;
v___y_910_ = v___y_952_;
v___y_911_ = v___x_961_;
v___y_912_ = v___x_963_;
v___y_913_ = v___x_987_;
goto v___jp_907_;
}
else
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; uint8_t v___x_992_; 
v___x_988_ = lean_unsigned_to_nat(4u);
v___x_989_ = lean_nat_mul(v___x_984_, v___x_988_);
lean_dec(v___x_984_);
v___x_990_ = lean_unsigned_to_nat(3u);
v___x_991_ = lean_nat_mul(v___x_985_, v___x_990_);
v___x_992_ = lean_nat_dec_le(v___x_989_, v___x_991_);
lean_dec(v___x_991_);
lean_dec(v___x_989_);
if (v___x_992_ == 0)
{
lean_object* v___x_993_; 
v___x_993_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_962_, v___x_963_, v___x_960_);
v___y_908_ = v_val_959_;
v___y_909_ = v___x_962_;
v___y_910_ = v___y_952_;
v___y_911_ = v___x_961_;
v___y_912_ = v___x_963_;
v___y_913_ = v___x_993_;
goto v___jp_907_;
}
else
{
v___y_908_ = v_val_959_;
v___y_909_ = v___x_962_;
v___y_910_ = v___y_952_;
v___y_911_ = v___x_961_;
v___y_912_ = v___x_963_;
v___y_913_ = v___x_960_;
goto v___jp_907_;
}
}
}
}
}
else
{
lean_object* v___x_994_; lean_object* v___x_995_; 
lean_dec(v___x_958_);
lean_dec_ref_known(v_stx_888_, 3);
v___x_994_ = lean_box(0);
v___x_995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
return v___x_995_;
}
}
}
v___jp_996_:
{
if (lean_obj_tag(v___y_997_) == 0)
{
lean_dec_ref_known(v___y_997_, 1);
v___y_952_ = v_a_889_;
goto v___jp_951_;
}
else
{
lean_dec_ref_known(v_stx_888_, 3);
lean_dec_ref(v_isTacKind_887_);
return v___y_997_;
}
}
}
else
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
lean_dec(v_stx_888_);
lean_dec_ref(v_isTacKind_887_);
lean_dec_ref(v_ignoreTacticKinds_886_);
v___x_1013_ = lean_box(0);
v___x_1014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
return v___x_1014_;
}
v___jp_891_:
{
lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_895_ = lean_st_ref_put(v___y_892_, v___y_894_);
v___x_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_896_, 0, v___y_893_);
return v___x_896_;
}
v___jp_897_:
{
lean_object* v_size_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v_size_903_ = lean_ctor_get(v___y_899_, 0);
v___x_904_ = lean_unsigned_to_nat(1u);
v___x_905_ = lean_nat_add(v_size_903_, v___x_904_);
v___x_906_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_899_, v___x_905_, v_i_902_, v___y_898_, v_stx_888_);
lean_dec(v_i_902_);
v___y_892_ = v___y_900_;
v___y_893_ = v___y_901_;
v___y_894_ = v___x_906_;
goto v___jp_891_;
}
v___jp_907_:
{
lean_object* v___x_914_; 
lean_inc_ref(v___y_908_);
v___x_914_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___y_909_, v___y_912_, v___y_913_, v___y_908_);
switch(lean_obj_tag(v___x_914_))
{
case 0:
{
lean_object* v_index_915_; lean_object* v_size_916_; lean_object* v___x_917_; 
v_index_915_ = lean_ctor_get(v___x_914_, 0);
lean_inc(v_index_915_);
lean_dec_ref_known(v___x_914_, 3);
v_size_916_ = lean_ctor_get(v___y_913_, 0);
lean_inc(v_size_916_);
v___x_917_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_913_, v_size_916_, v_index_915_, v___y_908_, v_stx_888_);
lean_dec(v_index_915_);
v___y_892_ = v___y_910_;
v___y_893_ = v___y_911_;
v___y_894_ = v___x_917_;
goto v___jp_891_;
}
case 1:
{
lean_object* v_index_918_; 
v_index_918_ = lean_ctor_get(v___x_914_, 0);
lean_inc(v_index_918_);
lean_dec_ref_known(v___x_914_, 1);
v___y_898_ = v___y_908_;
v___y_899_ = v___y_913_;
v___y_900_ = v___y_910_;
v___y_901_ = v___y_911_;
v_i_902_ = v_index_918_;
goto v___jp_897_;
}
default: 
{
lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_919_ = lean_unsigned_to_nat(0u);
v___x_920_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_913_, v___x_919_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v_index_921_; 
v_index_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_index_921_);
lean_dec_ref_known(v___x_920_, 1);
v___y_898_ = v___y_908_;
v___y_899_ = v___y_913_;
v___y_900_ = v___y_910_;
v___y_901_ = v___y_911_;
v_i_902_ = v_index_921_;
goto v___jp_897_;
}
else
{
lean_dec_ref(v___y_908_);
lean_dec(v_stx_888_);
v___y_892_ = v___y_910_;
v___y_893_ = v___y_911_;
v___y_894_ = v___y_913_;
goto v___jp_891_;
}
}
}
}
v___jp_922_:
{
lean_object* v_size_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v_size_928_ = lean_ctor_get(v___y_926_, 0);
v___x_929_ = lean_unsigned_to_nat(1u);
v___x_930_ = lean_nat_add(v_size_928_, v___x_929_);
v___x_931_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_926_, v___x_930_, v_i_927_, v___y_923_, v_stx_888_);
lean_dec(v_i_927_);
v___y_892_ = v___y_924_;
v___y_893_ = v___y_925_;
v___y_894_ = v___x_931_;
goto v___jp_891_;
}
v___jp_932_:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
lean_inc_ref(v___y_938_);
lean_inc_ref(v___y_935_);
v___x_939_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___y_935_, v___y_938_, v___y_933_);
lean_inc_ref(v___y_934_);
v___x_940_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___y_935_, v___y_938_, v___x_939_, v___y_934_);
switch(lean_obj_tag(v___x_940_))
{
case 0:
{
lean_object* v_index_941_; lean_object* v_size_942_; lean_object* v___x_943_; 
v_index_941_ = lean_ctor_get(v___x_940_, 0);
lean_inc(v_index_941_);
lean_dec_ref_known(v___x_940_, 3);
v_size_942_ = lean_ctor_get(v___x_939_, 0);
lean_inc(v_size_942_);
v___x_943_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_939_, v_size_942_, v_index_941_, v___y_934_, v_stx_888_);
lean_dec(v_index_941_);
v___y_892_ = v___y_936_;
v___y_893_ = v___y_937_;
v___y_894_ = v___x_943_;
goto v___jp_891_;
}
case 1:
{
lean_object* v_index_944_; 
v_index_944_ = lean_ctor_get(v___x_940_, 0);
lean_inc(v_index_944_);
lean_dec_ref_known(v___x_940_, 1);
v___y_923_ = v___y_934_;
v___y_924_ = v___y_936_;
v___y_925_ = v___y_937_;
v___y_926_ = v___x_939_;
v_i_927_ = v_index_944_;
goto v___jp_922_;
}
default: 
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = lean_unsigned_to_nat(0u);
v___x_946_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_939_, v___x_945_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v_index_947_; 
v_index_947_ = lean_ctor_get(v___x_946_, 0);
lean_inc(v_index_947_);
lean_dec_ref_known(v___x_946_, 1);
v___y_923_ = v___y_934_;
v___y_924_ = v___y_936_;
v___y_925_ = v___y_937_;
v___y_926_ = v___x_939_;
v_i_927_ = v_index_947_;
goto v___jp_922_;
}
else
{
lean_dec_ref(v___y_934_);
lean_dec(v_stx_888_);
v___y_892_ = v___y_936_;
v___y_893_ = v___y_937_;
v___y_894_ = v___x_939_;
goto v___jp_891_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_getTactics___lam__0(lean_object* v_ignoreTacticKinds_1015_, lean_object* v_isTacKind_1016_, lean_object* v_x_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v___x_1021_; 
v___x_1021_ = l_Lean_Linter_Extra_UnreachableTactic_getTactics(v_ignoreTacticKinds_1015_, v_isTacKind_1016_, v___y_1018_, v___y_1019_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_getTactics___boxed(lean_object* v_ignoreTacticKinds_1022_, lean_object* v_isTacKind_1023_, lean_object* v_stx_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l_Lean_Linter_Extra_UnreachableTactic_getTactics(v_ignoreTacticKinds_1022_, v_isTacKind_1023_, v_stx_1024_, v_a_1025_);
lean_dec(v_a_1025_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5_spec__8_spec__9___redArg(lean_object* v_m_1028_, lean_object* v_query_1029_, lean_object* v_x_1030_, lean_object* v_x_1031_, lean_object* v_x_1032_){
_start:
{
lean_object* v_zero_1033_; uint8_t v_isZero_1034_; 
v_zero_1033_ = lean_unsigned_to_nat(0u);
v_isZero_1034_ = lean_nat_dec_eq(v_x_1031_, v_zero_1033_);
if (v_isZero_1034_ == 1)
{
lean_dec(v_x_1032_);
lean_dec(v_x_1031_);
if (lean_obj_tag(v_x_1030_) == 0)
{
lean_object* v___x_1035_; 
v___x_1035_ = lean_box(2);
return v___x_1035_;
}
else
{
lean_object* v_val_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1043_; 
v_val_1036_ = lean_ctor_get(v_x_1030_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v_x_1030_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1038_ = v_x_1030_;
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_val_1036_);
lean_dec(v_x_1030_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_1039_ == 0)
{
v___x_1041_ = v___x_1038_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_val_1036_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
else
{
lean_object* v_keyArray_1044_; lean_object* v_valueArray_1045_; lean_object* v___x_1046_; uint8_t v_isSome_1047_; 
v_keyArray_1044_ = lean_ctor_get(v_m_1028_, 1);
v_valueArray_1045_ = lean_ctor_get(v_m_1028_, 2);
v___x_1046_ = lean_array_fget_borrowed(v_keyArray_1044_, v_x_1032_);
v_isSome_1047_ = lean_noption_is_some(v___x_1046_);
if (v_isSome_1047_ == 0)
{
lean_dec(v_x_1031_);
if (lean_obj_tag(v_x_1030_) == 0)
{
lean_object* v___x_1048_; 
v___x_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1048_, 0, v_x_1032_);
return v___x_1048_;
}
else
{
lean_object* v_val_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1056_; 
lean_dec(v_x_1032_);
v_val_1049_ = lean_ctor_get(v_x_1030_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v_x_1030_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1051_ = v_x_1030_;
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_val_1049_);
lean_dec(v_x_1030_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1054_; 
if (v_isShared_1052_ == 0)
{
v___x_1054_ = v___x_1051_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_val_1049_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
}
else
{
lean_object* v_one_1057_; lean_object* v_n_1058_; lean_object* v___y_1060_; 
v_one_1057_ = lean_unsigned_to_nat(1u);
v_n_1058_ = lean_nat_sub(v_x_1031_, v_one_1057_);
lean_dec(v_x_1031_);
if (v_isSome_1047_ == 0)
{
goto v___jp_1066_;
}
else
{
lean_object* v___x_1068_; uint8_t v_isSome_1069_; 
v___x_1068_ = lean_array_fget_borrowed(v_valueArray_1045_, v_x_1032_);
v_isSome_1069_ = lean_noption_is_some(v___x_1068_);
if (v_isSome_1069_ == 0)
{
goto v___jp_1066_;
}
else
{
lean_object* v_val_1070_; uint8_t v___x_1071_; 
lean_inc(v___x_1046_);
v_val_1070_ = lean_noption_get(v___x_1046_);
v___x_1071_ = l_Lean_Syntax_instBEqRange_beq(v_val_1070_, v_query_1029_);
if (v___x_1071_ == 0)
{
lean_object* v___x_1072_; lean_object* v___x_1073_; uint8_t v___x_1074_; 
lean_dec(v_val_1070_);
v___x_1072_ = lean_array_get_size(v_keyArray_1044_);
v___x_1073_ = lean_nat_add(v_x_1032_, v_one_1057_);
lean_dec(v_x_1032_);
v___x_1074_ = lean_nat_dec_lt(v___x_1073_, v___x_1072_);
if (v___x_1074_ == 0)
{
lean_dec(v___x_1073_);
v_x_1031_ = v_n_1058_;
v_x_1032_ = v_zero_1033_;
goto _start;
}
else
{
v_x_1031_ = v_n_1058_;
v_x_1032_ = v___x_1073_;
goto _start;
}
}
else
{
lean_object* v_val_1077_; lean_object* v___x_1078_; 
lean_dec(v_n_1058_);
lean_dec(v_x_1030_);
lean_inc(v___x_1068_);
v_val_1077_ = lean_noption_get(v___x_1068_);
v___x_1078_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1078_, 0, v_x_1032_);
lean_ctor_set(v___x_1078_, 1, v_val_1070_);
lean_ctor_set(v___x_1078_, 2, v_val_1077_);
return v___x_1078_;
}
}
}
v___jp_1059_:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; uint8_t v___x_1063_; 
v___x_1061_ = lean_array_get_size(v_keyArray_1044_);
v___x_1062_ = lean_nat_add(v_x_1032_, v_one_1057_);
lean_dec(v_x_1032_);
v___x_1063_ = lean_nat_dec_lt(v___x_1062_, v___x_1061_);
if (v___x_1063_ == 0)
{
lean_dec(v___x_1062_);
v_x_1030_ = v___y_1060_;
v_x_1031_ = v_n_1058_;
v_x_1032_ = v_zero_1033_;
goto _start;
}
else
{
v_x_1030_ = v___y_1060_;
v_x_1031_ = v_n_1058_;
v_x_1032_ = v___x_1062_;
goto _start;
}
}
v___jp_1066_:
{
if (lean_obj_tag(v_x_1030_) == 0)
{
lean_object* v___x_1067_; 
lean_inc(v_x_1032_);
v___x_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1067_, 0, v_x_1032_);
v___y_1060_ = v___x_1067_;
goto v___jp_1059_;
}
else
{
v___y_1060_ = v_x_1030_;
goto v___jp_1059_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5_spec__8_spec__9___redArg___boxed(lean_object* v_m_1079_, lean_object* v_query_1080_, lean_object* v_x_1081_, lean_object* v_x_1082_, lean_object* v_x_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5_spec__8_spec__9___redArg(v_m_1079_, v_query_1080_, v_x_1081_, v_x_1082_, v_x_1083_);
lean_dec_ref(v_query_1080_);
lean_dec_ref(v_m_1079_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5_spec__8___redArg(lean_object* v_m_1085_, lean_object* v_query_1086_){
_start:
{
lean_object* v_keyArray_1087_; lean_object* v___x_1088_; uint64_t v___x_1089_; uint64_t v___x_1090_; uint64_t v___x_1091_; uint64_t v_fold_1092_; uint64_t v___x_1093_; uint64_t v___x_1094_; uint64_t v___x_1095_; size_t v___x_1096_; size_t v___x_1097_; size_t v___x_1098_; size_t v___x_1099_; size_t v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v_keyArray_1087_ = lean_ctor_get(v_m_1085_, 1);
v___x_1088_ = lean_array_get_size(v_keyArray_1087_);
v___x_1089_ = l_Lean_Syntax_instHashableRange_hash(v_query_1086_);
v___x_1090_ = 32ULL;
v___x_1091_ = lean_uint64_shift_right(v___x_1089_, v___x_1090_);
v_fold_1092_ = lean_uint64_xor(v___x_1089_, v___x_1091_);
v___x_1093_ = 16ULL;
v___x_1094_ = lean_uint64_shift_right(v_fold_1092_, v___x_1093_);
v___x_1095_ = lean_uint64_xor(v_fold_1092_, v___x_1094_);
v___x_1096_ = lean_uint64_to_usize(v___x_1095_);
v___x_1097_ = lean_usize_of_nat(v___x_1088_);
v___x_1098_ = ((size_t)1ULL);
v___x_1099_ = lean_usize_sub(v___x_1097_, v___x_1098_);
v___x_1100_ = lean_usize_land(v___x_1096_, v___x_1099_);
v___x_1101_ = lean_usize_to_nat(v___x_1100_);
v___x_1102_ = lean_box(0);
v___x_1103_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5_spec__8_spec__9___redArg(v_m_1085_, v_query_1086_, v___x_1102_, v___x_1088_, v___x_1101_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_m_1104_, lean_object* v_query_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5_spec__8___redArg(v_m_1104_, v_query_1105_);
lean_dec_ref(v_query_1105_);
lean_dec_ref(v_m_1104_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5___redArg(lean_object* v_m_1107_, lean_object* v_query_1108_){
_start:
{
lean_object* v___x_1109_; 
v___x_1109_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5_spec__8___redArg(v_m_1107_, v_query_1108_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v_index_1110_; lean_object* v_key_1111_; lean_object* v_value_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1119_; 
v_index_1110_ = lean_ctor_get(v___x_1109_, 0);
v_key_1111_ = lean_ctor_get(v___x_1109_, 1);
v_value_1112_ = lean_ctor_get(v___x_1109_, 2);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1114_ = v___x_1109_;
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_value_1112_);
lean_inc(v_key_1111_);
lean_inc(v_index_1110_);
lean_dec(v___x_1109_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1117_; 
if (v_isShared_1115_ == 0)
{
v___x_1117_ = v___x_1114_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_index_1110_);
lean_ctor_set(v_reuseFailAlloc_1118_, 1, v_key_1111_);
lean_ctor_set(v_reuseFailAlloc_1118_, 2, v_value_1112_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
else
{
lean_object* v___x_1120_; 
lean_dec(v___x_1109_);
v___x_1120_ = lean_box(1);
return v___x_1120_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5___redArg___boxed(lean_object* v_m_1121_, lean_object* v_query_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5___redArg(v_m_1121_, v_query_1122_);
lean_dec_ref(v_query_1122_);
lean_dec_ref(v_m_1121_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2___redArg(lean_object* v_m_1124_, lean_object* v_a_1125_){
_start:
{
lean_object* v___x_1126_; 
v___x_1126_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5___redArg(v_m_1124_, v_a_1125_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v_index_1127_; lean_object* v_size_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v_index_1127_ = lean_ctor_get(v___x_1126_, 0);
lean_inc(v_index_1127_);
lean_dec_ref_known(v___x_1126_, 3);
v_size_1128_ = lean_ctor_get(v_m_1124_, 0);
v___x_1129_ = lean_unsigned_to_nat(1u);
v___x_1130_ = lean_nat_sub(v_size_1128_, v___x_1129_);
v___x_1131_ = l_Std_DHashMap_Raw_clearCell___redArg(v_m_1124_, v___x_1130_, v_index_1127_);
lean_dec(v_index_1127_);
return v___x_1131_;
}
else
{
return v_m_1124_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2___redArg___boxed(lean_object* v_m_1132_, lean_object* v_a_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2___redArg(v_m_1132_, v_a_1133_);
lean_dec_ref(v_a_1133_);
return v_res_1134_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1135_; 
v___x_1135_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics(lean_object* v_x_1136_, lean_object* v_a_1137_){
_start:
{
switch(lean_obj_tag(v_x_1136_))
{
case 0:
{
lean_object* v_t_1139_; 
v_t_1139_ = lean_ctor_get(v_x_1136_, 1);
lean_inc_ref(v_t_1139_);
lean_dec_ref_known(v_x_1136_, 2);
v_x_1136_ = v_t_1139_;
goto _start;
}
case 1:
{
lean_object* v_i_1141_; 
v_i_1141_ = lean_ctor_get(v_x_1136_, 0);
if (lean_obj_tag(v_i_1141_) == 0)
{
lean_object* v_i_1142_; lean_object* v_toElabInfo_1143_; lean_object* v_children_1144_; lean_object* v_stx_1145_; uint8_t v___x_1146_; lean_object* v___x_1147_; 
v_i_1142_ = lean_ctor_get(v_i_1141_, 0);
v_toElabInfo_1143_ = lean_ctor_get(v_i_1142_, 0);
lean_inc_ref(v_toElabInfo_1143_);
v_children_1144_ = lean_ctor_get(v_x_1136_, 1);
lean_inc_ref(v_children_1144_);
lean_dec_ref_known(v_x_1136_, 2);
v_stx_1145_ = lean_ctor_get(v_toElabInfo_1143_, 1);
lean_inc(v_stx_1145_);
lean_dec_ref(v_toElabInfo_1143_);
v___x_1146_ = 1;
v___x_1147_ = l_Lean_Syntax_getRange_x3f(v_stx_1145_, v___x_1146_);
lean_dec(v_stx_1145_);
if (lean_obj_tag(v___x_1147_) == 1)
{
lean_object* v_val_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v_val_1148_ = lean_ctor_get(v___x_1147_, 0);
lean_inc(v_val_1148_);
lean_dec_ref_known(v___x_1147_, 1);
v___x_1149_ = lean_st_ref_take(v_a_1137_);
v___x_1150_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2___redArg(v___x_1149_, v_val_1148_);
lean_dec(v_val_1148_);
v___x_1151_ = lean_st_ref_put(v_a_1137_, v___x_1150_);
v___x_1152_ = l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList(v_children_1144_, v_a_1137_);
return v___x_1152_;
}
else
{
lean_object* v___x_1153_; 
lean_dec(v___x_1147_);
v___x_1153_ = l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList(v_children_1144_, v_a_1137_);
return v___x_1153_;
}
}
else
{
lean_object* v_children_1154_; lean_object* v___x_1155_; 
v_children_1154_ = lean_ctor_get(v_x_1136_, 1);
lean_inc_ref(v_children_1154_);
lean_dec_ref_known(v_x_1136_, 2);
v___x_1155_ = l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList(v_children_1154_, v_a_1137_);
return v___x_1155_;
}
}
default: 
{
lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1163_; 
v_isSharedCheck_1163_ = !lean_is_exclusive(v_x_1136_);
if (v_isSharedCheck_1163_ == 0)
{
lean_object* v_unused_1164_; 
v_unused_1164_ = lean_ctor_get(v_x_1136_, 0);
lean_dec(v_unused_1164_);
v___x_1157_ = v_x_1136_;
v_isShared_1158_ = v_isSharedCheck_1163_;
goto v_resetjp_1156_;
}
else
{
lean_dec(v_x_1136_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1163_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1159_; lean_object* v___x_1161_; 
v___x_1159_ = lean_box(0);
if (v_isShared_1158_ == 0)
{
lean_ctor_set_tag(v___x_1157_, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1159_);
v___x_1161_ = v___x_1157_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v___x_1159_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(lean_object* v_as_1165_, size_t v_i_1166_, size_t v_stop_1167_, lean_object* v_b_1168_, lean_object* v___y_1169_){
_start:
{
uint8_t v___x_1171_; 
v___x_1171_ = lean_usize_dec_eq(v_i_1166_, v_stop_1167_);
if (v___x_1171_ == 0)
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1172_ = lean_array_uget_borrowed(v_as_1165_, v_i_1166_);
lean_inc(v___x_1172_);
v___x_1173_ = l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics(v___x_1172_, v___y_1169_);
if (lean_obj_tag(v___x_1173_) == 0)
{
lean_object* v_a_1174_; size_t v___x_1175_; size_t v___x_1176_; 
v_a_1174_ = lean_ctor_get(v___x_1173_, 0);
lean_inc(v_a_1174_);
lean_dec_ref_known(v___x_1173_, 1);
v___x_1175_ = ((size_t)1ULL);
v___x_1176_ = lean_usize_add(v_i_1166_, v___x_1175_);
v_i_1166_ = v___x_1176_;
v_b_1168_ = v_a_1174_;
goto _start;
}
else
{
return v___x_1173_;
}
}
else
{
lean_object* v___x_1178_; 
v___x_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1178_, 0, v_b_1168_);
return v___x_1178_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__2(lean_object* v_x_1179_, lean_object* v___y_1180_){
_start:
{
if (lean_obj_tag(v_x_1179_) == 0)
{
lean_object* v_cs_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1203_; 
v_cs_1182_ = lean_ctor_get(v_x_1179_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v_x_1179_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1184_ = v_x_1179_;
v_isShared_1185_ = v_isSharedCheck_1203_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_cs_1182_);
lean_dec(v_x_1179_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1203_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; uint8_t v___x_1189_; 
v___x_1186_ = lean_unsigned_to_nat(0u);
v___x_1187_ = lean_array_get_size(v_cs_1182_);
v___x_1188_ = lean_box(0);
v___x_1189_ = lean_nat_dec_lt(v___x_1186_, v___x_1187_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1191_; 
lean_dec_ref(v_cs_1182_);
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 0, v___x_1188_);
v___x_1191_ = v___x_1184_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1188_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
else
{
uint8_t v___x_1193_; 
v___x_1193_ = lean_nat_dec_le(v___x_1187_, v___x_1187_);
if (v___x_1193_ == 0)
{
if (v___x_1189_ == 0)
{
lean_object* v___x_1195_; 
lean_dec_ref(v_cs_1182_);
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 0, v___x_1188_);
v___x_1195_ = v___x_1184_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v___x_1188_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
else
{
size_t v___x_1197_; size_t v___x_1198_; lean_object* v___x_1199_; 
lean_del_object(v___x_1184_);
v___x_1197_ = ((size_t)0ULL);
v___x_1198_ = lean_usize_of_nat(v___x_1187_);
v___x_1199_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__3(v_cs_1182_, v___x_1197_, v___x_1198_, v___x_1188_, v___y_1180_);
lean_dec_ref(v_cs_1182_);
return v___x_1199_;
}
}
else
{
size_t v___x_1200_; size_t v___x_1201_; lean_object* v___x_1202_; 
lean_del_object(v___x_1184_);
v___x_1200_ = ((size_t)0ULL);
v___x_1201_ = lean_usize_of_nat(v___x_1187_);
v___x_1202_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__3(v_cs_1182_, v___x_1200_, v___x_1201_, v___x_1188_, v___y_1180_);
lean_dec_ref(v_cs_1182_);
return v___x_1202_;
}
}
}
}
else
{
lean_object* v_vs_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1225_; 
v_vs_1204_ = lean_ctor_get(v_x_1179_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v_x_1179_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1206_ = v_x_1179_;
v_isShared_1207_ = v_isSharedCheck_1225_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_vs_1204_);
lean_dec(v_x_1179_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1225_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; uint8_t v___x_1211_; 
v___x_1208_ = lean_unsigned_to_nat(0u);
v___x_1209_ = lean_array_get_size(v_vs_1204_);
v___x_1210_ = lean_box(0);
v___x_1211_ = lean_nat_dec_lt(v___x_1208_, v___x_1209_);
if (v___x_1211_ == 0)
{
lean_object* v___x_1213_; 
lean_dec_ref(v_vs_1204_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set_tag(v___x_1206_, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1210_);
v___x_1213_ = v___x_1206_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v___x_1210_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
else
{
uint8_t v___x_1215_; 
v___x_1215_ = lean_nat_dec_le(v___x_1209_, v___x_1209_);
if (v___x_1215_ == 0)
{
if (v___x_1211_ == 0)
{
lean_object* v___x_1217_; 
lean_dec_ref(v_vs_1204_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set_tag(v___x_1206_, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1210_);
v___x_1217_ = v___x_1206_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v___x_1210_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
else
{
size_t v___x_1219_; size_t v___x_1220_; lean_object* v___x_1221_; 
lean_del_object(v___x_1206_);
v___x_1219_ = ((size_t)0ULL);
v___x_1220_ = lean_usize_of_nat(v___x_1209_);
v___x_1221_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(v_vs_1204_, v___x_1219_, v___x_1220_, v___x_1210_, v___y_1180_);
lean_dec_ref(v_vs_1204_);
return v___x_1221_;
}
}
else
{
size_t v___x_1222_; size_t v___x_1223_; lean_object* v___x_1224_; 
lean_del_object(v___x_1206_);
v___x_1222_ = ((size_t)0ULL);
v___x_1223_ = lean_usize_of_nat(v___x_1209_);
v___x_1224_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(v_vs_1204_, v___x_1222_, v___x_1223_, v___x_1210_, v___y_1180_);
lean_dec_ref(v_vs_1204_);
return v___x_1224_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__3(lean_object* v_as_1226_, size_t v_i_1227_, size_t v_stop_1228_, lean_object* v_b_1229_, lean_object* v___y_1230_){
_start:
{
uint8_t v___x_1232_; 
v___x_1232_ = lean_usize_dec_eq(v_i_1227_, v_stop_1228_);
if (v___x_1232_ == 0)
{
lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1233_ = lean_array_uget_borrowed(v_as_1226_, v_i_1227_);
lean_inc(v___x_1233_);
v___x_1234_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__2(v___x_1233_, v___y_1230_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v_a_1235_; size_t v___x_1236_; size_t v___x_1237_; 
v_a_1235_ = lean_ctor_get(v___x_1234_, 0);
lean_inc(v_a_1235_);
lean_dec_ref_known(v___x_1234_, 1);
v___x_1236_ = ((size_t)1ULL);
v___x_1237_ = lean_usize_add(v_i_1227_, v___x_1236_);
v_i_1227_ = v___x_1237_;
v_b_1229_ = v_a_1235_;
goto _start;
}
else
{
return v___x_1234_;
}
}
else
{
lean_object* v___x_1239_; 
v___x_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1239_, 0, v_b_1229_);
return v___x_1239_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0(lean_object* v_x_1240_, size_t v_x_1241_, size_t v_x_1242_, lean_object* v___y_1243_){
_start:
{
if (lean_obj_tag(v_x_1240_) == 0)
{
lean_object* v_cs_1245_; lean_object* v___x_1246_; size_t v___x_1247_; lean_object* v_j_1248_; lean_object* v___x_1249_; size_t v___x_1250_; size_t v___x_1251_; size_t v___x_1252_; size_t v___x_1253_; size_t v___x_1254_; size_t v___x_1255_; lean_object* v___x_1256_; 
v_cs_1245_ = lean_ctor_get(v_x_1240_, 0);
lean_inc_ref(v_cs_1245_);
lean_dec_ref_known(v_x_1240_, 1);
v___x_1246_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0___closed__0);
v___x_1247_ = lean_usize_shift_right(v_x_1241_, v_x_1242_);
v_j_1248_ = lean_usize_to_nat(v___x_1247_);
v___x_1249_ = lean_array_get_borrowed(v___x_1246_, v_cs_1245_, v_j_1248_);
v___x_1250_ = ((size_t)1ULL);
v___x_1251_ = lean_usize_shift_left(v___x_1250_, v_x_1242_);
v___x_1252_ = lean_usize_sub(v___x_1251_, v___x_1250_);
v___x_1253_ = lean_usize_land(v_x_1241_, v___x_1252_);
v___x_1254_ = ((size_t)5ULL);
v___x_1255_ = lean_usize_sub(v_x_1242_, v___x_1254_);
lean_inc(v___x_1249_);
v___x_1256_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0(v___x_1249_, v___x_1253_, v___x_1255_, v___y_1243_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1278_; 
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1278_ == 0)
{
lean_object* v_unused_1279_; 
v_unused_1279_ = lean_ctor_get(v___x_1256_, 0);
lean_dec(v_unused_1279_);
v___x_1258_ = v___x_1256_;
v_isShared_1259_ = v_isSharedCheck_1278_;
goto v_resetjp_1257_;
}
else
{
lean_dec(v___x_1256_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1278_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; uint8_t v___x_1264_; 
v___x_1260_ = lean_unsigned_to_nat(1u);
v___x_1261_ = lean_nat_add(v_j_1248_, v___x_1260_);
lean_dec(v_j_1248_);
v___x_1262_ = lean_array_get_size(v_cs_1245_);
v___x_1263_ = lean_box(0);
v___x_1264_ = lean_nat_dec_lt(v___x_1261_, v___x_1262_);
if (v___x_1264_ == 0)
{
lean_object* v___x_1266_; 
lean_dec(v___x_1261_);
lean_dec_ref(v_cs_1245_);
if (v_isShared_1259_ == 0)
{
lean_ctor_set(v___x_1258_, 0, v___x_1263_);
v___x_1266_ = v___x_1258_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1263_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
else
{
uint8_t v___x_1268_; 
v___x_1268_ = lean_nat_dec_le(v___x_1262_, v___x_1262_);
if (v___x_1268_ == 0)
{
if (v___x_1264_ == 0)
{
lean_object* v___x_1270_; 
lean_dec(v___x_1261_);
lean_dec_ref(v_cs_1245_);
if (v_isShared_1259_ == 0)
{
lean_ctor_set(v___x_1258_, 0, v___x_1263_);
v___x_1270_ = v___x_1258_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v___x_1263_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
else
{
size_t v___x_1272_; size_t v___x_1273_; lean_object* v___x_1274_; 
lean_del_object(v___x_1258_);
v___x_1272_ = lean_usize_of_nat(v___x_1261_);
lean_dec(v___x_1261_);
v___x_1273_ = lean_usize_of_nat(v___x_1262_);
v___x_1274_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__3(v_cs_1245_, v___x_1272_, v___x_1273_, v___x_1263_, v___y_1243_);
lean_dec_ref(v_cs_1245_);
return v___x_1274_;
}
}
else
{
size_t v___x_1275_; size_t v___x_1276_; lean_object* v___x_1277_; 
lean_del_object(v___x_1258_);
v___x_1275_ = lean_usize_of_nat(v___x_1261_);
lean_dec(v___x_1261_);
v___x_1276_ = lean_usize_of_nat(v___x_1262_);
v___x_1277_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__3(v_cs_1245_, v___x_1275_, v___x_1276_, v___x_1263_, v___y_1243_);
lean_dec_ref(v_cs_1245_);
return v___x_1277_;
}
}
}
}
else
{
lean_dec(v_j_1248_);
lean_dec_ref(v_cs_1245_);
return v___x_1256_;
}
}
else
{
lean_object* v_vs_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1301_; 
v_vs_1280_ = lean_ctor_get(v_x_1240_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v_x_1240_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1282_ = v_x_1240_;
v_isShared_1283_ = v_isSharedCheck_1301_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_vs_1280_);
lean_dec(v_x_1240_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1301_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; uint8_t v___x_1287_; 
v___x_1284_ = lean_usize_to_nat(v_x_1241_);
v___x_1285_ = lean_array_get_size(v_vs_1280_);
v___x_1286_ = lean_box(0);
v___x_1287_ = lean_nat_dec_lt(v___x_1284_, v___x_1285_);
if (v___x_1287_ == 0)
{
lean_object* v___x_1289_; 
lean_dec(v___x_1284_);
lean_dec_ref(v_vs_1280_);
if (v_isShared_1283_ == 0)
{
lean_ctor_set_tag(v___x_1282_, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1286_);
v___x_1289_ = v___x_1282_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1286_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
else
{
uint8_t v___x_1291_; 
v___x_1291_ = lean_nat_dec_le(v___x_1285_, v___x_1285_);
if (v___x_1291_ == 0)
{
if (v___x_1287_ == 0)
{
lean_object* v___x_1293_; 
lean_dec(v___x_1284_);
lean_dec_ref(v_vs_1280_);
if (v_isShared_1283_ == 0)
{
lean_ctor_set_tag(v___x_1282_, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1286_);
v___x_1293_ = v___x_1282_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1286_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
else
{
size_t v___x_1295_; size_t v___x_1296_; lean_object* v___x_1297_; 
lean_del_object(v___x_1282_);
v___x_1295_ = lean_usize_of_nat(v___x_1284_);
lean_dec(v___x_1284_);
v___x_1296_ = lean_usize_of_nat(v___x_1285_);
v___x_1297_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(v_vs_1280_, v___x_1295_, v___x_1296_, v___x_1286_, v___y_1243_);
lean_dec_ref(v_vs_1280_);
return v___x_1297_;
}
}
else
{
size_t v___x_1298_; size_t v___x_1299_; lean_object* v___x_1300_; 
lean_del_object(v___x_1282_);
v___x_1298_ = lean_usize_of_nat(v___x_1284_);
lean_dec(v___x_1284_);
v___x_1299_ = lean_usize_of_nat(v___x_1285_);
v___x_1300_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(v_vs_1280_, v___x_1298_, v___x_1299_, v___x_1286_, v___y_1243_);
lean_dec_ref(v_vs_1280_);
return v___x_1300_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__2(lean_object* v_t_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v_root_1305_; lean_object* v_tail_1306_; lean_object* v___x_1307_; 
v_root_1305_ = lean_ctor_get(v_t_1302_, 0);
lean_inc_ref(v_root_1305_);
v_tail_1306_ = lean_ctor_get(v_t_1302_, 1);
lean_inc_ref(v_tail_1306_);
lean_dec_ref(v_t_1302_);
v___x_1307_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__2(v_root_1305_, v___y_1303_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1328_; 
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1328_ == 0)
{
lean_object* v_unused_1329_; 
v_unused_1329_ = lean_ctor_get(v___x_1307_, 0);
lean_dec(v_unused_1329_);
v___x_1309_ = v___x_1307_;
v_isShared_1310_ = v_isSharedCheck_1328_;
goto v_resetjp_1308_;
}
else
{
lean_dec(v___x_1307_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1328_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; uint8_t v___x_1314_; 
v___x_1311_ = lean_unsigned_to_nat(0u);
v___x_1312_ = lean_array_get_size(v_tail_1306_);
v___x_1313_ = lean_box(0);
v___x_1314_ = lean_nat_dec_lt(v___x_1311_, v___x_1312_);
if (v___x_1314_ == 0)
{
lean_object* v___x_1316_; 
lean_dec_ref(v_tail_1306_);
if (v_isShared_1310_ == 0)
{
lean_ctor_set(v___x_1309_, 0, v___x_1313_);
v___x_1316_ = v___x_1309_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v___x_1313_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
else
{
uint8_t v___x_1318_; 
v___x_1318_ = lean_nat_dec_le(v___x_1312_, v___x_1312_);
if (v___x_1318_ == 0)
{
if (v___x_1314_ == 0)
{
lean_object* v___x_1320_; 
lean_dec_ref(v_tail_1306_);
if (v_isShared_1310_ == 0)
{
lean_ctor_set(v___x_1309_, 0, v___x_1313_);
v___x_1320_ = v___x_1309_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v___x_1313_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
else
{
size_t v___x_1322_; size_t v___x_1323_; lean_object* v___x_1324_; 
lean_del_object(v___x_1309_);
v___x_1322_ = ((size_t)0ULL);
v___x_1323_ = lean_usize_of_nat(v___x_1312_);
v___x_1324_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(v_tail_1306_, v___x_1322_, v___x_1323_, v___x_1313_, v___y_1303_);
lean_dec_ref(v_tail_1306_);
return v___x_1324_;
}
}
else
{
size_t v___x_1325_; size_t v___x_1326_; lean_object* v___x_1327_; 
lean_del_object(v___x_1309_);
v___x_1325_ = ((size_t)0ULL);
v___x_1326_ = lean_usize_of_nat(v___x_1312_);
v___x_1327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(v_tail_1306_, v___x_1325_, v___x_1326_, v___x_1313_, v___y_1303_);
lean_dec_ref(v_tail_1306_);
return v___x_1327_;
}
}
}
}
else
{
lean_dec_ref(v_tail_1306_);
return v___x_1307_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0(lean_object* v_t_1330_, lean_object* v_start_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v___x_1334_; uint8_t v___x_1335_; 
v___x_1334_ = lean_unsigned_to_nat(0u);
v___x_1335_ = lean_nat_dec_eq(v_start_1331_, v___x_1334_);
if (v___x_1335_ == 0)
{
lean_object* v_root_1336_; lean_object* v_tail_1337_; size_t v_shift_1338_; lean_object* v_tailOff_1339_; uint8_t v___x_1340_; 
v_root_1336_ = lean_ctor_get(v_t_1330_, 0);
lean_inc_ref(v_root_1336_);
v_tail_1337_ = lean_ctor_get(v_t_1330_, 1);
lean_inc_ref(v_tail_1337_);
v_shift_1338_ = lean_ctor_get_usize(v_t_1330_, 4);
v_tailOff_1339_ = lean_ctor_get(v_t_1330_, 3);
lean_inc(v_tailOff_1339_);
lean_dec_ref(v_t_1330_);
v___x_1340_ = lean_nat_dec_le(v_tailOff_1339_, v_start_1331_);
if (v___x_1340_ == 0)
{
size_t v___x_1341_; lean_object* v___x_1342_; 
lean_dec(v_tailOff_1339_);
v___x_1341_ = lean_usize_of_nat(v_start_1331_);
v___x_1342_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0(v_root_1336_, v___x_1341_, v_shift_1338_, v___y_1332_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1362_; 
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1362_ == 0)
{
lean_object* v_unused_1363_; 
v_unused_1363_ = lean_ctor_get(v___x_1342_, 0);
lean_dec(v_unused_1363_);
v___x_1344_ = v___x_1342_;
v_isShared_1345_ = v_isSharedCheck_1362_;
goto v_resetjp_1343_;
}
else
{
lean_dec(v___x_1342_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1362_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; uint8_t v___x_1348_; 
v___x_1346_ = lean_array_get_size(v_tail_1337_);
v___x_1347_ = lean_box(0);
v___x_1348_ = lean_nat_dec_lt(v___x_1334_, v___x_1346_);
if (v___x_1348_ == 0)
{
lean_object* v___x_1350_; 
lean_dec_ref(v_tail_1337_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 0, v___x_1347_);
v___x_1350_ = v___x_1344_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v___x_1347_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
else
{
uint8_t v___x_1352_; 
v___x_1352_ = lean_nat_dec_le(v___x_1346_, v___x_1346_);
if (v___x_1352_ == 0)
{
if (v___x_1348_ == 0)
{
lean_object* v___x_1354_; 
lean_dec_ref(v_tail_1337_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 0, v___x_1347_);
v___x_1354_ = v___x_1344_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1347_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
else
{
size_t v___x_1356_; size_t v___x_1357_; lean_object* v___x_1358_; 
lean_del_object(v___x_1344_);
v___x_1356_ = ((size_t)0ULL);
v___x_1357_ = lean_usize_of_nat(v___x_1346_);
v___x_1358_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(v_tail_1337_, v___x_1356_, v___x_1357_, v___x_1347_, v___y_1332_);
lean_dec_ref(v_tail_1337_);
return v___x_1358_;
}
}
else
{
size_t v___x_1359_; size_t v___x_1360_; lean_object* v___x_1361_; 
lean_del_object(v___x_1344_);
v___x_1359_ = ((size_t)0ULL);
v___x_1360_ = lean_usize_of_nat(v___x_1346_);
v___x_1361_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(v_tail_1337_, v___x_1359_, v___x_1360_, v___x_1347_, v___y_1332_);
lean_dec_ref(v_tail_1337_);
return v___x_1361_;
}
}
}
}
else
{
lean_dec_ref(v_tail_1337_);
return v___x_1342_;
}
}
else
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; uint8_t v___x_1367_; 
lean_dec_ref(v_root_1336_);
v___x_1364_ = lean_nat_sub(v_start_1331_, v_tailOff_1339_);
lean_dec(v_tailOff_1339_);
v___x_1365_ = lean_array_get_size(v_tail_1337_);
v___x_1366_ = lean_box(0);
v___x_1367_ = lean_nat_dec_lt(v___x_1364_, v___x_1365_);
if (v___x_1367_ == 0)
{
lean_object* v___x_1368_; 
lean_dec(v___x_1364_);
lean_dec_ref(v_tail_1337_);
v___x_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1366_);
return v___x_1368_;
}
else
{
uint8_t v___x_1369_; 
v___x_1369_ = lean_nat_dec_le(v___x_1365_, v___x_1365_);
if (v___x_1369_ == 0)
{
if (v___x_1367_ == 0)
{
lean_object* v___x_1370_; 
lean_dec(v___x_1364_);
lean_dec_ref(v_tail_1337_);
v___x_1370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1366_);
return v___x_1370_;
}
else
{
size_t v___x_1371_; size_t v___x_1372_; lean_object* v___x_1373_; 
v___x_1371_ = lean_usize_of_nat(v___x_1364_);
lean_dec(v___x_1364_);
v___x_1372_ = lean_usize_of_nat(v___x_1365_);
v___x_1373_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(v_tail_1337_, v___x_1371_, v___x_1372_, v___x_1366_, v___y_1332_);
lean_dec_ref(v_tail_1337_);
return v___x_1373_;
}
}
else
{
size_t v___x_1374_; size_t v___x_1375_; lean_object* v___x_1376_; 
v___x_1374_ = lean_usize_of_nat(v___x_1364_);
lean_dec(v___x_1364_);
v___x_1375_ = lean_usize_of_nat(v___x_1365_);
v___x_1376_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(v_tail_1337_, v___x_1374_, v___x_1375_, v___x_1366_, v___y_1332_);
lean_dec_ref(v_tail_1337_);
return v___x_1376_;
}
}
}
}
else
{
lean_object* v___x_1377_; 
v___x_1377_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__2(v_t_1330_, v___y_1332_);
return v___x_1377_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList(lean_object* v_trees_1378_, lean_object* v_a_1379_){
_start:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1381_ = lean_unsigned_to_nat(0u);
v___x_1382_ = l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0(v_trees_1378_, v___x_1381_, v_a_1379_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList___boxed(lean_object* v_trees_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_){
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList(v_trees_1383_, v_a_1384_);
lean_dec(v_a_1384_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1___boxed(lean_object* v_as_1387_, lean_object* v_i_1388_, lean_object* v_stop_1389_, lean_object* v_b_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
size_t v_i_boxed_1393_; size_t v_stop_boxed_1394_; lean_object* v_res_1395_; 
v_i_boxed_1393_ = lean_unbox_usize(v_i_1388_);
lean_dec(v_i_1388_);
v_stop_boxed_1394_ = lean_unbox_usize(v_stop_1389_);
lean_dec(v_stop_1389_);
v_res_1395_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(v_as_1387_, v_i_boxed_1393_, v_stop_boxed_1394_, v_b_1390_, v___y_1391_);
lean_dec(v___y_1391_);
lean_dec_ref(v_as_1387_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__3___boxed(lean_object* v_as_1396_, lean_object* v_i_1397_, lean_object* v_stop_1398_, lean_object* v_b_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
size_t v_i_boxed_1402_; size_t v_stop_boxed_1403_; lean_object* v_res_1404_; 
v_i_boxed_1402_ = lean_unbox_usize(v_i_1397_);
lean_dec(v_i_1397_);
v_stop_boxed_1403_ = lean_unbox_usize(v_stop_1398_);
lean_dec(v_stop_1398_);
v_res_1404_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__3(v_as_1396_, v_i_boxed_1402_, v_stop_boxed_1403_, v_b_1399_, v___y_1400_);
lean_dec(v___y_1400_);
lean_dec_ref(v_as_1396_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__2___boxed(lean_object* v_t_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__2(v_t_1405_, v___y_1406_);
lean_dec(v___y_1406_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics___boxed(lean_object* v_x_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics(v_x_1409_, v_a_1410_);
lean_dec(v_a_1410_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__2___boxed(lean_object* v_x_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__2(v_x_1413_, v___y_1414_);
lean_dec(v___y_1414_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0___boxed(lean_object* v_t_1417_, lean_object* v_start_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0(v_t_1417_, v_start_1418_, v___y_1419_);
lean_dec(v___y_1419_);
lean_dec(v_start_1418_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0___boxed(lean_object* v_x_1422_, lean_object* v_x_1423_, lean_object* v_x_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
size_t v_x_3132__boxed_1427_; size_t v_x_3133__boxed_1428_; lean_object* v_res_1429_; 
v_x_3132__boxed_1427_ = lean_unbox_usize(v_x_1423_);
lean_dec(v_x_1423_);
v_x_3133__boxed_1428_ = lean_unbox_usize(v_x_1424_);
lean_dec(v_x_1424_);
v_res_1429_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0(v_x_1422_, v_x_3132__boxed_1427_, v_x_3133__boxed_1428_, v___y_1425_);
lean_dec(v___y_1425_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2(lean_object* v_00_u03b2_1430_, lean_object* v_m_1431_, lean_object* v_a_1432_){
_start:
{
lean_object* v___x_1433_; 
v___x_1433_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2___redArg(v_m_1431_, v_a_1432_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2___boxed(lean_object* v_00_u03b2_1434_, lean_object* v_m_1435_, lean_object* v_a_1436_){
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2(v_00_u03b2_1434_, v_m_1435_, v_a_1436_);
lean_dec_ref(v_a_1436_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5(lean_object* v_00_u03b2_1438_, lean_object* v_m_1439_, lean_object* v_query_1440_){
_start:
{
lean_object* v___x_1441_; 
v___x_1441_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5___redArg(v_m_1439_, v_query_1440_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1442_, lean_object* v_m_1443_, lean_object* v_query_1444_){
_start:
{
lean_object* v_res_1445_; 
v_res_1445_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5(v_00_u03b2_1442_, v_m_1443_, v_query_1444_);
lean_dec_ref(v_query_1444_);
lean_dec_ref(v_m_1443_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_1446_, lean_object* v_m_1447_, lean_object* v_query_1448_){
_start:
{
lean_object* v___x_1449_; 
v___x_1449_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5_spec__8___redArg(v_m_1447_, v_query_1448_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1450_, lean_object* v_m_1451_, lean_object* v_query_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5_spec__8(v_00_u03b2_1450_, v_m_1451_, v_query_1452_);
lean_dec_ref(v_query_1452_);
lean_dec_ref(v_m_1451_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5_spec__8_spec__9(lean_object* v_00_u03b2_1454_, lean_object* v_m_1455_, lean_object* v_query_1456_, lean_object* v_x_1457_, lean_object* v_x_1458_, lean_object* v_x_1459_, lean_object* v_x_1460_){
_start:
{
lean_object* v___x_1461_; 
v___x_1461_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5_spec__8_spec__9___redArg(v_m_1455_, v_query_1456_, v_x_1457_, v_x_1458_, v_x_1459_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5_spec__8_spec__9___boxed(lean_object* v_00_u03b2_1462_, lean_object* v_m_1463_, lean_object* v_query_1464_, lean_object* v_x_1465_, lean_object* v_x_1466_, lean_object* v_x_1467_, lean_object* v_x_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5_spec__8_spec__9(v_00_u03b2_1462_, v_m_1463_, v_query_1464_, v_x_1465_, v_x_1466_, v_x_1467_, v_x_1468_);
lean_dec_ref(v_query_1464_);
lean_dec_ref(v_m_1463_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__0(lean_object* v_a_1470_){
_start:
{
lean_object* v___x_1471_; 
v___x_1471_ = lean_nat_to_int(v_a_1470_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4___redArg(lean_object* v___y_1472_){
_start:
{
lean_object* v___x_1474_; lean_object* v_infoState_1475_; lean_object* v_trees_1476_; lean_object* v___x_1477_; 
v___x_1474_ = lean_st_ref_get(v___y_1472_);
v_infoState_1475_ = lean_ctor_get(v___x_1474_, 8);
lean_inc_ref(v_infoState_1475_);
lean_dec(v___x_1474_);
v_trees_1476_ = lean_ctor_get(v_infoState_1475_, 2);
lean_inc_ref(v_trees_1476_);
lean_dec_ref(v_infoState_1475_);
v___x_1477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1477_, 0, v_trees_1476_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4___redArg___boxed(lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4___redArg(v___y_1478_);
lean_dec(v___y_1478_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4(lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
lean_object* v___x_1484_; 
v___x_1484_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4___redArg(v___y_1482_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4___boxed(lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_){
_start:
{
lean_object* v_res_1488_; 
v_res_1488_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4(v___y_1485_, v___y_1486_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
return v_res_1488_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8_spec__13_spec__16___redArg(lean_object* v_keys_1489_, lean_object* v_i_1490_, lean_object* v_k_1491_){
_start:
{
lean_object* v___x_1492_; uint8_t v___x_1493_; 
v___x_1492_ = lean_array_get_size(v_keys_1489_);
v___x_1493_ = lean_nat_dec_lt(v_i_1490_, v___x_1492_);
if (v___x_1493_ == 0)
{
lean_dec(v_i_1490_);
return v___x_1493_;
}
else
{
lean_object* v_k_x27_1494_; uint8_t v___x_1495_; 
v_k_x27_1494_ = lean_array_fget_borrowed(v_keys_1489_, v_i_1490_);
v___x_1495_ = lean_name_eq(v_k_1491_, v_k_x27_1494_);
if (v___x_1495_ == 0)
{
lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1496_ = lean_unsigned_to_nat(1u);
v___x_1497_ = lean_nat_add(v_i_1490_, v___x_1496_);
lean_dec(v_i_1490_);
v_i_1490_ = v___x_1497_;
goto _start;
}
else
{
lean_dec(v_i_1490_);
return v___x_1495_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8_spec__13_spec__16___redArg___boxed(lean_object* v_keys_1499_, lean_object* v_i_1500_, lean_object* v_k_1501_){
_start:
{
uint8_t v_res_1502_; lean_object* v_r_1503_; 
v_res_1502_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8_spec__13_spec__16___redArg(v_keys_1499_, v_i_1500_, v_k_1501_);
lean_dec(v_k_1501_);
lean_dec_ref(v_keys_1499_);
v_r_1503_ = lean_box(v_res_1502_);
return v_r_1503_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8_spec__13___redArg(lean_object* v_x_1504_, size_t v_x_1505_, lean_object* v_x_1506_){
_start:
{
if (lean_obj_tag(v_x_1504_) == 0)
{
lean_object* v_es_1507_; lean_object* v___x_1508_; size_t v___x_1509_; size_t v___x_1510_; lean_object* v_j_1511_; lean_object* v___x_1512_; 
v_es_1507_ = lean_ctor_get(v_x_1504_, 0);
v___x_1508_ = lean_box(2);
v___x_1509_ = ((size_t)31ULL);
v___x_1510_ = lean_usize_land(v_x_1505_, v___x_1509_);
v_j_1511_ = lean_usize_to_nat(v___x_1510_);
v___x_1512_ = lean_array_get_borrowed(v___x_1508_, v_es_1507_, v_j_1511_);
lean_dec(v_j_1511_);
switch(lean_obj_tag(v___x_1512_))
{
case 0:
{
lean_object* v_key_1513_; uint8_t v___x_1514_; 
v_key_1513_ = lean_ctor_get(v___x_1512_, 0);
v___x_1514_ = lean_name_eq(v_x_1506_, v_key_1513_);
return v___x_1514_;
}
case 1:
{
lean_object* v_node_1515_; size_t v___x_1516_; size_t v___x_1517_; 
v_node_1515_ = lean_ctor_get(v___x_1512_, 0);
v___x_1516_ = ((size_t)5ULL);
v___x_1517_ = lean_usize_shift_right(v_x_1505_, v___x_1516_);
v_x_1504_ = v_node_1515_;
v_x_1505_ = v___x_1517_;
goto _start;
}
default: 
{
uint8_t v___x_1519_; 
v___x_1519_ = 0;
return v___x_1519_;
}
}
}
else
{
lean_object* v_ks_1520_; lean_object* v___x_1521_; uint8_t v___x_1522_; 
v_ks_1520_ = lean_ctor_get(v_x_1504_, 0);
v___x_1521_ = lean_unsigned_to_nat(0u);
v___x_1522_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8_spec__13_spec__16___redArg(v_ks_1520_, v___x_1521_, v_x_1506_);
return v___x_1522_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8_spec__13___redArg___boxed(lean_object* v_x_1523_, lean_object* v_x_1524_, lean_object* v_x_1525_){
_start:
{
size_t v_x_12228__boxed_1526_; uint8_t v_res_1527_; lean_object* v_r_1528_; 
v_x_12228__boxed_1526_ = lean_unbox_usize(v_x_1524_);
lean_dec(v_x_1524_);
v_res_1527_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8_spec__13___redArg(v_x_1523_, v_x_12228__boxed_1526_, v_x_1525_);
lean_dec(v_x_1525_);
lean_dec_ref(v_x_1523_);
v_r_1528_ = lean_box(v_res_1527_);
return v_r_1528_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8___redArg(lean_object* v_x_1529_, lean_object* v_x_1530_){
_start:
{
uint64_t v___y_1532_; 
if (lean_obj_tag(v_x_1530_) == 0)
{
uint64_t v___x_1535_; 
v___x_1535_ = 1723ULL;
v___y_1532_ = v___x_1535_;
goto v___jp_1531_;
}
else
{
uint64_t v_hash_1536_; 
v_hash_1536_ = lean_ctor_get_uint64(v_x_1530_, sizeof(void*)*2);
v___y_1532_ = v_hash_1536_;
goto v___jp_1531_;
}
v___jp_1531_:
{
size_t v___x_1533_; uint8_t v___x_1534_; 
v___x_1533_ = lean_uint64_to_usize(v___y_1532_);
v___x_1534_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8_spec__13___redArg(v_x_1529_, v___x_1533_, v_x_1530_);
return v___x_1534_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8___redArg___boxed(lean_object* v_x_1537_, lean_object* v_x_1538_){
_start:
{
uint8_t v_res_1539_; lean_object* v_r_1540_; 
v_res_1539_ = l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8___redArg(v_x_1537_, v_x_1538_);
lean_dec(v_x_1538_);
lean_dec_ref(v_x_1537_);
v_r_1540_ = lean_box(v_res_1539_);
return v_r_1540_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__15_spec__19_spec__21___redArg(lean_object* v_b_1541_, lean_object* v_acc_1542_, lean_object* v_i_1543_){
_start:
{
lean_object* v___y_1545_; lean_object* v_keyArray_1553_; lean_object* v_valueArray_1554_; lean_object* v___x_1555_; uint8_t v___x_1556_; 
v_keyArray_1553_ = lean_ctor_get(v_b_1541_, 1);
v_valueArray_1554_ = lean_ctor_get(v_b_1541_, 2);
v___x_1555_ = lean_array_get_size(v_keyArray_1553_);
v___x_1556_ = lean_nat_dec_lt(v_i_1543_, v___x_1555_);
if (v___x_1556_ == 0)
{
lean_dec(v_i_1543_);
return v_acc_1542_;
}
else
{
lean_object* v___x_1557_; uint8_t v_isSome_1558_; 
v___x_1557_ = lean_array_fget_borrowed(v_keyArray_1553_, v_i_1543_);
v_isSome_1558_ = lean_noption_is_some(v___x_1557_);
if (v_isSome_1558_ == 0)
{
goto v___jp_1549_;
}
else
{
lean_object* v___x_1559_; uint8_t v_isSome_1560_; 
v___x_1559_ = lean_array_fget_borrowed(v_valueArray_1554_, v_i_1543_);
v_isSome_1560_ = lean_noption_is_some(v___x_1559_);
if (v_isSome_1560_ == 0)
{
goto v___jp_1549_;
}
else
{
lean_object* v_val_1561_; lean_object* v_val_1562_; lean_object* v_i_1564_; lean_object* v___x_1569_; 
lean_inc(v___x_1557_);
v_val_1561_ = lean_noption_get(v___x_1557_);
lean_inc(v___x_1559_);
v_val_1562_ = lean_noption_get(v___x_1559_);
v___x_1569_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5_spec__8___redArg(v_acc_1542_, v_val_1561_);
switch(lean_obj_tag(v___x_1569_))
{
case 0:
{
lean_object* v_index_1570_; lean_object* v_size_1571_; lean_object* v___x_1572_; 
v_index_1570_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_index_1570_);
lean_dec_ref_known(v___x_1569_, 3);
v_size_1571_ = lean_ctor_get(v_acc_1542_, 0);
lean_inc(v_size_1571_);
v___x_1572_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1542_, v_size_1571_, v_index_1570_, v_val_1561_, v_val_1562_);
lean_dec(v_index_1570_);
v___y_1545_ = v___x_1572_;
goto v___jp_1544_;
}
case 1:
{
lean_object* v_index_1573_; 
v_index_1573_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_index_1573_);
lean_dec_ref_known(v___x_1569_, 1);
v_i_1564_ = v_index_1573_;
goto v___jp_1563_;
}
default: 
{
lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1574_ = lean_unsigned_to_nat(0u);
v___x_1575_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_1542_, v___x_1574_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v_index_1576_; 
v_index_1576_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_index_1576_);
lean_dec_ref_known(v___x_1575_, 1);
v_i_1564_ = v_index_1576_;
goto v___jp_1563_;
}
else
{
lean_dec(v_val_1562_);
lean_dec(v_val_1561_);
v___y_1545_ = v_acc_1542_;
goto v___jp_1544_;
}
}
}
v___jp_1563_:
{
lean_object* v_size_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
v_size_1565_ = lean_ctor_get(v_acc_1542_, 0);
v___x_1566_ = lean_unsigned_to_nat(1u);
v___x_1567_ = lean_nat_add(v_size_1565_, v___x_1566_);
v___x_1568_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1542_, v___x_1567_, v_i_1564_, v_val_1561_, v_val_1562_);
lean_dec(v_i_1564_);
v___y_1545_ = v___x_1568_;
goto v___jp_1544_;
}
}
}
}
v___jp_1544_:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1546_ = lean_unsigned_to_nat(1u);
v___x_1547_ = lean_nat_add(v_i_1543_, v___x_1546_);
lean_dec(v_i_1543_);
v_acc_1542_ = v___y_1545_;
v_i_1543_ = v___x_1547_;
goto _start;
}
v___jp_1549_:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1550_ = lean_unsigned_to_nat(1u);
v___x_1551_ = lean_nat_add(v_i_1543_, v___x_1550_);
lean_dec(v_i_1543_);
v_i_1543_ = v___x_1551_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__15_spec__19_spec__21___redArg___boxed(lean_object* v_b_1577_, lean_object* v_acc_1578_, lean_object* v_i_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__15_spec__19_spec__21___redArg(v_b_1577_, v_acc_1578_, v_i_1579_);
lean_dec_ref(v_b_1577_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__15_spec__19___redArg(lean_object* v_init_1581_, lean_object* v_b_1582_){
_start:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1583_ = lean_unsigned_to_nat(0u);
v___x_1584_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__15_spec__19_spec__21___redArg(v_b_1582_, v_init_1581_, v___x_1583_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__15_spec__19___redArg___boxed(lean_object* v_init_1585_, lean_object* v_b_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__15_spec__19___redArg(v_init_1585_, v_b_1586_);
lean_dec_ref(v_b_1586_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__15___redArg(lean_object* v_m_1588_){
_start:
{
lean_object* v_keyArray_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v_cellCount_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v_target_1596_; lean_object* v___x_1597_; 
v_keyArray_1589_ = lean_ctor_get(v_m_1588_, 1);
v___x_1590_ = lean_array_get_size(v_keyArray_1589_);
v___x_1591_ = lean_unsigned_to_nat(2u);
v_cellCount_1592_ = lean_nat_mul(v___x_1590_, v___x_1591_);
v___x_1593_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_1592_);
v___x_1594_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1592_);
v___x_1595_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1592_);
v_target_1596_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_1596_, 0, v___x_1593_);
lean_ctor_set(v_target_1596_, 1, v___x_1594_);
lean_ctor_set(v_target_1596_, 2, v___x_1595_);
v___x_1597_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__15_spec__19___redArg(v_target_1596_, v_m_1588_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__15___redArg___boxed(lean_object* v_m_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__15___redArg(v_m_1598_);
lean_dec_ref(v_m_1598_);
return v_res_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9(lean_object* v___x_1600_, lean_object* v___x_1601_, uint8_t v___y_1602_, lean_object* v_ignoreTacticKinds_1603_, lean_object* v_stx_1604_, lean_object* v_a_1605_){
_start:
{
lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v_i_1618_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1639_; lean_object* v___y_1640_; lean_object* v_i_1641_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1661_; uint8_t v___y_1662_; 
if (lean_obj_tag(v_stx_1604_) == 1)
{
lean_object* v_kind_1701_; lean_object* v_args_1702_; lean_object* v___y_1704_; lean_object* v___y_1708_; uint8_t v___x_1709_; 
v_kind_1701_ = lean_ctor_get(v_stx_1604_, 1);
v_args_1702_ = lean_ctor_get(v_stx_1604_, 2);
v___x_1709_ = l_Lean_Linter_Extra_UnreachableTactic_isIgnoreTacticKind(v_ignoreTacticKinds_1603_, v_kind_1701_);
if (v___x_1709_ == 0)
{
lean_object* v___x_1710_; lean_object* v___x_1711_; uint8_t v___x_1712_; 
v___x_1710_ = lean_unsigned_to_nat(0u);
v___x_1711_ = lean_array_get_size(v_args_1702_);
v___x_1712_ = lean_nat_dec_lt(v___x_1710_, v___x_1711_);
if (v___x_1712_ == 0)
{
v___y_1704_ = v_a_1605_;
goto v___jp_1703_;
}
else
{
lean_object* v___x_1713_; uint8_t v___x_1714_; 
v___x_1713_ = lean_box(0);
v___x_1714_ = lean_nat_dec_le(v___x_1711_, v___x_1711_);
if (v___x_1714_ == 0)
{
if (v___x_1712_ == 0)
{
v___y_1704_ = v_a_1605_;
goto v___jp_1703_;
}
else
{
size_t v___x_1715_; size_t v___x_1716_; lean_object* v___x_1717_; 
v___x_1715_ = ((size_t)0ULL);
v___x_1716_ = lean_usize_of_nat(v___x_1711_);
v___x_1717_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__16(v___x_1600_, v___x_1601_, v___y_1602_, v_ignoreTacticKinds_1603_, v_args_1702_, v___x_1715_, v___x_1716_, v___x_1713_, v_a_1605_);
v___y_1708_ = v___x_1717_;
goto v___jp_1707_;
}
}
else
{
size_t v___x_1718_; size_t v___x_1719_; lean_object* v___x_1720_; 
v___x_1718_ = ((size_t)0ULL);
v___x_1719_ = lean_usize_of_nat(v___x_1711_);
v___x_1720_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__16(v___x_1600_, v___x_1601_, v___y_1602_, v_ignoreTacticKinds_1603_, v_args_1702_, v___x_1718_, v___x_1719_, v___x_1713_, v_a_1605_);
v___y_1708_ = v___x_1720_;
goto v___jp_1707_;
}
}
}
else
{
v___y_1704_ = v_a_1605_;
goto v___jp_1703_;
}
v___jp_1703_:
{
uint8_t v___x_1705_; 
v___x_1705_ = l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8___redArg(v___x_1600_, v_kind_1701_);
if (v___x_1705_ == 0)
{
uint8_t v___x_1706_; 
v___x_1706_ = l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8___redArg(v___x_1601_, v_kind_1701_);
v___y_1661_ = v___y_1704_;
v___y_1662_ = v___x_1706_;
goto v___jp_1660_;
}
else
{
v___y_1661_ = v___y_1704_;
v___y_1662_ = v___y_1602_;
goto v___jp_1660_;
}
}
v___jp_1707_:
{
if (lean_obj_tag(v___y_1708_) == 0)
{
lean_dec_ref_known(v___y_1708_, 1);
v___y_1704_ = v_a_1605_;
goto v___jp_1703_;
}
else
{
lean_dec_ref_known(v_stx_1604_, 3);
return v___y_1708_;
}
}
}
else
{
lean_object* v___x_1721_; lean_object* v___x_1722_; 
lean_dec(v_stx_1604_);
v___x_1721_ = lean_box(0);
v___x_1722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1722_, 0, v___x_1721_);
return v___x_1722_;
}
v___jp_1607_:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1611_ = lean_st_ref_put(v___y_1608_, v___y_1610_);
v___x_1612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1612_, 0, v___y_1609_);
return v___x_1612_;
}
v___jp_1613_:
{
lean_object* v_size_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
v_size_1619_ = lean_ctor_get(v___y_1617_, 0);
v___x_1620_ = lean_unsigned_to_nat(1u);
v___x_1621_ = lean_nat_add(v_size_1619_, v___x_1620_);
v___x_1622_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1617_, v___x_1621_, v_i_1618_, v___y_1615_, v_stx_1604_);
lean_dec(v_i_1618_);
v___y_1608_ = v___y_1614_;
v___y_1609_ = v___y_1616_;
v___y_1610_ = v___x_1622_;
goto v___jp_1607_;
}
v___jp_1623_:
{
lean_object* v___x_1628_; 
v___x_1628_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5_spec__8___redArg(v___y_1627_, v___y_1625_);
switch(lean_obj_tag(v___x_1628_))
{
case 0:
{
lean_object* v_index_1629_; lean_object* v_size_1630_; lean_object* v___x_1631_; 
v_index_1629_ = lean_ctor_get(v___x_1628_, 0);
lean_inc(v_index_1629_);
lean_dec_ref_known(v___x_1628_, 3);
v_size_1630_ = lean_ctor_get(v___y_1627_, 0);
lean_inc(v_size_1630_);
v___x_1631_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1627_, v_size_1630_, v_index_1629_, v___y_1625_, v_stx_1604_);
lean_dec(v_index_1629_);
v___y_1608_ = v___y_1624_;
v___y_1609_ = v___y_1626_;
v___y_1610_ = v___x_1631_;
goto v___jp_1607_;
}
case 1:
{
lean_object* v_index_1632_; 
v_index_1632_ = lean_ctor_get(v___x_1628_, 0);
lean_inc(v_index_1632_);
lean_dec_ref_known(v___x_1628_, 1);
v___y_1614_ = v___y_1624_;
v___y_1615_ = v___y_1625_;
v___y_1616_ = v___y_1626_;
v___y_1617_ = v___y_1627_;
v_i_1618_ = v_index_1632_;
goto v___jp_1613_;
}
default: 
{
lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1633_ = lean_unsigned_to_nat(0u);
v___x_1634_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1627_, v___x_1633_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_index_1635_; 
v_index_1635_ = lean_ctor_get(v___x_1634_, 0);
lean_inc(v_index_1635_);
lean_dec_ref_known(v___x_1634_, 1);
v___y_1614_ = v___y_1624_;
v___y_1615_ = v___y_1625_;
v___y_1616_ = v___y_1626_;
v___y_1617_ = v___y_1627_;
v_i_1618_ = v_index_1635_;
goto v___jp_1613_;
}
else
{
lean_dec_ref(v___y_1625_);
lean_dec(v_stx_1604_);
v___y_1608_ = v___y_1624_;
v___y_1609_ = v___y_1626_;
v___y_1610_ = v___y_1627_;
goto v___jp_1607_;
}
}
}
}
v___jp_1636_:
{
lean_object* v_size_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
v_size_1642_ = lean_ctor_get(v___y_1640_, 0);
v___x_1643_ = lean_unsigned_to_nat(1u);
v___x_1644_ = lean_nat_add(v_size_1642_, v___x_1643_);
v___x_1645_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1640_, v___x_1644_, v_i_1641_, v___y_1638_, v_stx_1604_);
lean_dec(v_i_1641_);
v___y_1608_ = v___y_1637_;
v___y_1609_ = v___y_1639_;
v___y_1610_ = v___x_1645_;
goto v___jp_1607_;
}
v___jp_1646_:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1651_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__15___redArg(v___y_1647_);
lean_dec_ref(v___y_1647_);
v___x_1652_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5_spec__8___redArg(v___x_1651_, v___y_1649_);
switch(lean_obj_tag(v___x_1652_))
{
case 0:
{
lean_object* v_index_1653_; lean_object* v_size_1654_; lean_object* v___x_1655_; 
v_index_1653_ = lean_ctor_get(v___x_1652_, 0);
lean_inc(v_index_1653_);
lean_dec_ref_known(v___x_1652_, 3);
v_size_1654_ = lean_ctor_get(v___x_1651_, 0);
lean_inc(v_size_1654_);
v___x_1655_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1651_, v_size_1654_, v_index_1653_, v___y_1649_, v_stx_1604_);
lean_dec(v_index_1653_);
v___y_1608_ = v___y_1648_;
v___y_1609_ = v___y_1650_;
v___y_1610_ = v___x_1655_;
goto v___jp_1607_;
}
case 1:
{
lean_object* v_index_1656_; 
v_index_1656_ = lean_ctor_get(v___x_1652_, 0);
lean_inc(v_index_1656_);
lean_dec_ref_known(v___x_1652_, 1);
v___y_1637_ = v___y_1648_;
v___y_1638_ = v___y_1649_;
v___y_1639_ = v___y_1650_;
v___y_1640_ = v___x_1651_;
v_i_1641_ = v_index_1656_;
goto v___jp_1636_;
}
default: 
{
lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1657_ = lean_unsigned_to_nat(0u);
v___x_1658_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1651_, v___x_1657_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_index_1659_; 
v_index_1659_ = lean_ctor_get(v___x_1658_, 0);
lean_inc(v_index_1659_);
lean_dec_ref_known(v___x_1658_, 1);
v___y_1637_ = v___y_1648_;
v___y_1638_ = v___y_1649_;
v___y_1639_ = v___y_1650_;
v___y_1640_ = v___x_1651_;
v_i_1641_ = v_index_1659_;
goto v___jp_1636_;
}
else
{
lean_dec_ref(v___y_1649_);
lean_dec(v_stx_1604_);
v___y_1608_ = v___y_1648_;
v___y_1609_ = v___y_1650_;
v___y_1610_ = v___x_1651_;
goto v___jp_1607_;
}
}
}
}
v___jp_1660_:
{
if (v___y_1662_ == 0)
{
lean_object* v___x_1663_; lean_object* v___x_1664_; 
lean_dec(v_stx_1604_);
v___x_1663_ = lean_box(0);
v___x_1664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1663_);
return v___x_1664_;
}
else
{
lean_object* v___x_1665_; 
v___x_1665_ = l_Lean_Syntax_getRange_x3f(v_stx_1604_, v___y_1662_);
if (lean_obj_tag(v___x_1665_) == 1)
{
lean_object* v_val_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v_val_1666_ = lean_ctor_get(v___x_1665_, 0);
lean_inc(v_val_1666_);
lean_dec_ref_known(v___x_1665_, 1);
v___x_1667_ = lean_st_ref_take(v___y_1661_);
v___x_1668_ = lean_box(0);
v___x_1669_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5_spec__8___redArg(v___x_1667_, v_val_1666_);
switch(lean_obj_tag(v___x_1669_))
{
case 0:
{
lean_object* v_index_1670_; lean_object* v_size_1671_; lean_object* v___x_1672_; 
v_index_1670_ = lean_ctor_get(v___x_1669_, 0);
lean_inc(v_index_1670_);
lean_dec_ref_known(v___x_1669_, 3);
v_size_1671_ = lean_ctor_get(v___x_1667_, 0);
lean_inc(v_size_1671_);
v___x_1672_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1667_, v_size_1671_, v_index_1670_, v_val_1666_, v_stx_1604_);
lean_dec(v_index_1670_);
v___y_1608_ = v___y_1661_;
v___y_1609_ = v___x_1668_;
v___y_1610_ = v___x_1672_;
goto v___jp_1607_;
}
case 1:
{
lean_object* v_index_1673_; lean_object* v_size_1674_; lean_object* v_keyArray_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; uint8_t v___x_1679_; 
v_index_1673_ = lean_ctor_get(v___x_1669_, 0);
lean_inc(v_index_1673_);
lean_dec_ref_known(v___x_1669_, 1);
v_size_1674_ = lean_ctor_get(v___x_1667_, 0);
lean_inc(v_size_1674_);
v_keyArray_1675_ = lean_ctor_get(v___x_1667_, 1);
lean_inc_ref(v_keyArray_1675_);
v___x_1676_ = lean_unsigned_to_nat(1u);
v___x_1677_ = lean_nat_add(v_size_1674_, v___x_1676_);
lean_dec(v_size_1674_);
v___x_1678_ = lean_array_get_size(v_keyArray_1675_);
lean_dec_ref(v_keyArray_1675_);
v___x_1679_ = lean_nat_dec_lt(v___x_1677_, v___x_1678_);
if (v___x_1679_ == 0)
{
lean_dec(v___x_1677_);
lean_dec(v_index_1673_);
v___y_1647_ = v___x_1667_;
v___y_1648_ = v___y_1661_;
v___y_1649_ = v_val_1666_;
v___y_1650_ = v___x_1668_;
goto v___jp_1646_;
}
else
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; uint8_t v___x_1684_; 
v___x_1680_ = lean_unsigned_to_nat(4u);
v___x_1681_ = lean_nat_mul(v___x_1677_, v___x_1680_);
v___x_1682_ = lean_unsigned_to_nat(3u);
v___x_1683_ = lean_nat_mul(v___x_1678_, v___x_1682_);
v___x_1684_ = lean_nat_dec_le(v___x_1681_, v___x_1683_);
lean_dec(v___x_1683_);
lean_dec(v___x_1681_);
if (v___x_1684_ == 0)
{
lean_dec(v___x_1677_);
lean_dec(v_index_1673_);
v___y_1647_ = v___x_1667_;
v___y_1648_ = v___y_1661_;
v___y_1649_ = v_val_1666_;
v___y_1650_ = v___x_1668_;
goto v___jp_1646_;
}
else
{
lean_object* v___x_1685_; 
v___x_1685_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1667_, v___x_1677_, v_index_1673_, v_val_1666_, v_stx_1604_);
lean_dec(v_index_1673_);
v___y_1608_ = v___y_1661_;
v___y_1609_ = v___x_1668_;
v___y_1610_ = v___x_1685_;
goto v___jp_1607_;
}
}
}
default: 
{
lean_object* v_size_1686_; lean_object* v_keyArray_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; uint8_t v___x_1691_; 
v_size_1686_ = lean_ctor_get(v___x_1667_, 0);
lean_inc(v_size_1686_);
v_keyArray_1687_ = lean_ctor_get(v___x_1667_, 1);
lean_inc_ref(v_keyArray_1687_);
v___x_1688_ = lean_unsigned_to_nat(1u);
v___x_1689_ = lean_nat_add(v_size_1686_, v___x_1688_);
lean_dec(v_size_1686_);
v___x_1690_ = lean_array_get_size(v_keyArray_1687_);
lean_dec_ref(v_keyArray_1687_);
v___x_1691_ = lean_nat_dec_lt(v___x_1689_, v___x_1690_);
if (v___x_1691_ == 0)
{
lean_object* v___x_1692_; 
lean_dec(v___x_1689_);
v___x_1692_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__15___redArg(v___x_1667_);
lean_dec(v___x_1667_);
v___y_1624_ = v___y_1661_;
v___y_1625_ = v_val_1666_;
v___y_1626_ = v___x_1668_;
v___y_1627_ = v___x_1692_;
goto v___jp_1623_;
}
else
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; uint8_t v___x_1697_; 
v___x_1693_ = lean_unsigned_to_nat(4u);
v___x_1694_ = lean_nat_mul(v___x_1689_, v___x_1693_);
lean_dec(v___x_1689_);
v___x_1695_ = lean_unsigned_to_nat(3u);
v___x_1696_ = lean_nat_mul(v___x_1690_, v___x_1695_);
v___x_1697_ = lean_nat_dec_le(v___x_1694_, v___x_1696_);
lean_dec(v___x_1696_);
lean_dec(v___x_1694_);
if (v___x_1697_ == 0)
{
lean_object* v___x_1698_; 
v___x_1698_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__15___redArg(v___x_1667_);
lean_dec(v___x_1667_);
v___y_1624_ = v___y_1661_;
v___y_1625_ = v_val_1666_;
v___y_1626_ = v___x_1668_;
v___y_1627_ = v___x_1698_;
goto v___jp_1623_;
}
else
{
v___y_1624_ = v___y_1661_;
v___y_1625_ = v_val_1666_;
v___y_1626_ = v___x_1668_;
v___y_1627_ = v___x_1667_;
goto v___jp_1623_;
}
}
}
}
}
else
{
lean_object* v___x_1699_; lean_object* v___x_1700_; 
lean_dec(v___x_1665_);
lean_dec(v_stx_1604_);
v___x_1699_ = lean_box(0);
v___x_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1700_, 0, v___x_1699_);
return v___x_1700_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__16(lean_object* v___x_1723_, lean_object* v___x_1724_, uint8_t v___y_1725_, lean_object* v_ignoreTacticKinds_1726_, lean_object* v_as_1727_, size_t v_i_1728_, size_t v_stop_1729_, lean_object* v_b_1730_, lean_object* v___y_1731_){
_start:
{
uint8_t v___x_1733_; 
v___x_1733_ = lean_usize_dec_eq(v_i_1728_, v_stop_1729_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1734_ = lean_array_uget_borrowed(v_as_1727_, v_i_1728_);
lean_inc(v___x_1734_);
v___x_1735_ = l_Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9(v___x_1723_, v___x_1724_, v___y_1725_, v_ignoreTacticKinds_1726_, v___x_1734_, v___y_1731_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v_a_1736_; size_t v___x_1737_; size_t v___x_1738_; 
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
lean_inc(v_a_1736_);
lean_dec_ref_known(v___x_1735_, 1);
v___x_1737_ = ((size_t)1ULL);
v___x_1738_ = lean_usize_add(v_i_1728_, v___x_1737_);
v_i_1728_ = v___x_1738_;
v_b_1730_ = v_a_1736_;
goto _start;
}
else
{
return v___x_1735_;
}
}
else
{
lean_object* v___x_1740_; 
v___x_1740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1740_, 0, v_b_1730_);
return v___x_1740_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__16___boxed(lean_object* v___x_1741_, lean_object* v___x_1742_, lean_object* v___y_1743_, lean_object* v_ignoreTacticKinds_1744_, lean_object* v_as_1745_, lean_object* v_i_1746_, lean_object* v_stop_1747_, lean_object* v_b_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
uint8_t v___y_12354__boxed_1751_; size_t v_i_boxed_1752_; size_t v_stop_boxed_1753_; lean_object* v_res_1754_; 
v___y_12354__boxed_1751_ = lean_unbox(v___y_1743_);
v_i_boxed_1752_ = lean_unbox_usize(v_i_1746_);
lean_dec(v_i_1746_);
v_stop_boxed_1753_ = lean_unbox_usize(v_stop_1747_);
lean_dec(v_stop_1747_);
v_res_1754_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__16(v___x_1741_, v___x_1742_, v___y_12354__boxed_1751_, v_ignoreTacticKinds_1744_, v_as_1745_, v_i_boxed_1752_, v_stop_boxed_1753_, v_b_1748_, v___y_1749_);
lean_dec(v___y_1749_);
lean_dec_ref(v_as_1745_);
lean_dec_ref(v_ignoreTacticKinds_1744_);
lean_dec_ref(v___x_1742_);
lean_dec_ref(v___x_1741_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9___boxed(lean_object* v___x_1755_, lean_object* v___x_1756_, lean_object* v___y_1757_, lean_object* v_ignoreTacticKinds_1758_, lean_object* v_stx_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_){
_start:
{
uint8_t v___y_12368__boxed_1762_; lean_object* v_res_1763_; 
v___y_12368__boxed_1762_ = lean_unbox(v___y_1757_);
v_res_1763_ = l_Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9(v___x_1755_, v___x_1756_, v___y_12368__boxed_1762_, v_ignoreTacticKinds_1758_, v_stx_1759_, v_a_1760_);
lean_dec(v_a_1760_);
lean_dec_ref(v_ignoreTacticKinds_1758_);
lean_dec_ref(v___x_1756_);
lean_dec_ref(v___x_1755_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1___redArg(lean_object* v_o_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v___x_1767_; lean_object* v_env_1768_; lean_object* v___x_1769_; lean_object* v_toEnvExtension_1770_; lean_object* v_asyncMode_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v_merged_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1783_; 
v___x_1767_ = lean_st_ref_get(v___y_1765_);
v_env_1768_ = lean_ctor_get(v___x_1767_, 0);
lean_inc_ref(v_env_1768_);
lean_dec(v___x_1767_);
v___x_1769_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_1770_ = lean_ctor_get(v___x_1769_, 0);
v_asyncMode_1771_ = lean_ctor_get(v_toEnvExtension_1770_, 2);
v___x_1772_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_1773_ = lean_box(0);
v___x_1774_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1772_, v___x_1769_, v_env_1768_, v_asyncMode_1771_, v___x_1773_);
v_merged_1775_ = lean_ctor_get(v___x_1774_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1783_ == 0)
{
lean_object* v_unused_1784_; 
v_unused_1784_ = lean_ctor_get(v___x_1774_, 1);
lean_dec(v_unused_1784_);
v___x_1777_ = v___x_1774_;
v_isShared_1778_ = v_isSharedCheck_1783_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_merged_1775_);
lean_dec(v___x_1774_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1783_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1780_; 
if (v_isShared_1778_ == 0)
{
lean_ctor_set(v___x_1777_, 1, v_merged_1775_);
lean_ctor_set(v___x_1777_, 0, v_o_1764_);
v___x_1780_ = v___x_1777_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_o_1764_);
lean_ctor_set(v_reuseFailAlloc_1782_, 1, v_merged_1775_);
v___x_1780_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
lean_object* v___x_1781_; 
v___x_1781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1780_);
return v___x_1781_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1___redArg___boxed(lean_object* v_o_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1___redArg(v_o_1785_, v___y_1786_);
lean_dec(v___y_1786_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1(lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v___x_1792_; lean_object* v_scopes_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v_opts_1796_; lean_object* v___x_1797_; 
v___x_1792_ = lean_st_ref_get(v___y_1790_);
v_scopes_1793_ = lean_ctor_get(v___x_1792_, 2);
lean_inc(v_scopes_1793_);
lean_dec(v___x_1792_);
v___x_1794_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1795_ = l_List_head_x21___redArg(v___x_1794_, v_scopes_1793_);
lean_dec(v_scopes_1793_);
v_opts_1796_ = lean_ctor_get(v___x_1795_, 1);
lean_inc_ref(v_opts_1796_);
lean_dec(v___x_1795_);
v___x_1797_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1___redArg(v_opts_1796_, v___y_1790_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1___boxed(lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_){
_start:
{
lean_object* v_res_1801_; 
v_res_1801_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1(v___y_1798_, v___y_1799_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
return v_res_1801_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___lam__0(lean_object* v_r_1802_){
_start:
{
lean_object* v_start_1803_; lean_object* v_stop_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1813_; 
v_start_1803_ = lean_ctor_get(v_r_1802_, 0);
v_stop_1804_ = lean_ctor_get(v_r_1802_, 1);
v_isSharedCheck_1813_ = !lean_is_exclusive(v_r_1802_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1806_ = v_r_1802_;
v_isShared_1807_ = v_isSharedCheck_1813_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_stop_1804_);
lean_inc(v_start_1803_);
lean_dec(v_r_1802_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1813_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1811_; 
v___x_1808_ = lean_nat_to_int(v_stop_1804_);
v___x_1809_ = lean_int_neg(v___x_1808_);
lean_dec(v___x_1808_);
if (v_isShared_1807_ == 0)
{
lean_ctor_set(v___x_1806_, 1, v___x_1809_);
v___x_1811_ = v___x_1806_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_start_1803_);
lean_ctor_set(v_reuseFailAlloc_1812_, 1, v___x_1809_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___lam__1(lean_object* v___f_1816_, uint8_t v___x_1817_, lean_object* v_x1_1818_, lean_object* v_x2_1819_){
_start:
{
lean_object* v_fst_1820_; lean_object* v_fst_1821_; lean_object* v___f_1822_; lean_object* v___f_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_12179__overap_1826_; lean_object* v___x_1827_; uint8_t v___x_1828_; 
v_fst_1820_ = lean_ctor_get(v_x1_1818_, 0);
lean_inc(v_fst_1820_);
lean_dec_ref(v_x1_1818_);
v_fst_1821_ = lean_ctor_get(v_x2_1819_, 0);
lean_inc(v_fst_1821_);
lean_dec_ref(v_x2_1819_);
v___f_1822_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___lam__1___closed__0));
v___f_1823_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___lam__1___closed__1));
lean_inc_ref(v___f_1816_);
v___x_1824_ = lean_apply_1(v___f_1816_, v_fst_1820_);
v___x_1825_ = lean_apply_1(v___f_1816_, v_fst_1821_);
v___x_12179__overap_1826_ = l_lexOrd___redArg(v___f_1822_, v___f_1823_);
v___x_1827_ = lean_apply_2(v___x_12179__overap_1826_, v___x_1824_, v___x_1825_);
v___x_1828_ = lean_unbox(v___x_1827_);
if (v___x_1828_ == 0)
{
return v___x_1817_;
}
else
{
uint8_t v___x_1829_; 
v___x_1829_ = 0;
return v___x_1829_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___lam__1___boxed(lean_object* v___f_1830_, lean_object* v___x_1831_, lean_object* v_x1_1832_, lean_object* v_x2_1833_){
_start:
{
uint8_t v___x_12683__boxed_1834_; uint8_t v_res_1835_; lean_object* v_r_1836_; 
v___x_12683__boxed_1834_ = lean_unbox(v___x_1831_);
v_res_1835_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___lam__1(v___f_1830_, v___x_12683__boxed_1834_, v_x1_1832_, v_x2_1833_);
v_r_1836_ = lean_box(v_res_1835_);
return v_r_1836_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7_spec__11___redArg(lean_object* v_hi_1837_, lean_object* v_pivot_1838_, lean_object* v_as_1839_, lean_object* v_i_1840_, lean_object* v_k_1841_){
_start:
{
uint8_t v___x_1846_; 
v___x_1846_ = lean_nat_dec_lt(v_k_1841_, v_hi_1837_);
if (v___x_1846_ == 0)
{
lean_object* v___x_1847_; lean_object* v___x_1848_; 
lean_dec(v_k_1841_);
lean_dec_ref(v_pivot_1838_);
v___x_1847_ = lean_array_fswap(v_as_1839_, v_i_1840_, v_hi_1837_);
v___x_1848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1848_, 0, v_i_1840_);
lean_ctor_set(v___x_1848_, 1, v___x_1847_);
return v___x_1848_;
}
else
{
lean_object* v___x_1849_; lean_object* v_fst_1850_; lean_object* v_fst_1851_; lean_object* v___f_1852_; lean_object* v___f_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_11914__overap_1856_; lean_object* v___x_1857_; uint8_t v___x_1858_; 
v___x_1849_ = lean_array_fget_borrowed(v_as_1839_, v_k_1841_);
v_fst_1850_ = lean_ctor_get(v___x_1849_, 0);
v_fst_1851_ = lean_ctor_get(v_pivot_1838_, 0);
v___f_1852_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___lam__1___closed__0));
v___f_1853_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___lam__1___closed__1));
lean_inc(v_fst_1850_);
v___x_1854_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___lam__0(v_fst_1850_);
lean_inc(v_fst_1851_);
v___x_1855_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___lam__0(v_fst_1851_);
v___x_11914__overap_1856_ = l_lexOrd___redArg(v___f_1852_, v___f_1853_);
v___x_1857_ = lean_apply_2(v___x_11914__overap_1856_, v___x_1854_, v___x_1855_);
v___x_1858_ = lean_unbox(v___x_1857_);
if (v___x_1858_ == 0)
{
if (v___x_1846_ == 0)
{
goto v___jp_1842_;
}
else
{
lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1859_ = lean_array_fswap(v_as_1839_, v_i_1840_, v_k_1841_);
v___x_1860_ = lean_unsigned_to_nat(1u);
v___x_1861_ = lean_nat_add(v_i_1840_, v___x_1860_);
lean_dec(v_i_1840_);
v___x_1862_ = lean_nat_add(v_k_1841_, v___x_1860_);
lean_dec(v_k_1841_);
v_as_1839_ = v___x_1859_;
v_i_1840_ = v___x_1861_;
v_k_1841_ = v___x_1862_;
goto _start;
}
}
else
{
goto v___jp_1842_;
}
}
v___jp_1842_:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1843_ = lean_unsigned_to_nat(1u);
v___x_1844_ = lean_nat_add(v_k_1841_, v___x_1843_);
lean_dec(v_k_1841_);
v_k_1841_ = v___x_1844_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7_spec__11___redArg___boxed(lean_object* v_hi_1864_, lean_object* v_pivot_1865_, lean_object* v_as_1866_, lean_object* v_i_1867_, lean_object* v_k_1868_){
_start:
{
lean_object* v_res_1869_; 
v_res_1869_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7_spec__11___redArg(v_hi_1864_, v_pivot_1865_, v_as_1866_, v_i_1867_, v_k_1868_);
lean_dec(v_hi_1864_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg(lean_object* v_n_1871_, lean_object* v_as_1872_, lean_object* v_lo_1873_, lean_object* v_hi_1874_){
_start:
{
lean_object* v___y_1876_; uint8_t v___x_1886_; 
v___x_1886_ = lean_nat_dec_lt(v_lo_1873_, v_hi_1874_);
if (v___x_1886_ == 0)
{
lean_dec(v_lo_1873_);
return v_as_1872_;
}
else
{
lean_object* v___f_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v_mid_1890_; lean_object* v___y_1892_; lean_object* v___y_1898_; lean_object* v___x_1903_; lean_object* v___x_1904_; uint8_t v___x_1905_; 
v___f_1887_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___closed__0));
v___x_1888_ = lean_nat_add(v_lo_1873_, v_hi_1874_);
v___x_1889_ = lean_unsigned_to_nat(1u);
v_mid_1890_ = lean_nat_shiftr(v___x_1888_, v___x_1889_);
lean_dec(v___x_1888_);
v___x_1903_ = lean_array_fget_borrowed(v_as_1872_, v_mid_1890_);
v___x_1904_ = lean_array_fget_borrowed(v_as_1872_, v_lo_1873_);
lean_inc(v___x_1904_);
lean_inc(v___x_1903_);
v___x_1905_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___lam__1(v___f_1887_, v___x_1886_, v___x_1903_, v___x_1904_);
if (v___x_1905_ == 0)
{
v___y_1898_ = v_as_1872_;
goto v___jp_1897_;
}
else
{
lean_object* v___x_1906_; 
v___x_1906_ = lean_array_fswap(v_as_1872_, v_lo_1873_, v_mid_1890_);
v___y_1898_ = v___x_1906_;
goto v___jp_1897_;
}
v___jp_1891_:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; uint8_t v___x_1895_; 
v___x_1893_ = lean_array_fget_borrowed(v___y_1892_, v_mid_1890_);
v___x_1894_ = lean_array_fget_borrowed(v___y_1892_, v_hi_1874_);
lean_inc(v___x_1894_);
lean_inc(v___x_1893_);
v___x_1895_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___lam__1(v___f_1887_, v___x_1886_, v___x_1893_, v___x_1894_);
if (v___x_1895_ == 0)
{
lean_dec(v_mid_1890_);
v___y_1876_ = v___y_1892_;
goto v___jp_1875_;
}
else
{
lean_object* v___x_1896_; 
v___x_1896_ = lean_array_fswap(v___y_1892_, v_mid_1890_, v_hi_1874_);
lean_dec(v_mid_1890_);
v___y_1876_ = v___x_1896_;
goto v___jp_1875_;
}
}
v___jp_1897_:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; uint8_t v___x_1901_; 
v___x_1899_ = lean_array_fget_borrowed(v___y_1898_, v_hi_1874_);
v___x_1900_ = lean_array_fget_borrowed(v___y_1898_, v_lo_1873_);
lean_inc(v___x_1900_);
lean_inc(v___x_1899_);
v___x_1901_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___lam__1(v___f_1887_, v___x_1886_, v___x_1899_, v___x_1900_);
if (v___x_1901_ == 0)
{
v___y_1892_ = v___y_1898_;
goto v___jp_1891_;
}
else
{
lean_object* v___x_1902_; 
v___x_1902_ = lean_array_fswap(v___y_1898_, v_lo_1873_, v_hi_1874_);
v___y_1892_ = v___x_1902_;
goto v___jp_1891_;
}
}
}
v___jp_1875_:
{
lean_object* v_pivot_1877_; lean_object* v___x_1878_; lean_object* v_fst_1879_; lean_object* v_snd_1880_; uint8_t v___x_1881_; 
v_pivot_1877_ = lean_array_fget(v___y_1876_, v_hi_1874_);
lean_inc_n(v_lo_1873_, 2);
v___x_1878_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7_spec__11___redArg(v_hi_1874_, v_pivot_1877_, v___y_1876_, v_lo_1873_, v_lo_1873_);
v_fst_1879_ = lean_ctor_get(v___x_1878_, 0);
lean_inc(v_fst_1879_);
v_snd_1880_ = lean_ctor_get(v___x_1878_, 1);
lean_inc(v_snd_1880_);
lean_dec_ref(v___x_1878_);
v___x_1881_ = lean_nat_dec_le(v_hi_1874_, v_fst_1879_);
if (v___x_1881_ == 0)
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1882_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg(v_n_1871_, v_snd_1880_, v_lo_1873_, v_fst_1879_);
v___x_1883_ = lean_unsigned_to_nat(1u);
v___x_1884_ = lean_nat_add(v_fst_1879_, v___x_1883_);
lean_dec(v_fst_1879_);
v_as_1872_ = v___x_1882_;
v_lo_1873_ = v___x_1884_;
goto _start;
}
else
{
lean_dec(v_fst_1879_);
lean_dec(v_lo_1873_);
return v_snd_1880_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___boxed(lean_object* v_n_1907_, lean_object* v_as_1908_, lean_object* v_lo_1909_, lean_object* v_hi_1910_){
_start:
{
lean_object* v_res_1911_; 
v_res_1911_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg(v_n_1907_, v_as_1908_, v_lo_1909_, v_hi_1910_);
lean_dec(v_hi_1910_);
lean_dec(v_n_1907_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5_spec__8(lean_object* v_b_1912_, lean_object* v_acc_1913_, lean_object* v_i_1914_){
_start:
{
lean_object* v_keyArray_1919_; lean_object* v_valueArray_1920_; lean_object* v___x_1921_; uint8_t v___x_1922_; 
v_keyArray_1919_ = lean_ctor_get(v_b_1912_, 1);
v_valueArray_1920_ = lean_ctor_get(v_b_1912_, 2);
v___x_1921_ = lean_array_get_size(v_keyArray_1919_);
v___x_1922_ = lean_nat_dec_lt(v_i_1914_, v___x_1921_);
if (v___x_1922_ == 0)
{
lean_dec(v_i_1914_);
return v_acc_1913_;
}
else
{
lean_object* v___x_1923_; uint8_t v_isSome_1924_; 
v___x_1923_ = lean_array_fget_borrowed(v_keyArray_1919_, v_i_1914_);
v_isSome_1924_ = lean_noption_is_some(v___x_1923_);
if (v_isSome_1924_ == 0)
{
goto v___jp_1915_;
}
else
{
lean_object* v___x_1925_; uint8_t v_isSome_1926_; 
v___x_1925_ = lean_array_fget_borrowed(v_valueArray_1920_, v_i_1914_);
v_isSome_1926_ = lean_noption_is_some(v___x_1925_);
if (v_isSome_1926_ == 0)
{
goto v___jp_1915_;
}
else
{
lean_object* v_val_1927_; lean_object* v_val_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
lean_inc(v___x_1923_);
v_val_1927_ = lean_noption_get(v___x_1923_);
lean_inc(v___x_1925_);
v_val_1928_ = lean_noption_get(v___x_1925_);
v___x_1929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1929_, 0, v_val_1927_);
lean_ctor_set(v___x_1929_, 1, v_val_1928_);
v___x_1930_ = lean_array_push(v_acc_1913_, v___x_1929_);
v___x_1931_ = lean_unsigned_to_nat(1u);
v___x_1932_ = lean_nat_add(v_i_1914_, v___x_1931_);
lean_dec(v_i_1914_);
v_acc_1913_ = v___x_1930_;
v_i_1914_ = v___x_1932_;
goto _start;
}
}
}
v___jp_1915_:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1916_ = lean_unsigned_to_nat(1u);
v___x_1917_ = lean_nat_add(v_i_1914_, v___x_1916_);
lean_dec(v_i_1914_);
v_i_1914_ = v___x_1917_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5_spec__8___boxed(lean_object* v_b_1934_, lean_object* v_acc_1935_, lean_object* v_i_1936_){
_start:
{
lean_object* v_res_1937_; 
v_res_1937_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5_spec__8(v_b_1934_, v_acc_1935_, v_i_1936_);
lean_dec_ref(v_b_1934_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5(lean_object* v_init_1938_, lean_object* v_b_1939_){
_start:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1940_ = lean_unsigned_to_nat(0u);
v___x_1941_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5_spec__8(v_b_1939_, v_init_1938_, v___x_1940_);
return v___x_1941_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___boxed(lean_object* v_init_1942_, lean_object* v_b_1943_){
_start:
{
lean_object* v_res_1944_; 
v_res_1944_ = l_Std_DHashMap_Raw_foldM___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5(v_init_1942_, v_b_1943_);
lean_dec_ref(v_b_1943_);
return v_res_1944_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8___redArg(lean_object* v_keys_1945_, lean_object* v_vals_1946_, lean_object* v_i_1947_, lean_object* v_k_1948_){
_start:
{
lean_object* v___x_1949_; uint8_t v___x_1950_; 
v___x_1949_ = lean_array_get_size(v_keys_1945_);
v___x_1950_ = lean_nat_dec_lt(v_i_1947_, v___x_1949_);
if (v___x_1950_ == 0)
{
lean_object* v___x_1951_; 
lean_dec(v_i_1947_);
v___x_1951_ = lean_box(0);
return v___x_1951_;
}
else
{
lean_object* v_k_x27_1952_; uint8_t v___x_1953_; 
v_k_x27_1952_ = lean_array_fget_borrowed(v_keys_1945_, v_i_1947_);
v___x_1953_ = lean_name_eq(v_k_1948_, v_k_x27_1952_);
if (v___x_1953_ == 0)
{
lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___x_1954_ = lean_unsigned_to_nat(1u);
v___x_1955_ = lean_nat_add(v_i_1947_, v___x_1954_);
lean_dec(v_i_1947_);
v_i_1947_ = v___x_1955_;
goto _start;
}
else
{
lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1957_ = lean_array_fget_borrowed(v_vals_1946_, v_i_1947_);
lean_dec(v_i_1947_);
lean_inc(v___x_1957_);
v___x_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1958_, 0, v___x_1957_);
return v___x_1958_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_keys_1959_, lean_object* v_vals_1960_, lean_object* v_i_1961_, lean_object* v_k_1962_){
_start:
{
lean_object* v_res_1963_; 
v_res_1963_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8___redArg(v_keys_1959_, v_vals_1960_, v_i_1961_, v_k_1962_);
lean_dec(v_k_1962_);
lean_dec_ref(v_vals_1960_);
lean_dec_ref(v_keys_1959_);
return v_res_1963_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5___redArg(lean_object* v_x_1964_, size_t v_x_1965_, lean_object* v_x_1966_){
_start:
{
if (lean_obj_tag(v_x_1964_) == 0)
{
lean_object* v_es_1967_; lean_object* v___x_1968_; size_t v___x_1969_; size_t v___x_1970_; lean_object* v_j_1971_; lean_object* v___x_1972_; 
v_es_1967_ = lean_ctor_get(v_x_1964_, 0);
v___x_1968_ = lean_box(2);
v___x_1969_ = ((size_t)31ULL);
v___x_1970_ = lean_usize_land(v_x_1965_, v___x_1969_);
v_j_1971_ = lean_usize_to_nat(v___x_1970_);
v___x_1972_ = lean_array_get_borrowed(v___x_1968_, v_es_1967_, v_j_1971_);
lean_dec(v_j_1971_);
switch(lean_obj_tag(v___x_1972_))
{
case 0:
{
lean_object* v_key_1973_; lean_object* v_val_1974_; uint8_t v___x_1975_; 
v_key_1973_ = lean_ctor_get(v___x_1972_, 0);
v_val_1974_ = lean_ctor_get(v___x_1972_, 1);
v___x_1975_ = lean_name_eq(v_x_1966_, v_key_1973_);
if (v___x_1975_ == 0)
{
lean_object* v___x_1976_; 
v___x_1976_ = lean_box(0);
return v___x_1976_;
}
else
{
lean_object* v___x_1977_; 
lean_inc(v_val_1974_);
v___x_1977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1977_, 0, v_val_1974_);
return v___x_1977_;
}
}
case 1:
{
lean_object* v_node_1978_; size_t v___x_1979_; size_t v___x_1980_; 
v_node_1978_ = lean_ctor_get(v___x_1972_, 0);
v___x_1979_ = ((size_t)5ULL);
v___x_1980_ = lean_usize_shift_right(v_x_1965_, v___x_1979_);
v_x_1964_ = v_node_1978_;
v_x_1965_ = v___x_1980_;
goto _start;
}
default: 
{
lean_object* v___x_1982_; 
v___x_1982_ = lean_box(0);
return v___x_1982_;
}
}
}
else
{
lean_object* v_ks_1983_; lean_object* v_vs_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
v_ks_1983_ = lean_ctor_get(v_x_1964_, 0);
v_vs_1984_ = lean_ctor_get(v_x_1964_, 1);
v___x_1985_ = lean_unsigned_to_nat(0u);
v___x_1986_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8___redArg(v_ks_1983_, v_vs_1984_, v___x_1985_, v_x_1966_);
return v___x_1986_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5___redArg___boxed(lean_object* v_x_1987_, lean_object* v_x_1988_, lean_object* v_x_1989_){
_start:
{
size_t v_x_12866__boxed_1990_; lean_object* v_res_1991_; 
v_x_12866__boxed_1990_ = lean_unbox_usize(v_x_1988_);
lean_dec(v_x_1988_);
v_res_1991_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5___redArg(v_x_1987_, v_x_12866__boxed_1990_, v_x_1989_);
lean_dec(v_x_1989_);
lean_dec_ref(v_x_1987_);
return v_res_1991_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3___redArg(lean_object* v_x_1992_, lean_object* v_x_1993_){
_start:
{
uint64_t v___y_1995_; 
if (lean_obj_tag(v_x_1993_) == 0)
{
uint64_t v___x_1998_; 
v___x_1998_ = 1723ULL;
v___y_1995_ = v___x_1998_;
goto v___jp_1994_;
}
else
{
uint64_t v_hash_1999_; 
v_hash_1999_ = lean_ctor_get_uint64(v_x_1993_, sizeof(void*)*2);
v___y_1995_ = v_hash_1999_;
goto v___jp_1994_;
}
v___jp_1994_:
{
size_t v___x_1996_; lean_object* v___x_1997_; 
v___x_1996_ = lean_uint64_to_usize(v___y_1995_);
v___x_1997_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5___redArg(v_x_1992_, v___x_1996_, v_x_1993_);
return v___x_1997_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3___redArg___boxed(lean_object* v_x_2000_, lean_object* v_x_2001_){
_start:
{
lean_object* v_res_2002_; 
v_res_2002_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3___redArg(v_x_2000_, v_x_2001_);
lean_dec(v_x_2001_);
lean_dec_ref(v_x_2000_);
return v_res_2002_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12___lam__0(uint8_t v___y_2004_, uint8_t v_suppressElabErrors_2005_, lean_object* v_x_2006_){
_start:
{
if (lean_obj_tag(v_x_2006_) == 1)
{
lean_object* v_pre_2007_; 
v_pre_2007_ = lean_ctor_get(v_x_2006_, 0);
if (lean_obj_tag(v_pre_2007_) == 0)
{
lean_object* v_str_2008_; lean_object* v___x_2009_; uint8_t v___x_2010_; 
v_str_2008_ = lean_ctor_get(v_x_2006_, 1);
v___x_2009_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12___lam__0___closed__0));
v___x_2010_ = lean_string_dec_eq(v_str_2008_, v___x_2009_);
if (v___x_2010_ == 0)
{
return v___y_2004_;
}
else
{
return v_suppressElabErrors_2005_;
}
}
else
{
return v___y_2004_;
}
}
else
{
return v___y_2004_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12___lam__0___boxed(lean_object* v___y_2011_, lean_object* v_suppressElabErrors_2012_, lean_object* v_x_2013_){
_start:
{
uint8_t v___y_12930__boxed_2014_; uint8_t v_suppressElabErrors_boxed_2015_; uint8_t v_res_2016_; lean_object* v_r_2017_; 
v___y_12930__boxed_2014_ = lean_unbox(v___y_2011_);
v_suppressElabErrors_boxed_2015_ = lean_unbox(v_suppressElabErrors_2012_);
v_res_2016_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12___lam__0(v___y_12930__boxed_2014_, v_suppressElabErrors_boxed_2015_, v_x_2013_);
lean_dec(v_x_2013_);
v_r_2017_ = lean_box(v_res_2016_);
return v_r_2017_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___redArg___closed__0(void){
_start:
{
lean_object* v___x_2018_; 
v___x_2018_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2018_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___redArg___closed__1(void){
_start:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2019_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___redArg___closed__0);
v___x_2020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2020_, 0, v___x_2019_);
return v___x_2020_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___redArg___closed__2(void){
_start:
{
lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
v___x_2021_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___redArg___closed__1);
v___x_2022_ = lean_unsigned_to_nat(0u);
v___x_2023_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2023_, 0, v___x_2022_);
lean_ctor_set(v___x_2023_, 1, v___x_2022_);
lean_ctor_set(v___x_2023_, 2, v___x_2022_);
lean_ctor_set(v___x_2023_, 3, v___x_2022_);
lean_ctor_set(v___x_2023_, 4, v___x_2021_);
lean_ctor_set(v___x_2023_, 5, v___x_2021_);
lean_ctor_set(v___x_2023_, 6, v___x_2021_);
lean_ctor_set(v___x_2023_, 7, v___x_2021_);
lean_ctor_set(v___x_2023_, 8, v___x_2021_);
lean_ctor_set(v___x_2023_, 9, v___x_2021_);
lean_ctor_set(v___x_2023_, 10, v___x_2021_);
return v___x_2023_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___redArg___closed__3(void){
_start:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2024_ = lean_unsigned_to_nat(32u);
v___x_2025_ = lean_mk_empty_array_with_capacity(v___x_2024_);
v___x_2026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2026_, 0, v___x_2025_);
return v___x_2026_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___redArg___closed__4(void){
_start:
{
size_t v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2027_ = ((size_t)5ULL);
v___x_2028_ = lean_unsigned_to_nat(0u);
v___x_2029_ = lean_unsigned_to_nat(32u);
v___x_2030_ = lean_mk_empty_array_with_capacity(v___x_2029_);
v___x_2031_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___redArg___closed__3);
v___x_2032_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2032_, 0, v___x_2031_);
lean_ctor_set(v___x_2032_, 1, v___x_2030_);
lean_ctor_set(v___x_2032_, 2, v___x_2028_);
lean_ctor_set(v___x_2032_, 3, v___x_2028_);
lean_ctor_set_usize(v___x_2032_, 4, v___x_2027_);
return v___x_2032_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___redArg___closed__5(void){
_start:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2033_ = lean_box(1);
v___x_2034_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___redArg___closed__4);
v___x_2035_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___redArg___closed__1);
v___x_2036_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2035_);
lean_ctor_set(v___x_2036_, 1, v___x_2034_);
lean_ctor_set(v___x_2036_, 2, v___x_2033_);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___redArg(lean_object* v_msgData_2037_, lean_object* v___y_2038_){
_start:
{
lean_object* v___x_2040_; lean_object* v_env_2041_; lean_object* v___x_2042_; lean_object* v_scopes_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v_opts_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2040_ = lean_st_ref_get(v___y_2038_);
v_env_2041_ = lean_ctor_get(v___x_2040_, 0);
lean_inc_ref(v_env_2041_);
lean_dec(v___x_2040_);
v___x_2042_ = lean_st_ref_get(v___y_2038_);
v_scopes_2043_ = lean_ctor_get(v___x_2042_, 2);
lean_inc(v_scopes_2043_);
lean_dec(v___x_2042_);
v___x_2044_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2045_ = l_List_head_x21___redArg(v___x_2044_, v_scopes_2043_);
lean_dec(v_scopes_2043_);
v_opts_2046_ = lean_ctor_get(v___x_2045_, 1);
lean_inc_ref(v_opts_2046_);
lean_dec(v___x_2045_);
v___x_2047_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___redArg___closed__2);
v___x_2048_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___redArg___closed__5);
v___x_2049_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2049_, 0, v_env_2041_);
lean_ctor_set(v___x_2049_, 1, v___x_2047_);
lean_ctor_set(v___x_2049_, 2, v___x_2048_);
lean_ctor_set(v___x_2049_, 3, v_opts_2046_);
v___x_2050_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2050_, 0, v___x_2049_);
lean_ctor_set(v___x_2050_, 1, v_msgData_2037_);
v___x_2051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2050_);
return v___x_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___redArg___boxed(lean_object* v_msgData_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___redArg(v_msgData_2052_, v___y_2053_);
lean_dec(v___y_2053_);
return v_res_2055_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__20(lean_object* v_opts_2056_, lean_object* v_opt_2057_){
_start:
{
lean_object* v_name_2058_; lean_object* v_defValue_2059_; lean_object* v_map_2060_; lean_object* v___x_2061_; 
v_name_2058_ = lean_ctor_get(v_opt_2057_, 0);
v_defValue_2059_ = lean_ctor_get(v_opt_2057_, 1);
v_map_2060_ = lean_ctor_get(v_opts_2056_, 0);
v___x_2061_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2060_, v_name_2058_);
if (lean_obj_tag(v___x_2061_) == 0)
{
uint8_t v___x_2062_; 
v___x_2062_ = lean_unbox(v_defValue_2059_);
return v___x_2062_;
}
else
{
lean_object* v_val_2063_; 
v_val_2063_ = lean_ctor_get(v___x_2061_, 0);
lean_inc(v_val_2063_);
lean_dec_ref_known(v___x_2061_, 1);
if (lean_obj_tag(v_val_2063_) == 1)
{
uint8_t v_v_2064_; 
v_v_2064_ = lean_ctor_get_uint8(v_val_2063_, 0);
lean_dec_ref_known(v_val_2063_, 0);
return v_v_2064_;
}
else
{
uint8_t v___x_2065_; 
lean_dec(v_val_2063_);
v___x_2065_ = lean_unbox(v_defValue_2059_);
return v___x_2065_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__20___boxed(lean_object* v_opts_2066_, lean_object* v_opt_2067_){
_start:
{
uint8_t v_res_2068_; lean_object* v_r_2069_; 
v_res_2068_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__20(v_opts_2066_, v_opt_2067_);
lean_dec_ref(v_opt_2067_);
lean_dec_ref(v_opts_2066_);
v_r_2069_ = lean_box(v_res_2068_);
return v_r_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12(lean_object* v_ref_2071_, lean_object* v_msgData_2072_, uint8_t v_severity_2073_, uint8_t v_isSilent_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_){
_start:
{
lean_object* v___y_2079_; uint8_t v___y_2080_; uint8_t v___y_2081_; lean_object* v___y_2082_; lean_object* v___y_2083_; lean_object* v___y_2084_; lean_object* v___y_2085_; lean_object* v___y_2086_; uint8_t v___y_2143_; lean_object* v___y_2144_; uint8_t v___y_2145_; uint8_t v___y_2146_; lean_object* v___y_2147_; uint8_t v___y_2171_; uint8_t v___y_2172_; uint8_t v___y_2173_; lean_object* v___y_2174_; lean_object* v___y_2175_; uint8_t v___y_2179_; uint8_t v___y_2180_; uint8_t v___y_2181_; uint8_t v___x_2196_; uint8_t v___y_2198_; uint8_t v___y_2199_; uint8_t v___y_2200_; uint8_t v___y_2202_; uint8_t v___x_2214_; 
v___x_2196_ = 2;
v___x_2214_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2073_, v___x_2196_);
if (v___x_2214_ == 0)
{
v___y_2202_ = v___x_2214_;
goto v___jp_2201_;
}
else
{
uint8_t v___x_2215_; 
lean_inc_ref(v_msgData_2072_);
v___x_2215_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2072_);
v___y_2202_ = v___x_2215_;
goto v___jp_2201_;
}
v___jp_2078_:
{
lean_object* v___x_2087_; 
v___x_2087_ = l_Lean_Elab_Command_getScope___redArg(v___y_2086_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v_a_2088_; lean_object* v___x_2089_; 
v_a_2088_ = lean_ctor_get(v___x_2087_, 0);
lean_inc(v_a_2088_);
lean_dec_ref_known(v___x_2087_, 1);
v___x_2089_ = l_Lean_Elab_Command_getScope___redArg(v___y_2086_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2125_; 
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2092_ = v___x_2089_;
v_isShared_2093_ = v_isSharedCheck_2125_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2089_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2125_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2094_; lean_object* v_currNamespace_2095_; lean_object* v_openDecls_2096_; lean_object* v_env_2097_; lean_object* v_messages_2098_; lean_object* v_scopes_2099_; lean_object* v_usedQuotCtxts_2100_; lean_object* v_nextMacroScope_2101_; lean_object* v_maxRecDepth_2102_; lean_object* v_ngen_2103_; lean_object* v_auxDeclNGen_2104_; lean_object* v_infoState_2105_; lean_object* v_traceState_2106_; lean_object* v_snapshotTasks_2107_; lean_object* v_prevLinterStates_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2124_; 
v___x_2094_ = lean_st_ref_take(v___y_2086_);
v_currNamespace_2095_ = lean_ctor_get(v_a_2088_, 2);
lean_inc(v_currNamespace_2095_);
lean_dec(v_a_2088_);
v_openDecls_2096_ = lean_ctor_get(v_a_2090_, 3);
lean_inc(v_openDecls_2096_);
lean_dec(v_a_2090_);
v_env_2097_ = lean_ctor_get(v___x_2094_, 0);
v_messages_2098_ = lean_ctor_get(v___x_2094_, 1);
v_scopes_2099_ = lean_ctor_get(v___x_2094_, 2);
v_usedQuotCtxts_2100_ = lean_ctor_get(v___x_2094_, 3);
v_nextMacroScope_2101_ = lean_ctor_get(v___x_2094_, 4);
v_maxRecDepth_2102_ = lean_ctor_get(v___x_2094_, 5);
v_ngen_2103_ = lean_ctor_get(v___x_2094_, 6);
v_auxDeclNGen_2104_ = lean_ctor_get(v___x_2094_, 7);
v_infoState_2105_ = lean_ctor_get(v___x_2094_, 8);
v_traceState_2106_ = lean_ctor_get(v___x_2094_, 9);
v_snapshotTasks_2107_ = lean_ctor_get(v___x_2094_, 10);
v_prevLinterStates_2108_ = lean_ctor_get(v___x_2094_, 11);
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2110_ = v___x_2094_;
v_isShared_2111_ = v_isSharedCheck_2124_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_prevLinterStates_2108_);
lean_inc(v_snapshotTasks_2107_);
lean_inc(v_traceState_2106_);
lean_inc(v_infoState_2105_);
lean_inc(v_auxDeclNGen_2104_);
lean_inc(v_ngen_2103_);
lean_inc(v_maxRecDepth_2102_);
lean_inc(v_nextMacroScope_2101_);
lean_inc(v_usedQuotCtxts_2100_);
lean_inc(v_scopes_2099_);
lean_inc(v_messages_2098_);
lean_inc(v_env_2097_);
lean_dec(v___x_2094_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2124_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2117_; 
v___x_2112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2112_, 0, v_currNamespace_2095_);
lean_ctor_set(v___x_2112_, 1, v_openDecls_2096_);
v___x_2113_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2112_);
lean_ctor_set(v___x_2113_, 1, v___y_2085_);
lean_inc_ref(v___y_2079_);
lean_inc_ref(v___y_2083_);
v___x_2114_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2114_, 0, v___y_2083_);
lean_ctor_set(v___x_2114_, 1, v___y_2084_);
lean_ctor_set(v___x_2114_, 2, v___y_2082_);
lean_ctor_set(v___x_2114_, 3, v___y_2079_);
lean_ctor_set(v___x_2114_, 4, v___x_2113_);
lean_ctor_set_uint8(v___x_2114_, sizeof(void*)*5, v___y_2080_);
lean_ctor_set_uint8(v___x_2114_, sizeof(void*)*5 + 1, v___y_2081_);
lean_ctor_set_uint8(v___x_2114_, sizeof(void*)*5 + 2, v_isSilent_2074_);
v___x_2115_ = l_Lean_MessageLog_add(v___x_2114_, v_messages_2098_);
if (v_isShared_2111_ == 0)
{
lean_ctor_set(v___x_2110_, 1, v___x_2115_);
v___x_2117_ = v___x_2110_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_env_2097_);
lean_ctor_set(v_reuseFailAlloc_2123_, 1, v___x_2115_);
lean_ctor_set(v_reuseFailAlloc_2123_, 2, v_scopes_2099_);
lean_ctor_set(v_reuseFailAlloc_2123_, 3, v_usedQuotCtxts_2100_);
lean_ctor_set(v_reuseFailAlloc_2123_, 4, v_nextMacroScope_2101_);
lean_ctor_set(v_reuseFailAlloc_2123_, 5, v_maxRecDepth_2102_);
lean_ctor_set(v_reuseFailAlloc_2123_, 6, v_ngen_2103_);
lean_ctor_set(v_reuseFailAlloc_2123_, 7, v_auxDeclNGen_2104_);
lean_ctor_set(v_reuseFailAlloc_2123_, 8, v_infoState_2105_);
lean_ctor_set(v_reuseFailAlloc_2123_, 9, v_traceState_2106_);
lean_ctor_set(v_reuseFailAlloc_2123_, 10, v_snapshotTasks_2107_);
lean_ctor_set(v_reuseFailAlloc_2123_, 11, v_prevLinterStates_2108_);
v___x_2117_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2121_; 
v___x_2118_ = lean_st_ref_put(v___y_2086_, v___x_2117_);
v___x_2119_ = lean_box(0);
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 0, v___x_2119_);
v___x_2121_ = v___x_2092_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v___x_2119_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
}
}
else
{
lean_object* v_a_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2133_; 
lean_dec(v_a_2088_);
lean_dec_ref(v___y_2085_);
lean_dec_ref(v___y_2084_);
lean_dec(v___y_2082_);
v_a_2126_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2128_ = v___x_2089_;
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_a_2126_);
lean_dec(v___x_2089_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2131_; 
if (v_isShared_2129_ == 0)
{
v___x_2131_ = v___x_2128_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_a_2126_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
}
else
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2141_; 
lean_dec_ref(v___y_2085_);
lean_dec_ref(v___y_2084_);
lean_dec(v___y_2082_);
v_a_2134_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2136_ = v___x_2087_;
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2087_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2139_; 
if (v_isShared_2137_ == 0)
{
v___x_2139_ = v___x_2136_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_a_2134_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
}
v___jp_2142_:
{
lean_object* v_fileName_2148_; lean_object* v_fileMap_2149_; uint8_t v_suppressElabErrors_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2169_; 
v_fileName_2148_ = lean_ctor_get(v___y_2075_, 0);
v_fileMap_2149_ = lean_ctor_get(v___y_2075_, 1);
v_suppressElabErrors_2150_ = lean_ctor_get_uint8(v___y_2075_, sizeof(void*)*10);
v___x_2151_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2072_);
v___x_2152_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___redArg(v___x_2151_, v___y_2076_);
v_a_2153_ = lean_ctor_get(v___x_2152_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2155_ = v___x_2152_;
v_isShared_2156_ = v_isSharedCheck_2169_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v___x_2152_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2169_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
lean_inc_ref_n(v_fileMap_2149_, 2);
v___x_2157_ = l_Lean_FileMap_toPosition(v_fileMap_2149_, v___y_2144_);
lean_dec(v___y_2144_);
v___x_2158_ = l_Lean_FileMap_toPosition(v_fileMap_2149_, v___y_2147_);
lean_dec(v___y_2147_);
v___x_2159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2158_);
v___x_2160_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12___closed__0));
if (v_suppressElabErrors_2150_ == 0)
{
lean_del_object(v___x_2155_);
v___y_2079_ = v___x_2160_;
v___y_2080_ = v___y_2145_;
v___y_2081_ = v___y_2146_;
v___y_2082_ = v___x_2159_;
v___y_2083_ = v_fileName_2148_;
v___y_2084_ = v___x_2157_;
v___y_2085_ = v_a_2153_;
v___y_2086_ = v___y_2076_;
goto v___jp_2078_;
}
else
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___f_2163_; uint8_t v___x_2164_; 
v___x_2161_ = lean_box(v___y_2143_);
v___x_2162_ = lean_box(v_suppressElabErrors_2150_);
v___f_2163_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2163_, 0, v___x_2161_);
lean_closure_set(v___f_2163_, 1, v___x_2162_);
lean_inc(v_a_2153_);
v___x_2164_ = l_Lean_MessageData_hasTag(v___f_2163_, v_a_2153_);
if (v___x_2164_ == 0)
{
lean_object* v___x_2165_; lean_object* v___x_2167_; 
lean_dec_ref_known(v___x_2159_, 1);
lean_dec_ref(v___x_2157_);
lean_dec(v_a_2153_);
v___x_2165_ = lean_box(0);
if (v_isShared_2156_ == 0)
{
lean_ctor_set(v___x_2155_, 0, v___x_2165_);
v___x_2167_ = v___x_2155_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v___x_2165_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
else
{
lean_del_object(v___x_2155_);
v___y_2079_ = v___x_2160_;
v___y_2080_ = v___y_2145_;
v___y_2081_ = v___y_2146_;
v___y_2082_ = v___x_2159_;
v___y_2083_ = v_fileName_2148_;
v___y_2084_ = v___x_2157_;
v___y_2085_ = v_a_2153_;
v___y_2086_ = v___y_2076_;
goto v___jp_2078_;
}
}
}
}
v___jp_2170_:
{
lean_object* v___x_2176_; 
v___x_2176_ = l_Lean_Syntax_getTailPos_x3f(v___y_2174_, v___y_2172_);
lean_dec(v___y_2174_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_inc(v___y_2175_);
v___y_2143_ = v___y_2171_;
v___y_2144_ = v___y_2175_;
v___y_2145_ = v___y_2172_;
v___y_2146_ = v___y_2173_;
v___y_2147_ = v___y_2175_;
goto v___jp_2142_;
}
else
{
lean_object* v_val_2177_; 
v_val_2177_ = lean_ctor_get(v___x_2176_, 0);
lean_inc(v_val_2177_);
lean_dec_ref_known(v___x_2176_, 1);
v___y_2143_ = v___y_2171_;
v___y_2144_ = v___y_2175_;
v___y_2145_ = v___y_2172_;
v___y_2146_ = v___y_2173_;
v___y_2147_ = v_val_2177_;
goto v___jp_2142_;
}
}
v___jp_2178_:
{
lean_object* v___x_2182_; 
v___x_2182_ = l_Lean_Elab_Command_getRef___redArg(v___y_2075_);
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_object* v_a_2183_; lean_object* v_ref_2184_; lean_object* v___x_2185_; 
v_a_2183_ = lean_ctor_get(v___x_2182_, 0);
lean_inc(v_a_2183_);
lean_dec_ref_known(v___x_2182_, 1);
v_ref_2184_ = l_Lean_replaceRef(v_ref_2071_, v_a_2183_);
lean_dec(v_a_2183_);
v___x_2185_ = l_Lean_Syntax_getPos_x3f(v_ref_2184_, v___y_2180_);
if (lean_obj_tag(v___x_2185_) == 0)
{
lean_object* v___x_2186_; 
v___x_2186_ = lean_unsigned_to_nat(0u);
v___y_2171_ = v___y_2179_;
v___y_2172_ = v___y_2180_;
v___y_2173_ = v___y_2181_;
v___y_2174_ = v_ref_2184_;
v___y_2175_ = v___x_2186_;
goto v___jp_2170_;
}
else
{
lean_object* v_val_2187_; 
v_val_2187_ = lean_ctor_get(v___x_2185_, 0);
lean_inc(v_val_2187_);
lean_dec_ref_known(v___x_2185_, 1);
v___y_2171_ = v___y_2179_;
v___y_2172_ = v___y_2180_;
v___y_2173_ = v___y_2181_;
v___y_2174_ = v_ref_2184_;
v___y_2175_ = v_val_2187_;
goto v___jp_2170_;
}
}
else
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2195_; 
lean_dec_ref(v_msgData_2072_);
v_a_2188_ = lean_ctor_get(v___x_2182_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2182_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2190_ = v___x_2182_;
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2182_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2193_; 
if (v_isShared_2191_ == 0)
{
v___x_2193_ = v___x_2190_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_a_2188_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
}
}
v___jp_2197_:
{
if (v___y_2200_ == 0)
{
v___y_2179_ = v___y_2198_;
v___y_2180_ = v___y_2199_;
v___y_2181_ = v_severity_2073_;
goto v___jp_2178_;
}
else
{
v___y_2179_ = v___y_2198_;
v___y_2180_ = v___y_2199_;
v___y_2181_ = v___x_2196_;
goto v___jp_2178_;
}
}
v___jp_2201_:
{
if (v___y_2202_ == 0)
{
lean_object* v___x_2203_; lean_object* v_scopes_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v_opts_2207_; uint8_t v___x_2208_; uint8_t v___x_2209_; 
v___x_2203_ = lean_st_ref_get(v___y_2076_);
v_scopes_2204_ = lean_ctor_get(v___x_2203_, 2);
lean_inc(v_scopes_2204_);
lean_dec(v___x_2203_);
v___x_2205_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2206_ = l_List_head_x21___redArg(v___x_2205_, v_scopes_2204_);
lean_dec(v_scopes_2204_);
v_opts_2207_ = lean_ctor_get(v___x_2206_, 1);
lean_inc_ref(v_opts_2207_);
lean_dec(v___x_2206_);
v___x_2208_ = 1;
v___x_2209_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2073_, v___x_2208_);
if (v___x_2209_ == 0)
{
lean_dec_ref(v_opts_2207_);
v___y_2198_ = v___y_2202_;
v___y_2199_ = v___y_2202_;
v___y_2200_ = v___x_2209_;
goto v___jp_2197_;
}
else
{
lean_object* v___x_2210_; uint8_t v___x_2211_; 
v___x_2210_ = l_Lean_warningAsError;
v___x_2211_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__20(v_opts_2207_, v___x_2210_);
lean_dec_ref(v_opts_2207_);
v___y_2198_ = v___y_2202_;
v___y_2199_ = v___y_2202_;
v___y_2200_ = v___x_2211_;
goto v___jp_2197_;
}
}
else
{
lean_object* v___x_2212_; lean_object* v___x_2213_; 
lean_dec_ref(v_msgData_2072_);
v___x_2212_ = lean_box(0);
v___x_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2212_);
return v___x_2213_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12___boxed(lean_object* v_ref_2216_, lean_object* v_msgData_2217_, lean_object* v_severity_2218_, lean_object* v_isSilent_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_){
_start:
{
uint8_t v_severity_boxed_2223_; uint8_t v_isSilent_boxed_2224_; lean_object* v_res_2225_; 
v_severity_boxed_2223_ = lean_unbox(v_severity_2218_);
v_isSilent_boxed_2224_ = lean_unbox(v_isSilent_2219_);
v_res_2225_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12(v_ref_2216_, v_msgData_2217_, v_severity_boxed_2223_, v_isSilent_boxed_2224_, v___y_2220_, v___y_2221_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec(v_ref_2216_);
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5(lean_object* v_ref_2226_, lean_object* v_msgData_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_){
_start:
{
uint8_t v___x_2231_; uint8_t v___x_2232_; lean_object* v___x_2233_; 
v___x_2231_ = 1;
v___x_2232_ = 0;
v___x_2233_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12(v_ref_2226_, v_msgData_2227_, v___x_2231_, v___x_2232_, v___y_2228_, v___y_2229_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5___boxed(lean_object* v_ref_2234_, lean_object* v_msgData_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_){
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5(v_ref_2234_, v_msgData_2235_, v___y_2236_, v___y_2237_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
lean_dec(v_ref_2234_);
return v_res_2239_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2241_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__0));
v___x_2242_ = l_Lean_stringToMessageData(v___x_2241_);
return v___x_2242_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__3(void){
_start:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2244_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__2));
v___x_2245_ = l_Lean_stringToMessageData(v___x_2244_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3(lean_object* v_linterOption_2246_, lean_object* v_stx_2247_, lean_object* v_msg_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_){
_start:
{
lean_object* v_name_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2270_; 
v_name_2252_ = lean_ctor_get(v_linterOption_2246_, 0);
v_isSharedCheck_2270_ = !lean_is_exclusive(v_linterOption_2246_);
if (v_isSharedCheck_2270_ == 0)
{
lean_object* v_unused_2271_; 
v_unused_2271_ = lean_ctor_get(v_linterOption_2246_, 1);
lean_dec(v_unused_2271_);
v___x_2254_ = v_linterOption_2246_;
v_isShared_2255_ = v_isSharedCheck_2270_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_name_2252_);
lean_dec(v_linterOption_2246_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2270_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2259_; 
v___x_2256_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__1);
lean_inc(v_name_2252_);
v___x_2257_ = l_Lean_MessageData_ofName(v_name_2252_);
if (v_isShared_2255_ == 0)
{
lean_ctor_set_tag(v___x_2254_, 7);
lean_ctor_set(v___x_2254_, 1, v___x_2257_);
lean_ctor_set(v___x_2254_, 0, v___x_2256_);
v___x_2259_ = v___x_2254_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v___x_2256_);
lean_ctor_set(v_reuseFailAlloc_2269_, 1, v___x_2257_);
v___x_2259_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v_disable_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2260_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__3);
v___x_2261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2259_);
lean_ctor_set(v___x_2261_, 1, v___x_2260_);
v_disable_2262_ = l_Lean_MessageData_note(v___x_2261_);
v___x_2263_ = l_Lean_Linter_linterMessageTag;
v___x_2264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2264_, 0, v_msg_2248_);
lean_ctor_set(v___x_2264_, 1, v_disable_2262_);
v___x_2265_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2263_);
lean_ctor_set(v___x_2265_, 1, v___x_2264_);
v___x_2266_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2266_, 0, v_name_2252_);
lean_ctor_set(v___x_2266_, 1, v___x_2265_);
lean_inc(v_stx_2247_);
v___x_2267_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_2267_, 0, v_stx_2247_);
lean_ctor_set(v___x_2267_, 1, v___x_2266_);
v___x_2268_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5(v_stx_2247_, v___x_2267_, v___y_2249_, v___y_2250_);
lean_dec(v_stx_2247_);
return v___x_2268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___boxed(lean_object* v_linterOption_2272_, lean_object* v_stx_2273_, lean_object* v_msg_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3(v_linterOption_2272_, v_stx_2273_, v_msg_2274_, v___y_2275_, v___y_2276_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2(lean_object* v_linterOption_2279_, lean_object* v_stx_2280_, lean_object* v_msg_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
lean_object* v___x_2285_; lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2296_; 
v___x_2285_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1(v___y_2282_, v___y_2283_);
v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2288_ = v___x_2285_;
v_isShared_2289_ = v_isSharedCheck_2296_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v___x_2285_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2296_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
uint8_t v___x_2290_; 
v___x_2290_ = l_Lean_Linter_getLinterValue(v_linterOption_2279_, v_a_2286_);
lean_dec(v_a_2286_);
if (v___x_2290_ == 0)
{
lean_object* v___x_2291_; lean_object* v___x_2293_; 
lean_dec_ref(v_msg_2281_);
lean_dec(v_stx_2280_);
lean_dec_ref(v_linterOption_2279_);
v___x_2291_ = lean_box(0);
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 0, v___x_2291_);
v___x_2293_ = v___x_2288_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v___x_2291_);
v___x_2293_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
return v___x_2293_;
}
}
else
{
lean_object* v___x_2295_; 
lean_del_object(v___x_2288_);
v___x_2295_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3(v_linterOption_2279_, v_stx_2280_, v_msg_2281_, v___y_2282_, v___y_2283_);
return v___x_2295_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2___boxed(lean_object* v_linterOption_2297_, lean_object* v_stx_2298_, lean_object* v_msg_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2(v_linterOption_2297_, v_stx_2298_, v_msg_2299_, v___y_2300_, v___y_2301_);
lean_dec(v___y_2301_);
lean_dec_ref(v___y_2300_);
return v_res_2303_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___closed__2(void){
_start:
{
lean_object* v___x_2307_; lean_object* v___x_2308_; 
v___x_2307_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___closed__1));
v___x_2308_ = l_Lean_MessageData_ofFormat(v___x_2307_);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6(lean_object* v_as_2309_, size_t v_sz_2310_, size_t v_i_2311_, lean_object* v_b_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
lean_object* v_a_2317_; uint8_t v___x_2321_; 
v___x_2321_ = lean_usize_dec_lt(v_i_2311_, v_sz_2310_);
if (v___x_2321_ == 0)
{
lean_object* v___x_2322_; 
v___x_2322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2322_, 0, v_b_2312_);
return v___x_2322_;
}
else
{
lean_object* v_a_2323_; lean_object* v_fst_2324_; lean_object* v_snd_2325_; lean_object* v_start_2326_; lean_object* v_stop_2327_; lean_object* v_start_2328_; lean_object* v_stop_2329_; lean_object* v___x_2330_; uint8_t v___y_2332_; uint8_t v___x_2343_; 
v_a_2323_ = lean_array_uget_borrowed(v_as_2309_, v_i_2311_);
v_fst_2324_ = lean_ctor_get(v_a_2323_, 0);
v_snd_2325_ = lean_ctor_get(v_a_2323_, 1);
v_start_2326_ = lean_ctor_get(v_b_2312_, 0);
v_stop_2327_ = lean_ctor_get(v_b_2312_, 1);
v_start_2328_ = lean_ctor_get(v_fst_2324_, 0);
v_stop_2329_ = lean_ctor_get(v_fst_2324_, 1);
v___x_2330_ = l_Lean_Linter_Extra_linter_extra_unreachableTactic;
v___x_2343_ = lean_nat_dec_le(v_start_2326_, v_start_2328_);
if (v___x_2343_ == 0)
{
v___y_2332_ = v___x_2343_;
goto v___jp_2331_;
}
else
{
uint8_t v___x_2344_; 
v___x_2344_ = lean_nat_dec_le(v_stop_2329_, v_stop_2327_);
v___y_2332_ = v___x_2344_;
goto v___jp_2331_;
}
v___jp_2331_:
{
if (v___y_2332_ == 0)
{
lean_object* v___x_2333_; lean_object* v___x_2334_; 
lean_dec_ref(v_b_2312_);
v___x_2333_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___closed__2);
lean_inc(v_snd_2325_);
v___x_2334_ = l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2(v___x_2330_, v_snd_2325_, v___x_2333_, v___y_2313_, v___y_2314_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_dec_ref_known(v___x_2334_, 1);
lean_inc(v_fst_2324_);
v_a_2317_ = v_fst_2324_;
goto v___jp_2316_;
}
else
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2342_; 
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2337_ = v___x_2334_;
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2334_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2340_; 
if (v_isShared_2338_ == 0)
{
v___x_2340_ = v___x_2337_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_a_2335_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
else
{
v_a_2317_ = v_b_2312_;
goto v___jp_2316_;
}
}
}
v___jp_2316_:
{
size_t v___x_2318_; size_t v___x_2319_; 
v___x_2318_ = ((size_t)1ULL);
v___x_2319_ = lean_usize_add(v_i_2311_, v___x_2318_);
v_i_2311_ = v___x_2319_;
v_b_2312_ = v_a_2317_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___boxed(lean_object* v_as_2345_, lean_object* v_sz_2346_, lean_object* v_i_2347_, lean_object* v_b_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
size_t v_sz_boxed_2352_; size_t v_i_boxed_2353_; lean_object* v_res_2354_; 
v_sz_boxed_2352_ = lean_unbox_usize(v_sz_2346_);
lean_dec(v_sz_2346_);
v_i_boxed_2353_ = lean_unbox_usize(v_i_2347_);
lean_dec(v_i_2347_);
v_res_2354_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6(v_as_2345_, v_sz_boxed_2352_, v_i_boxed_2353_, v_b_2348_, v___y_2349_, v___y_2350_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec_ref(v_as_2345_);
return v_res_2354_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__4(void){
_start:
{
lean_object* v_cellCount_2361_; lean_object* v___x_2362_; 
v_cellCount_2361_ = lean_unsigned_to_nat(16u);
v___x_2362_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_2361_);
return v___x_2362_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__5(void){
_start:
{
lean_object* v_cellCount_2363_; lean_object* v___x_2364_; 
v_cellCount_2363_ = lean_unsigned_to_nat(16u);
v___x_2364_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_2363_);
return v___x_2364_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__6(void){
_start:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
v___x_2365_ = lean_obj_once(&l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__5, &l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__5_once, _init_l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__5);
v___x_2366_ = lean_obj_once(&l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__4, &l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__4_once, _init_l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__4);
v___x_2367_ = lean_unsigned_to_nat(0u);
v___x_2368_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2367_);
lean_ctor_set(v___x_2368_, 1, v___x_2366_);
lean_ctor_set(v___x_2368_, 2, v___x_2365_);
return v___x_2368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0(lean_object* v_stx_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_){
_start:
{
lean_object* v___y_2374_; lean_object* v___y_2375_; lean_object* v___y_2397_; lean_object* v___y_2398_; lean_object* v___y_2399_; lean_object* v___y_2400_; lean_object* v___y_2401_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___y_2406_; lean_object* v___y_2407_; lean_object* v___y_2408_; lean_object* v___y_2411_; lean_object* v___y_2412_; lean_object* v___y_2413_; lean_object* v___x_2437_; lean_object* v_a_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2494_; 
v___x_2437_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1(v___y_2370_, v___y_2371_);
v_a_2438_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2440_ = v___x_2437_;
v_isShared_2441_ = v_isSharedCheck_2494_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_a_2438_);
lean_dec(v___x_2437_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2494_;
goto v_resetjp_2439_;
}
v___jp_2373_:
{
size_t v_sz_2376_; size_t v___x_2377_; lean_object* v___x_2378_; 
v_sz_2376_ = lean_array_size(v___y_2375_);
v___x_2377_ = ((size_t)0ULL);
v___x_2378_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6(v___y_2375_, v_sz_2376_, v___x_2377_, v___y_2374_, v___y_2370_, v___y_2371_);
lean_dec_ref(v___y_2375_);
if (lean_obj_tag(v___x_2378_) == 0)
{
lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2386_; 
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2386_ == 0)
{
lean_object* v_unused_2387_; 
v_unused_2387_ = lean_ctor_get(v___x_2378_, 0);
lean_dec(v_unused_2387_);
v___x_2380_ = v___x_2378_;
v_isShared_2381_ = v_isSharedCheck_2386_;
goto v_resetjp_2379_;
}
else
{
lean_dec(v___x_2378_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2386_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v___x_2382_; lean_object* v___x_2384_; 
v___x_2382_ = lean_box(0);
if (v_isShared_2381_ == 0)
{
lean_ctor_set(v___x_2380_, 0, v___x_2382_);
v___x_2384_ = v___x_2380_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v___x_2382_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
return v___x_2384_;
}
}
}
else
{
lean_object* v_a_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2395_; 
v_a_2388_ = lean_ctor_get(v___x_2378_, 0);
v_isSharedCheck_2395_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2390_ = v___x_2378_;
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_a_2388_);
lean_dec(v___x_2378_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2393_; 
if (v_isShared_2391_ == 0)
{
v___x_2393_ = v___x_2390_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_a_2388_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
}
}
v___jp_2396_:
{
lean_object* v___x_2402_; 
v___x_2402_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg(v___y_2397_, v___y_2400_, v___y_2398_, v___y_2401_);
lean_dec(v___y_2401_);
lean_dec(v___y_2397_);
v___y_2374_ = v___y_2399_;
v___y_2375_ = v___x_2402_;
goto v___jp_2373_;
}
v___jp_2403_:
{
uint8_t v___x_2409_; 
v___x_2409_ = lean_nat_dec_le(v___y_2408_, v___y_2404_);
if (v___x_2409_ == 0)
{
lean_dec(v___y_2404_);
lean_inc(v___y_2408_);
v___y_2397_ = v___y_2405_;
v___y_2398_ = v___y_2408_;
v___y_2399_ = v___y_2406_;
v___y_2400_ = v___y_2407_;
v___y_2401_ = v___y_2408_;
goto v___jp_2396_;
}
else
{
v___y_2397_ = v___y_2405_;
v___y_2398_ = v___y_2408_;
v___y_2399_ = v___y_2406_;
v___y_2400_ = v___y_2407_;
v___y_2401_ = v___y_2404_;
goto v___jp_2396_;
}
}
v___jp_2410_:
{
if (lean_obj_tag(v___y_2413_) == 0)
{
lean_object* v___x_2414_; lean_object* v_size_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; uint8_t v___x_2420_; 
lean_dec_ref_known(v___y_2413_, 1);
v___x_2414_ = lean_st_ref_get(v___y_2412_);
lean_dec(v___y_2412_);
v_size_2415_ = lean_ctor_get(v___x_2414_, 0);
lean_inc(v_size_2415_);
v___x_2416_ = lean_mk_empty_array_with_capacity(v_size_2415_);
lean_dec(v_size_2415_);
v___x_2417_ = l_Std_DHashMap_Raw_foldM___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5(v___x_2416_, v___x_2414_);
lean_dec(v___x_2414_);
lean_inc_n(v___y_2411_, 2);
v___x_2418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2418_, 0, v___y_2411_);
lean_ctor_set(v___x_2418_, 1, v___y_2411_);
v___x_2419_ = lean_array_get_size(v___x_2417_);
v___x_2420_ = lean_nat_dec_eq(v___x_2419_, v___y_2411_);
if (v___x_2420_ == 0)
{
lean_object* v___x_2421_; lean_object* v___x_2422_; uint8_t v___x_2423_; 
v___x_2421_ = lean_unsigned_to_nat(1u);
v___x_2422_ = lean_nat_sub(v___x_2419_, v___x_2421_);
v___x_2423_ = lean_nat_dec_le(v___y_2411_, v___x_2422_);
if (v___x_2423_ == 0)
{
lean_dec(v___y_2411_);
lean_inc(v___x_2422_);
v___y_2404_ = v___x_2422_;
v___y_2405_ = v___x_2419_;
v___y_2406_ = v___x_2418_;
v___y_2407_ = v___x_2417_;
v___y_2408_ = v___x_2422_;
goto v___jp_2403_;
}
else
{
v___y_2404_ = v___x_2422_;
v___y_2405_ = v___x_2419_;
v___y_2406_ = v___x_2418_;
v___y_2407_ = v___x_2417_;
v___y_2408_ = v___y_2411_;
goto v___jp_2403_;
}
}
else
{
lean_dec(v___y_2411_);
v___y_2374_ = v___x_2418_;
v___y_2375_ = v___x_2417_;
goto v___jp_2373_;
}
}
else
{
lean_object* v_a_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2436_; 
lean_dec(v___y_2412_);
lean_dec(v___y_2411_);
v_a_2424_ = lean_ctor_get(v___y_2413_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___y_2413_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2426_ = v___y_2413_;
v_isShared_2427_ = v_isSharedCheck_2436_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_a_2424_);
lean_dec(v___y_2413_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2436_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v_ref_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2434_; 
v_ref_2428_ = lean_ctor_get(v___y_2370_, 7);
v___x_2429_ = lean_io_error_to_string(v_a_2424_);
v___x_2430_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2430_, 0, v___x_2429_);
v___x_2431_ = l_Lean_MessageData_ofFormat(v___x_2430_);
lean_inc(v_ref_2428_);
v___x_2432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2432_, 0, v_ref_2428_);
lean_ctor_set(v___x_2432_, 1, v___x_2431_);
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 0, v___x_2432_);
v___x_2434_ = v___x_2426_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v___x_2432_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
}
}
v_resetjp_2439_:
{
lean_object* v___x_2442_; uint8_t v___y_2444_; lean_object* v___x_2490_; uint8_t v___x_2491_; 
v___x_2442_ = lean_st_ref_get(v___y_2371_);
v___x_2490_ = l_Lean_Linter_Extra_linter_extra_unreachableTactic;
v___x_2491_ = l_Lean_Linter_getLinterValue(v___x_2490_, v_a_2438_);
lean_dec(v_a_2438_);
if (v___x_2491_ == 0)
{
lean_dec(v___x_2442_);
v___y_2444_ = v___x_2491_;
goto v___jp_2443_;
}
else
{
lean_object* v_infoState_2492_; uint8_t v_enabled_2493_; 
v_infoState_2492_ = lean_ctor_get(v___x_2442_, 8);
lean_inc_ref(v_infoState_2492_);
lean_dec(v___x_2442_);
v_enabled_2493_ = lean_ctor_get_uint8(v_infoState_2492_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2492_);
v___y_2444_ = v_enabled_2493_;
goto v___jp_2443_;
}
v___jp_2443_:
{
if (v___y_2444_ == 0)
{
lean_object* v___x_2445_; lean_object* v___x_2447_; 
lean_dec(v_stx_2369_);
v___x_2445_ = lean_box(0);
if (v_isShared_2441_ == 0)
{
lean_ctor_set(v___x_2440_, 0, v___x_2445_);
v___x_2447_ = v___x_2440_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v___x_2445_);
v___x_2447_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
return v___x_2447_;
}
}
else
{
lean_object* v___x_2449_; lean_object* v_messages_2450_; uint8_t v___x_2451_; 
v___x_2449_ = lean_st_ref_get(v___y_2371_);
v_messages_2450_ = lean_ctor_get(v___x_2449_, 1);
lean_inc_ref(v_messages_2450_);
lean_dec(v___x_2449_);
v___x_2451_ = l_Lean_MessageLog_hasErrors(v_messages_2450_);
lean_dec_ref(v_messages_2450_);
if (v___x_2451_ == 0)
{
lean_object* v___x_2452_; lean_object* v_env_2453_; lean_object* v___x_2454_; lean_object* v_ext_2455_; lean_object* v_toEnvExtension_2456_; lean_object* v_asyncMode_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v_categories_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2452_ = lean_st_ref_get(v___y_2371_);
v_env_2453_ = lean_ctor_get(v___x_2452_, 0);
lean_inc_ref(v_env_2453_);
lean_dec(v___x_2452_);
v___x_2454_ = l_Lean_Parser_parserExtension;
v_ext_2455_ = lean_ctor_get(v___x_2454_, 1);
v_toEnvExtension_2456_ = lean_ctor_get(v_ext_2455_, 0);
v_asyncMode_2457_ = lean_ctor_get(v_toEnvExtension_2456_, 2);
v___x_2458_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2459_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2458_, v___x_2454_, v_env_2453_, v_asyncMode_2457_);
v_categories_2460_ = lean_ctor_get(v___x_2459_, 2);
lean_inc_ref(v_categories_2460_);
lean_dec(v___x_2459_);
v___x_2461_ = ((lean_object*)(l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__1));
v___x_2462_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3___redArg(v_categories_2460_, v___x_2461_);
if (lean_obj_tag(v___x_2462_) == 0)
{
lean_object* v___x_2463_; lean_object* v___x_2465_; 
lean_dec_ref(v_categories_2460_);
lean_dec(v_stx_2369_);
v___x_2463_ = lean_box(0);
if (v_isShared_2441_ == 0)
{
lean_ctor_set(v___x_2440_, 0, v___x_2463_);
v___x_2465_ = v___x_2440_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v___x_2463_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
else
{
lean_object* v_val_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; 
v_val_2467_ = lean_ctor_get(v___x_2462_, 0);
lean_inc(v_val_2467_);
lean_dec_ref_known(v___x_2462_, 1);
v___x_2468_ = ((lean_object*)(l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__3));
v___x_2469_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3___redArg(v_categories_2460_, v___x_2468_);
lean_dec_ref(v_categories_2460_);
if (lean_obj_tag(v___x_2469_) == 0)
{
lean_object* v___x_2470_; lean_object* v___x_2472_; 
lean_dec(v_val_2467_);
lean_dec(v_stx_2369_);
v___x_2470_ = lean_box(0);
if (v_isShared_2441_ == 0)
{
lean_ctor_set(v___x_2440_, 0, v___x_2470_);
v___x_2472_ = v___x_2440_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v___x_2470_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
else
{
lean_object* v_val_2474_; lean_object* v___x_2475_; lean_object* v_a_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v_kinds_2482_; lean_object* v_kinds_2483_; lean_object* v___x_2484_; 
lean_del_object(v___x_2440_);
v_val_2474_ = lean_ctor_get(v___x_2469_, 0);
lean_inc(v_val_2474_);
lean_dec_ref_known(v___x_2469_, 1);
v___x_2475_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4___redArg(v___y_2371_);
v_a_2476_ = lean_ctor_get(v___x_2475_, 0);
lean_inc(v_a_2476_);
lean_dec_ref(v___x_2475_);
v___x_2477_ = lean_unsigned_to_nat(0u);
v___x_2478_ = lean_obj_once(&l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__6, &l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__6_once, _init_l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__6);
v___x_2479_ = lean_st_mk_ref(v___x_2478_);
v___x_2480_ = l_Lean_Linter_Extra_UnreachableTactic_ignoreTacticKindsRef;
v___x_2481_ = lean_st_ref_get(v___x_2480_);
v_kinds_2482_ = lean_ctor_get(v_val_2467_, 1);
lean_inc_ref(v_kinds_2482_);
lean_dec(v_val_2467_);
v_kinds_2483_ = lean_ctor_get(v_val_2474_, 1);
lean_inc_ref(v_kinds_2483_);
lean_dec(v_val_2474_);
v___x_2484_ = l_Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9(v_kinds_2482_, v_kinds_2483_, v___y_2444_, v___x_2481_, v_stx_2369_, v___x_2479_);
lean_dec(v___x_2481_);
lean_dec_ref(v_kinds_2483_);
lean_dec_ref(v_kinds_2482_);
if (lean_obj_tag(v___x_2484_) == 0)
{
lean_object* v___x_2485_; 
lean_dec_ref_known(v___x_2484_, 1);
v___x_2485_ = l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList(v_a_2476_, v___x_2479_);
v___y_2411_ = v___x_2477_;
v___y_2412_ = v___x_2479_;
v___y_2413_ = v___x_2485_;
goto v___jp_2410_;
}
else
{
lean_dec(v_a_2476_);
v___y_2411_ = v___x_2477_;
v___y_2412_ = v___x_2479_;
v___y_2413_ = v___x_2484_;
goto v___jp_2410_;
}
}
}
}
else
{
lean_object* v___x_2486_; lean_object* v___x_2488_; 
lean_dec(v_stx_2369_);
v___x_2486_ = lean_box(0);
if (v_isShared_2441_ == 0)
{
lean_ctor_set(v___x_2440_, 0, v___x_2486_);
v___x_2488_ = v___x_2440_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v___x_2486_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___boxed(lean_object* v_stx_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_){
_start:
{
lean_object* v_res_2499_; 
v_res_2499_ = l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0(v_stx_2495_, v___y_2496_, v___y_2497_);
lean_dec(v___y_2497_);
lean_dec_ref(v___y_2496_);
return v_res_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1(lean_object* v_o_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_){
_start:
{
lean_object* v___x_2519_; 
v___x_2519_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1___redArg(v_o_2515_, v___y_2517_);
return v___x_2519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1___boxed(lean_object* v_o_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_){
_start:
{
lean_object* v_res_2524_; 
v_res_2524_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1(v_o_2520_, v___y_2521_, v___y_2522_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3(lean_object* v_00_u03b2_2525_, lean_object* v_x_2526_, lean_object* v_x_2527_){
_start:
{
lean_object* v___x_2528_; 
v___x_2528_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3___redArg(v_x_2526_, v_x_2527_);
return v___x_2528_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3___boxed(lean_object* v_00_u03b2_2529_, lean_object* v_x_2530_, lean_object* v_x_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3(v_00_u03b2_2529_, v_x_2530_, v_x_2531_);
lean_dec(v_x_2531_);
lean_dec_ref(v_x_2530_);
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7(lean_object* v_n_2533_, lean_object* v_as_2534_, lean_object* v_lo_2535_, lean_object* v_hi_2536_, lean_object* v_w_2537_, lean_object* v_hlo_2538_, lean_object* v_hhi_2539_){
_start:
{
lean_object* v___x_2540_; 
v___x_2540_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg(v_n_2533_, v_as_2534_, v_lo_2535_, v_hi_2536_);
return v___x_2540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___boxed(lean_object* v_n_2541_, lean_object* v_as_2542_, lean_object* v_lo_2543_, lean_object* v_hi_2544_, lean_object* v_w_2545_, lean_object* v_hlo_2546_, lean_object* v_hhi_2547_){
_start:
{
lean_object* v_res_2548_; 
v_res_2548_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7(v_n_2541_, v_as_2542_, v_lo_2543_, v_hi_2544_, v_w_2545_, v_hlo_2546_, v_hhi_2547_);
lean_dec(v_hi_2544_);
lean_dec(v_n_2541_);
return v_res_2548_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8(lean_object* v_00_u03b2_2549_, lean_object* v_x_2550_, lean_object* v_x_2551_){
_start:
{
uint8_t v___x_2552_; 
v___x_2552_ = l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8___redArg(v_x_2550_, v_x_2551_);
return v___x_2552_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8___boxed(lean_object* v_00_u03b2_2553_, lean_object* v_x_2554_, lean_object* v_x_2555_){
_start:
{
uint8_t v_res_2556_; lean_object* v_r_2557_; 
v_res_2556_ = l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8(v_00_u03b2_2553_, v_x_2554_, v_x_2555_);
lean_dec(v_x_2555_);
lean_dec_ref(v_x_2554_);
v_r_2557_ = lean_box(v_res_2556_);
return v_r_2557_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5(lean_object* v_00_u03b2_2558_, lean_object* v_x_2559_, size_t v_x_2560_, lean_object* v_x_2561_){
_start:
{
lean_object* v___x_2562_; 
v___x_2562_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5___redArg(v_x_2559_, v_x_2560_, v_x_2561_);
return v___x_2562_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5___boxed(lean_object* v_00_u03b2_2563_, lean_object* v_x_2564_, lean_object* v_x_2565_, lean_object* v_x_2566_){
_start:
{
size_t v_x_13840__boxed_2567_; lean_object* v_res_2568_; 
v_x_13840__boxed_2567_ = lean_unbox_usize(v_x_2565_);
lean_dec(v_x_2565_);
v_res_2568_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5(v_00_u03b2_2563_, v_x_2564_, v_x_13840__boxed_2567_, v_x_2566_);
lean_dec(v_x_2566_);
lean_dec_ref(v_x_2564_);
return v_res_2568_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7_spec__11(lean_object* v_n_2569_, lean_object* v_lo_2570_, lean_object* v_hi_2571_, lean_object* v_hhi_2572_, lean_object* v_pivot_2573_, lean_object* v_as_2574_, lean_object* v_i_2575_, lean_object* v_k_2576_, lean_object* v_ilo_2577_, lean_object* v_ik_2578_, lean_object* v_w_2579_){
_start:
{
lean_object* v___x_2580_; 
v___x_2580_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7_spec__11___redArg(v_hi_2571_, v_pivot_2573_, v_as_2574_, v_i_2575_, v_k_2576_);
return v___x_2580_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7_spec__11___boxed(lean_object* v_n_2581_, lean_object* v_lo_2582_, lean_object* v_hi_2583_, lean_object* v_hhi_2584_, lean_object* v_pivot_2585_, lean_object* v_as_2586_, lean_object* v_i_2587_, lean_object* v_k_2588_, lean_object* v_ilo_2589_, lean_object* v_ik_2590_, lean_object* v_w_2591_){
_start:
{
lean_object* v_res_2592_; 
v_res_2592_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7_spec__11(v_n_2581_, v_lo_2582_, v_hi_2583_, v_hhi_2584_, v_pivot_2585_, v_as_2586_, v_i_2587_, v_k_2588_, v_ilo_2589_, v_ik_2590_, v_w_2591_);
lean_dec(v_hi_2583_);
lean_dec(v_lo_2582_);
lean_dec(v_n_2581_);
return v_res_2592_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8_spec__13(lean_object* v_00_u03b2_2593_, lean_object* v_x_2594_, size_t v_x_2595_, lean_object* v_x_2596_){
_start:
{
uint8_t v___x_2597_; 
v___x_2597_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8_spec__13___redArg(v_x_2594_, v_x_2595_, v_x_2596_);
return v___x_2597_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8_spec__13___boxed(lean_object* v_00_u03b2_2598_, lean_object* v_x_2599_, lean_object* v_x_2600_, lean_object* v_x_2601_){
_start:
{
size_t v_x_13853__boxed_2602_; uint8_t v_res_2603_; lean_object* v_r_2604_; 
v_x_13853__boxed_2602_ = lean_unbox_usize(v_x_2600_);
lean_dec(v_x_2600_);
v_res_2603_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8_spec__13(v_00_u03b2_2598_, v_x_2599_, v_x_13853__boxed_2602_, v_x_2601_);
lean_dec(v_x_2601_);
lean_dec_ref(v_x_2599_);
v_r_2604_ = lean_box(v_res_2603_);
return v_r_2604_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__15(lean_object* v_00_u03b2_2605_, lean_object* v_m_2606_){
_start:
{
lean_object* v___x_2607_; 
v___x_2607_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__15___redArg(v_m_2606_);
return v___x_2607_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__15___boxed(lean_object* v_00_u03b2_2608_, lean_object* v_m_2609_){
_start:
{
lean_object* v_res_2610_; 
v_res_2610_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__15(v_00_u03b2_2608_, v_m_2609_);
lean_dec_ref(v_m_2609_);
return v_res_2610_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8(lean_object* v_00_u03b2_2611_, lean_object* v_keys_2612_, lean_object* v_vals_2613_, lean_object* v_heq_2614_, lean_object* v_i_2615_, lean_object* v_k_2616_){
_start:
{
lean_object* v___x_2617_; 
v___x_2617_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8___redArg(v_keys_2612_, v_vals_2613_, v_i_2615_, v_k_2616_);
return v___x_2617_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b2_2618_, lean_object* v_keys_2619_, lean_object* v_vals_2620_, lean_object* v_heq_2621_, lean_object* v_i_2622_, lean_object* v_k_2623_){
_start:
{
lean_object* v_res_2624_; 
v_res_2624_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8(v_00_u03b2_2618_, v_keys_2619_, v_vals_2620_, v_heq_2621_, v_i_2622_, v_k_2623_);
lean_dec(v_k_2623_);
lean_dec_ref(v_vals_2620_);
lean_dec_ref(v_keys_2619_);
return v_res_2624_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8_spec__13_spec__16(lean_object* v_00_u03b2_2625_, lean_object* v_keys_2626_, lean_object* v_vals_2627_, lean_object* v_heq_2628_, lean_object* v_i_2629_, lean_object* v_k_2630_){
_start:
{
uint8_t v___x_2631_; 
v___x_2631_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8_spec__13_spec__16___redArg(v_keys_2626_, v_i_2629_, v_k_2630_);
return v___x_2631_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8_spec__13_spec__16___boxed(lean_object* v_00_u03b2_2632_, lean_object* v_keys_2633_, lean_object* v_vals_2634_, lean_object* v_heq_2635_, lean_object* v_i_2636_, lean_object* v_k_2637_){
_start:
{
uint8_t v_res_2638_; lean_object* v_r_2639_; 
v_res_2638_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8_spec__13_spec__16(v_00_u03b2_2632_, v_keys_2633_, v_vals_2634_, v_heq_2635_, v_i_2636_, v_k_2637_);
lean_dec(v_k_2637_);
lean_dec_ref(v_vals_2634_);
lean_dec_ref(v_keys_2633_);
v_r_2639_ = lean_box(v_res_2638_);
return v_r_2639_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__15_spec__19(lean_object* v_00_u03b2_2640_, lean_object* v_init_2641_, lean_object* v_b_2642_){
_start:
{
lean_object* v___x_2643_; 
v___x_2643_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__15_spec__19___redArg(v_init_2641_, v_b_2642_);
return v___x_2643_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__15_spec__19___boxed(lean_object* v_00_u03b2_2644_, lean_object* v_init_2645_, lean_object* v_b_2646_){
_start:
{
lean_object* v_res_2647_; 
v_res_2647_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__15_spec__19(v_00_u03b2_2644_, v_init_2645_, v_b_2646_);
lean_dec_ref(v_b_2646_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19(lean_object* v_msgData_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_){
_start:
{
lean_object* v___x_2652_; 
v___x_2652_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___redArg(v_msgData_2648_, v___y_2650_);
return v___x_2652_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19___boxed(lean_object* v_msgData_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_){
_start:
{
lean_object* v_res_2657_; 
v_res_2657_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__12_spec__19(v_msgData_2653_, v___y_2654_, v___y_2655_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
return v_res_2657_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__15_spec__19_spec__21(lean_object* v_00_u03b2_2658_, lean_object* v_b_2659_, lean_object* v_acc_2660_, lean_object* v_i_2661_){
_start:
{
lean_object* v___x_2662_; 
v___x_2662_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__15_spec__19_spec__21___redArg(v_b_2659_, v_acc_2660_, v_i_2661_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__15_spec__19_spec__21___boxed(lean_object* v_00_u03b2_2663_, lean_object* v_b_2664_, lean_object* v_acc_2665_, lean_object* v_i_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__15_spec__19_spec__21(v_00_u03b2_2663_, v_b_2664_, v_acc_2665_, v_i_2666_);
lean_dec_ref(v_b_2664_);
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_1366347041____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2669_; lean_object* v___x_2670_; 
v___x_2669_ = ((lean_object*)(l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter));
v___x_2670_ = l_Lean_Elab_Command_addLinter(v___x_2669_);
return v___x_2670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_1366347041____hygCtx___hyg_2____boxed(lean_object* v_a_2671_){
_start:
{
lean_object* v_res_2672_; 
v_res_2672_ = l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_1366347041____hygCtx___hyg_2_();
return v_res_2672_;
}
}
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Init_Try(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_Extra_UnreachableTactic(uint8_t builtin) {
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
res = runtime_initialize_Lean_Parser_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Try(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_Extra_linter_extra_unreachableTactic = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_Extra_linter_extra_unreachableTactic);
lean_dec_ref(res);
res = l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_Extra_UnreachableTactic_ignoreTacticKindsRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_Extra_UnreachableTactic_ignoreTacticKindsRef);
lean_dec_ref(res);
res = l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_1366347041____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Linter_Extra_UnreachableTactic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* initialize_Lean_Linter_Basic(uint8_t builtin);
lean_object* initialize_Lean_Parser_Syntax(uint8_t builtin);
lean_object* initialize_Init_Try(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Linter_Extra_UnreachableTactic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Try(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Extra_UnreachableTactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Linter_Extra_UnreachableTactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Linter_Extra_UnreachableTactic(builtin);
}
#ifdef __cplusplus
}
#endif
