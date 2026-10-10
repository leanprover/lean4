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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default___redArg();
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
uint64_t l_Lean_Syntax_instHashableRange_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
uint8_t l_Lean_Syntax_instBEqRange_beq(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Syntax_instBEqRange_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_instHashableRange_hash___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_NameHashSet_contains(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_ParserExtension_instInhabitedState_default;
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
extern lean_object* l_Lean_Linter_linterSetsExt;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
extern lean_object* l_Lean_Linter_linterMessageTag;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l_instOrdNat___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instOrdInt___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_lexOrd___redArg(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
extern lean_object* l_Lean_Parser_parserExtension;
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameHashSet_insert(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__0_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__0_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__1_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__1_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__2_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__2_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__2_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__3_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__3_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__3_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__4_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "binderTactic"};
static const lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__4_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__4_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__5_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__5_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__5_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__2_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__5_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__5_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__3_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__5_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__5_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__4_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(17, 181, 78, 34, 190, 12, 180, 92)}};
static const lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__5_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__5_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__7_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "dynamicQuot"};
static const lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__7_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__7_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__8_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__8_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__8_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__2_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__8_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__8_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__3_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__8_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__8_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__7_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(116, 123, 139, 164, 173, 191, 116, 242)}};
static const lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__8_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__8_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__10_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__10_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__10_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__11_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "quotSeq"};
static const lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__11_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__11_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__12_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__12_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__12_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__2_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__12_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__12_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__10_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__12_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__12_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__11_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(171, 67, 133, 150, 48, 85, 223, 184)}};
static const lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__12_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__12_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__13_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__13_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__14_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "tacticStop_"};
static const lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__14_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__14_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__15_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__15_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__15_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__2_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__15_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__15_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__10_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__15_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__15_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__14_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(186, 187, 217, 116, 133, 153, 2, 108)}};
static const lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__15_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__15_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__16_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__16_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__17_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__17_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__17_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__18_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "notation"};
static const lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__18_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__18_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__19_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__19_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__19_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__2_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__19_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__19_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__17_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__19_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__19_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__18_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(13, 34, 53, 7, 182, 20, 8, 182)}};
static const lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__19_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__19_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__20_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__20_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__21_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mixfix"};
static const lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__21_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__21_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__22_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__22_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__22_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__2_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__22_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__22_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__17_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__22_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__22_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__21_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 31, 80, 86, 44, 46, 155, 0)}};
static const lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__22_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__22_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__23_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__23_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__24_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "registerTryTactic"};
static const lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__24_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__24_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__25_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__25_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__25_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__2_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__25_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__25_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__17_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__25_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__25_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__24_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(64, 133, 180, 171, 152, 84, 222, 30)}};
static const lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__25_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__25_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__26_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__26_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__27_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "discharger"};
static const lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__27_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__27_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__28_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__28_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__28_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__2_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__28_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__28_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__10_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__28_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__28_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__27_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(233, 186, 255, 143, 150, 72, 152, 71)}};
static const lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__28_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__28_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__29_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__29_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___lam__0(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7_spec__11___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instOrdNat___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7_spec__11___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7_spec__11___redArg___closed__0_value;
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7_spec__11___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instOrdInt___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7_spec__11___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7_spec__11___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19_spec__21_spec__25___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19_spec__21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__20___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4_spec__7_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4_spec__7___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__16(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__20(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__20___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__0;
static lean_once_cell_t l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__1;
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
static lean_once_cell_t l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__5;
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter;
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4_spec__7(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4_spec__7_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__20(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19_spec__21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19_spec__21_spec__25(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_1366347041____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_1366347041____hygCtx___hyg_2____boxed(lean_object*);
lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1_ = stack[0].m_obj;
lean_object* v_decl_2_ = stack[1].m_obj;
lean_object* v_ref_3_ = stack[2].m_obj;
lean_object* v_res_29_;
v_res_29_ = l_Lean_Option_register___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__spec__0(v_name_1_, v_decl_2_, v_ref_3_);
stack->m_obj
 = v_res_29_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_30_, lean_object* v_decl_31_, lean_object* v_ref_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Option_register___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__spec__0(v_name_30_, v_decl_31_, v_ref_32_);
lean_dec_ref(v_decl_31_);
return v_res_34_;
}
}
lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_59_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4_));
v___x_60_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__5_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4_));
v___x_61_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4_));
v___x_62_ = l_Lean_Option_register___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__spec__0(v___x_59_, v___x_60_, v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT void l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_63_;
v_res_63_ = l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4_();
stack->m_obj
 = v_res_63_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4____boxed(lean_object* v_a_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4_();
return v_res_65_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_a_66_, lean_object* v_x_67_){
_start:
{
if (lean_obj_tag(v_x_67_) == 0)
{
uint8_t v___x_68_; 
v___x_68_ = 0;
return v___x_68_;
}
else
{
lean_object* v_key_69_; lean_object* v_tail_70_; uint8_t v___x_71_; 
v_key_69_ = lean_ctor_get(v_x_67_, 0);
v_tail_70_ = lean_ctor_get(v_x_67_, 2);
v___x_71_ = lean_name_eq(v_key_69_, v_a_66_);
if (v___x_71_ == 0)
{
v_x_67_ = v_tail_70_;
goto _start;
}
else
{
return v___x_71_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_66_ = stack[0].m_obj;
lean_object* v_x_67_ = stack[1].m_obj;
uint8_t v_res_73_;
v_res_73_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_66_, v_x_67_);
stack->m_num = v_res_73_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_a_74_, lean_object* v_x_75_){
_start:
{
uint8_t v_res_76_; lean_object* v_r_77_; 
v_res_76_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_74_, v_x_75_);
lean_dec(v_x_75_);
lean_dec(v_a_74_);
v_r_77_ = lean_box(v_res_76_);
return v_r_77_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_78_, lean_object* v_x_79_){
_start:
{
if (lean_obj_tag(v_x_79_) == 0)
{
return v_x_78_;
}
else
{
lean_object* v_key_80_; lean_object* v_value_81_; lean_object* v_tail_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_108_; 
v_key_80_ = lean_ctor_get(v_x_79_, 0);
v_value_81_ = lean_ctor_get(v_x_79_, 1);
v_tail_82_ = lean_ctor_get(v_x_79_, 2);
v_isSharedCheck_108_ = !lean_is_exclusive(v_x_79_);
if (v_isSharedCheck_108_ == 0)
{
v___x_84_ = v_x_79_;
v_isShared_85_ = v_isSharedCheck_108_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_tail_82_);
lean_inc(v_value_81_);
lean_inc(v_key_80_);
lean_dec(v_x_79_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_108_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___x_86_; uint64_t v___y_88_; 
v___x_86_ = lean_array_get_size(v_x_78_);
if (lean_obj_tag(v_key_80_) == 0)
{
uint64_t v___x_106_; 
v___x_106_ = 1723ULL;
v___y_88_ = v___x_106_;
goto v___jp_87_;
}
else
{
uint64_t v_hash_107_; 
v_hash_107_ = lean_ctor_get_uint64(v_key_80_, sizeof(void*)*2);
v___y_88_ = v_hash_107_;
goto v___jp_87_;
}
v___jp_87_:
{
uint64_t v___x_89_; uint64_t v___x_90_; uint64_t v_fold_91_; uint64_t v___x_92_; uint64_t v___x_93_; uint64_t v___x_94_; size_t v___x_95_; size_t v___x_96_; size_t v___x_97_; size_t v___x_98_; size_t v___x_99_; lean_object* v___x_100_; lean_object* v___x_102_; 
v___x_89_ = 32ULL;
v___x_90_ = lean_uint64_shift_right(v___y_88_, v___x_89_);
v_fold_91_ = lean_uint64_xor(v___y_88_, v___x_90_);
v___x_92_ = 16ULL;
v___x_93_ = lean_uint64_shift_right(v_fold_91_, v___x_92_);
v___x_94_ = lean_uint64_xor(v_fold_91_, v___x_93_);
v___x_95_ = lean_uint64_to_usize(v___x_94_);
v___x_96_ = lean_usize_of_nat(v___x_86_);
v___x_97_ = ((size_t)1ULL);
v___x_98_ = lean_usize_sub(v___x_96_, v___x_97_);
v___x_99_ = lean_usize_land(v___x_95_, v___x_98_);
v___x_100_ = lean_array_uget_borrowed(v_x_78_, v___x_99_);
lean_inc(v___x_100_);
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 2, v___x_100_);
v___x_102_ = v___x_84_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v_key_80_);
lean_ctor_set(v_reuseFailAlloc_105_, 1, v_value_81_);
lean_ctor_set(v_reuseFailAlloc_105_, 2, v___x_100_);
v___x_102_ = v_reuseFailAlloc_105_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
lean_object* v___x_103_; 
v___x_103_ = lean_array_uset(v_x_78_, v___x_99_, v___x_102_);
v_x_78_ = v___x_103_;
v_x_79_ = v_tail_82_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(lean_object* v_i_109_, lean_object* v_source_110_, lean_object* v_target_111_){
_start:
{
lean_object* v___x_112_; uint8_t v___x_113_; 
v___x_112_ = lean_array_get_size(v_source_110_);
v___x_113_ = lean_nat_dec_lt(v_i_109_, v___x_112_);
if (v___x_113_ == 0)
{
lean_dec_ref(v_source_110_);
lean_dec(v_i_109_);
return v_target_111_;
}
else
{
lean_object* v_es_114_; lean_object* v___x_115_; lean_object* v_source_116_; lean_object* v_target_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v_es_114_ = lean_array_fget(v_source_110_, v_i_109_);
v___x_115_ = lean_box(0);
v_source_116_ = lean_array_fset(v_source_110_, v_i_109_, v___x_115_);
v_target_117_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg(v_target_111_, v_es_114_);
v___x_118_ = lean_unsigned_to_nat(1u);
v___x_119_ = lean_nat_add(v_i_109_, v___x_118_);
lean_dec(v_i_109_);
v_i_109_ = v___x_119_;
v_source_110_ = v_source_116_;
v_target_111_ = v_target_117_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_data_121_){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v_nbuckets_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_122_ = lean_array_get_size(v_data_121_);
v___x_123_ = lean_unsigned_to_nat(2u);
v_nbuckets_124_ = lean_nat_mul(v___x_122_, v___x_123_);
v___x_125_ = lean_unsigned_to_nat(0u);
v___x_126_ = lean_box(0);
v___x_127_ = lean_mk_array(v_nbuckets_124_, v___x_126_);
v___x_128_ = lean_array_propagate_mark(v_data_121_, v___x_127_);
v___x_129_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v___x_125_, v_data_121_, v___x_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(lean_object* v_m_130_, lean_object* v_a_131_, lean_object* v_b_132_){
_start:
{
lean_object* v_size_133_; lean_object* v_buckets_134_; lean_object* v___x_135_; uint64_t v___y_137_; 
v_size_133_ = lean_ctor_get(v_m_130_, 0);
v_buckets_134_ = lean_ctor_get(v_m_130_, 1);
v___x_135_ = lean_array_get_size(v_buckets_134_);
if (lean_obj_tag(v_a_131_) == 0)
{
uint64_t v___x_174_; 
v___x_174_ = 1723ULL;
v___y_137_ = v___x_174_;
goto v___jp_136_;
}
else
{
uint64_t v_hash_175_; 
v_hash_175_ = lean_ctor_get_uint64(v_a_131_, sizeof(void*)*2);
v___y_137_ = v_hash_175_;
goto v___jp_136_;
}
v___jp_136_:
{
uint64_t v___x_138_; uint64_t v___x_139_; uint64_t v_fold_140_; uint64_t v___x_141_; uint64_t v___x_142_; uint64_t v___x_143_; size_t v___x_144_; size_t v___x_145_; size_t v___x_146_; size_t v___x_147_; size_t v___x_148_; lean_object* v_bkt_149_; uint8_t v___x_150_; 
v___x_138_ = 32ULL;
v___x_139_ = lean_uint64_shift_right(v___y_137_, v___x_138_);
v_fold_140_ = lean_uint64_xor(v___y_137_, v___x_139_);
v___x_141_ = 16ULL;
v___x_142_ = lean_uint64_shift_right(v_fold_140_, v___x_141_);
v___x_143_ = lean_uint64_xor(v_fold_140_, v___x_142_);
v___x_144_ = lean_uint64_to_usize(v___x_143_);
v___x_145_ = lean_usize_of_nat(v___x_135_);
v___x_146_ = ((size_t)1ULL);
v___x_147_ = lean_usize_sub(v___x_145_, v___x_146_);
v___x_148_ = lean_usize_land(v___x_144_, v___x_147_);
v_bkt_149_ = lean_array_uget_borrowed(v_buckets_134_, v___x_148_);
v___x_150_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_131_, v_bkt_149_);
if (v___x_150_ == 0)
{
lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_171_; 
lean_inc_ref(v_buckets_134_);
lean_inc(v_size_133_);
v_isSharedCheck_171_ = !lean_is_exclusive(v_m_130_);
if (v_isSharedCheck_171_ == 0)
{
lean_object* v_unused_172_; lean_object* v_unused_173_; 
v_unused_172_ = lean_ctor_get(v_m_130_, 1);
lean_dec(v_unused_172_);
v_unused_173_ = lean_ctor_get(v_m_130_, 0);
lean_dec(v_unused_173_);
v___x_152_ = v_m_130_;
v_isShared_153_ = v_isSharedCheck_171_;
goto v_resetjp_151_;
}
else
{
lean_dec(v_m_130_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_171_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_154_; lean_object* v_size_x27_155_; lean_object* v___x_156_; lean_object* v_buckets_x27_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; 
v___x_154_ = lean_unsigned_to_nat(1u);
v_size_x27_155_ = lean_nat_add(v_size_133_, v___x_154_);
lean_dec(v_size_133_);
lean_inc(v_bkt_149_);
v___x_156_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_156_, 0, v_a_131_);
lean_ctor_set(v___x_156_, 1, v_b_132_);
lean_ctor_set(v___x_156_, 2, v_bkt_149_);
v_buckets_x27_157_ = lean_array_uset(v_buckets_134_, v___x_148_, v___x_156_);
v___x_158_ = lean_unsigned_to_nat(4u);
v___x_159_ = lean_nat_mul(v_size_x27_155_, v___x_158_);
v___x_160_ = lean_unsigned_to_nat(3u);
v___x_161_ = lean_nat_div(v___x_159_, v___x_160_);
lean_dec(v___x_159_);
v___x_162_ = lean_array_get_size(v_buckets_x27_157_);
v___x_163_ = lean_nat_dec_le(v___x_161_, v___x_162_);
lean_dec(v___x_161_);
if (v___x_163_ == 0)
{
lean_object* v_val_164_; lean_object* v___x_166_; 
v_val_164_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1___redArg(v_buckets_x27_157_);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 1, v_val_164_);
lean_ctor_set(v___x_152_, 0, v_size_x27_155_);
v___x_166_ = v___x_152_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_size_x27_155_);
lean_ctor_set(v_reuseFailAlloc_167_, 1, v_val_164_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
else
{
lean_object* v___x_169_; 
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 1, v_buckets_x27_157_);
lean_ctor_set(v___x_152_, 0, v_size_x27_155_);
v___x_169_ = v___x_152_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_size_x27_155_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v_buckets_x27_157_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
}
else
{
lean_dec(v_b_132_);
lean_dec(v_a_131_);
return v_m_130_;
}
}
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__0_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_176_ = lean_box(0);
v___x_177_ = lean_unsigned_to_nat(16u);
v___x_178_ = lean_mk_array(v___x_177_, v___x_176_);
return v___x_178_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__1_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_179_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__0_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__0_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__0_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
v___x_180_ = lean_unsigned_to_nat(0u);
v___x_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
lean_ctor_set(v___x_181_, 1, v___x_179_);
return v___x_181_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_190_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__5_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_));
v___x_191_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__1_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__1_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__1_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
v___x_192_ = l_Lean_NameHashSet_insert(v___x_191_, v___x_190_);
return v___x_192_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_199_ = lean_box(0);
v___x_200_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__8_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_));
v___x_201_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
v___x_202_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___x_201_, v___x_200_, v___x_199_);
return v___x_202_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__13_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_210_ = lean_box(0);
v___x_211_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__12_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_));
v___x_212_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
v___x_213_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___x_212_, v___x_211_, v___x_210_);
return v___x_213_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__16_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_220_ = lean_box(0);
v___x_221_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__15_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_));
v___x_222_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__13_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__13_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__13_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
v___x_223_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___x_222_, v___x_221_, v___x_220_);
return v___x_223_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__20_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_231_ = lean_box(0);
v___x_232_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__19_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_));
v___x_233_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__16_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__16_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__16_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
v___x_234_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___x_233_, v___x_232_, v___x_231_);
return v___x_234_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__23_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_241_ = lean_box(0);
v___x_242_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__22_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_));
v___x_243_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__20_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__20_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__20_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
v___x_244_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___x_243_, v___x_242_, v___x_241_);
return v___x_244_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__26_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_251_ = lean_box(0);
v___x_252_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__25_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_));
v___x_253_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__23_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__23_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__23_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
v___x_254_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___x_253_, v___x_252_, v___x_251_);
return v___x_254_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__29_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_261_ = lean_box(0);
v___x_262_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__28_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_));
v___x_263_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__26_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__26_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__26_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
v___x_264_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___x_263_, v___x_262_, v___x_261_);
return v___x_264_;
}
}
lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_266_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__29_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__29_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__29_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
v___x_267_ = lean_st_mk_ref(v___x_266_);
v___x_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
return v___x_268_;
}
}
LEAN_EXPORT void l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_269_;
v_res_269_ = l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_();
stack->m_obj
 = v_res_269_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2____boxed(lean_object* v_a_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_();
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_272_, lean_object* v_m_273_, lean_object* v_a_274_, lean_object* v_b_275_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v_m_273_, v_a_274_, v_b_275_);
return v___x_276_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_277_, lean_object* v_a_278_, lean_object* v_x_279_){
_start:
{
uint8_t v___x_280_; 
v___x_280_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_278_, v_x_279_);
return v___x_280_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_278_ = stack[1].m_obj;
lean_object* v_x_279_ = stack[2].m_obj;
uint8_t v_res_281_;
v_res_281_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0(lean_box(0), v_a_278_, v_x_279_);
stack->m_num = v_res_281_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_282_, lean_object* v_a_283_, lean_object* v_x_284_){
_start:
{
uint8_t v_res_285_; lean_object* v_r_286_; 
v_res_285_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_282_, v_a_283_, v_x_284_);
lean_dec(v_x_284_);
lean_dec(v_a_283_);
v_r_286_ = lean_box(v_res_285_);
return v_r_286_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_00_u03b2_287_, lean_object* v_data_288_){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1___redArg(v_data_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2(lean_object* v_00_u03b2_290_, lean_object* v_i_291_, lean_object* v_source_292_, lean_object* v_target_293_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v_i_291_, v_source_292_, v_target_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_295_, lean_object* v_x_296_, lean_object* v_x_297_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg(v_x_296_, v_x_297_);
return v___x_298_;
}
}
uint8_t l_Lean_Linter_Extra_UnreachableTactic_isIgnoreTacticKind(lean_object* v_ignoreTacticKinds_300_, lean_object* v_k_301_){
_start:
{
if (lean_obj_tag(v_k_301_) == 1)
{
lean_object* v_str_302_; lean_object* v___x_303_; uint8_t v___x_304_; 
v_str_302_ = lean_ctor_get(v_k_301_, 1);
v___x_303_ = ((lean_object*)(l_Lean_Linter_Extra_UnreachableTactic_isIgnoreTacticKind___closed__0));
v___x_304_ = lean_string_dec_eq(v_str_302_, v___x_303_);
if (v___x_304_ == 0)
{
uint8_t v___x_305_; 
v___x_305_ = l_Lean_NameHashSet_contains(v_ignoreTacticKinds_300_, v_k_301_);
return v___x_305_;
}
else
{
return v___x_304_;
}
}
else
{
uint8_t v___x_306_; 
v___x_306_ = l_Lean_NameHashSet_contains(v_ignoreTacticKinds_300_, v_k_301_);
return v___x_306_;
}
}
}
LEAN_EXPORT void l_Lean_Linter_Extra_UnreachableTactic_isIgnoreTacticKind_0interp(lean_interpreter_value* stack)
{
lean_object* v_ignoreTacticKinds_300_ = stack[0].m_obj;
lean_object* v_k_301_ = stack[1].m_obj;
uint8_t v_res_307_;
v_res_307_ = l_Lean_Linter_Extra_UnreachableTactic_isIgnoreTacticKind(v_ignoreTacticKinds_300_, v_k_301_);
stack->m_num = v_res_307_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_isIgnoreTacticKind___boxed(lean_object* v_ignoreTacticKinds_308_, lean_object* v_k_309_){
_start:
{
uint8_t v_res_310_; lean_object* v_r_311_; 
v_res_310_ = l_Lean_Linter_Extra_UnreachableTactic_isIgnoreTacticKind(v_ignoreTacticKinds_308_, v_k_309_);
lean_dec(v_k_309_);
lean_dec_ref(v_ignoreTacticKinds_308_);
v_r_311_ = lean_box(v_res_310_);
return v_r_311_;
}
}
lean_object* l_Lean_Linter_Extra_UnreachableTactic_addIgnoreTacticKind(lean_object* v_kind_312_){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_314_ = l_Lean_Linter_Extra_UnreachableTactic_ignoreTacticKindsRef;
v___x_315_ = lean_st_ref_take(v___x_314_);
v___x_316_ = l_Lean_NameHashSet_insert(v___x_315_, v_kind_312_);
v___x_317_ = lean_st_ref_put(v___x_314_, v___x_316_);
v___x_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
return v___x_318_;
}
}
LEAN_EXPORT void l_Lean_Linter_Extra_UnreachableTactic_addIgnoreTacticKind_0interp(lean_interpreter_value* stack)
{
lean_object* v_kind_312_ = stack[0].m_obj;
lean_object* v_res_319_;
v_res_319_ = l_Lean_Linter_Extra_UnreachableTactic_addIgnoreTacticKind(v_kind_312_);
stack->m_obj
 = v_res_319_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_addIgnoreTacticKind___boxed(lean_object* v_kind_320_, lean_object* v_a_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lean_Linter_Extra_UnreachableTactic_addIgnoreTacticKind(v_kind_320_);
return v_res_322_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__0(void){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = l_instMonadEIO___redArg();
return v___x_323_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__1(void){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = lean_obj_once(&l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__0, &l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__0_once, _init_l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__0);
v___x_325_ = l_StateRefT_x27_instMonad___redArg(v___x_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_getTactics___lam__0___boxed(lean_object* v_ignoreTacticKinds_328_, lean_object* v_isTacKind_329_, lean_object* v_x_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_Linter_Extra_UnreachableTactic_getTactics___lam__0(v_ignoreTacticKinds_328_, v_isTacKind_329_, v_x_330_, v___y_331_, v___y_332_);
lean_dec(v___y_332_);
return v_res_334_;
}
}
lean_object* l_Lean_Linter_Extra_UnreachableTactic_getTactics(lean_object* v_ignoreTacticKinds_335_, lean_object* v_isTacKind_336_, lean_object* v_stx_337_, lean_object* v_a_338_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = lean_obj_once(&l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__1, &l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__1_once, _init_l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__1);
if (lean_obj_tag(v_stx_337_) == 1)
{
lean_object* v_kind_341_; lean_object* v_args_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___y_346_; lean_object* v___y_368_; uint8_t v___x_369_; 
v_kind_341_ = lean_ctor_get(v_stx_337_, 1);
v_args_342_ = lean_ctor_get(v_stx_337_, 2);
v___x_343_ = ((lean_object*)(l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__2));
v___x_344_ = ((lean_object*)(l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__3));
v___x_369_ = l_Lean_Linter_Extra_UnreachableTactic_isIgnoreTacticKind(v_ignoreTacticKinds_335_, v_kind_341_);
if (v___x_369_ == 0)
{
lean_object* v___x_370_; lean_object* v___x_371_; uint8_t v___x_372_; 
v___x_370_ = lean_unsigned_to_nat(0u);
v___x_371_ = lean_array_get_size(v_args_342_);
v___x_372_ = lean_nat_dec_lt(v___x_370_, v___x_371_);
if (v___x_372_ == 0)
{
lean_dec_ref(v_ignoreTacticKinds_335_);
v___y_346_ = v_a_338_;
goto v___jp_345_;
}
else
{
lean_object* v___f_373_; lean_object* v___x_374_; uint8_t v___x_375_; 
lean_inc_ref(v_isTacKind_336_);
v___f_373_ = lean_alloc_closure((void*)(l_Lean_Linter_Extra_UnreachableTactic_getTactics___lam__0___boxed), 6, 2);
lean_closure_set(v___f_373_, 0, v_ignoreTacticKinds_335_);
lean_closure_set(v___f_373_, 1, v_isTacKind_336_);
v___x_374_ = lean_box(0);
v___x_375_ = lean_nat_dec_le(v___x_371_, v___x_371_);
if (v___x_375_ == 0)
{
if (v___x_372_ == 0)
{
lean_dec_ref(v___f_373_);
v___y_346_ = v_a_338_;
goto v___jp_345_;
}
else
{
size_t v___x_376_; size_t v___x_377_; lean_object* v___x_923__overap_378_; lean_object* v___x_379_; 
v___x_376_ = ((size_t)0ULL);
v___x_377_ = lean_usize_of_nat(v___x_371_);
lean_inc_ref(v_args_342_);
v___x_923__overap_378_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_340_, v___f_373_, v_args_342_, v___x_376_, v___x_377_, v___x_374_);
lean_inc(v_a_338_);
v___x_379_ = lean_apply_2(v___x_923__overap_378_, v_a_338_, lean_box(0));
v___y_368_ = v___x_379_;
goto v___jp_367_;
}
}
else
{
size_t v___x_380_; size_t v___x_381_; lean_object* v___x_926__overap_382_; lean_object* v___x_383_; 
v___x_380_ = ((size_t)0ULL);
v___x_381_ = lean_usize_of_nat(v___x_371_);
lean_inc_ref(v_args_342_);
v___x_926__overap_382_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_340_, v___f_373_, v_args_342_, v___x_380_, v___x_381_, v___x_374_);
lean_inc(v_a_338_);
v___x_383_ = lean_apply_2(v___x_926__overap_382_, v_a_338_, lean_box(0));
v___y_368_ = v___x_383_;
goto v___jp_367_;
}
}
}
else
{
lean_dec_ref(v_ignoreTacticKinds_335_);
v___y_346_ = v_a_338_;
goto v___jp_345_;
}
v___jp_345_:
{
lean_object* v___x_347_; uint8_t v___x_348_; 
lean_inc(v_kind_341_);
v___x_347_ = lean_apply_1(v_isTacKind_336_, v_kind_341_);
v___x_348_ = lean_unbox(v___x_347_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; lean_object* v___x_350_; 
lean_dec_ref_known(v_stx_337_, 3);
v___x_349_ = lean_box(0);
v___x_350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
return v___x_350_;
}
else
{
uint8_t v___x_351_; lean_object* v___x_352_; 
v___x_351_ = lean_unbox(v___x_347_);
v___x_352_ = l_Lean_Syntax_getRange_x3f(v_stx_337_, v___x_351_);
if (lean_obj_tag(v___x_352_) == 1)
{
lean_object* v_val_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_364_; 
v_val_353_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_364_ == 0)
{
v___x_355_ = v___x_352_;
v_isShared_356_ = v_isSharedCheck_364_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_val_353_);
lean_dec(v___x_352_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_364_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_362_; 
v___x_357_ = lean_st_ref_take(v___y_346_);
v___x_358_ = lean_box(0);
v___x_359_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_343_, v___x_344_, v___x_357_, v_val_353_, v_stx_337_);
v___x_360_ = lean_st_ref_put(v___y_346_, v___x_359_);
if (v_isShared_356_ == 0)
{
lean_ctor_set_tag(v___x_355_, 0);
lean_ctor_set(v___x_355_, 0, v___x_358_);
v___x_362_ = v___x_355_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v___x_358_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
else
{
lean_object* v___x_365_; lean_object* v___x_366_; 
lean_dec(v___x_352_);
lean_dec_ref_known(v_stx_337_, 3);
v___x_365_ = lean_box(0);
v___x_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
return v___x_366_;
}
}
}
v___jp_367_:
{
if (lean_obj_tag(v___y_368_) == 0)
{
lean_dec_ref_known(v___y_368_, 1);
v___y_346_ = v_a_338_;
goto v___jp_345_;
}
else
{
lean_dec_ref_known(v_stx_337_, 3);
lean_dec_ref(v_isTacKind_336_);
return v___y_368_;
}
}
}
else
{
lean_object* v___x_384_; lean_object* v___x_385_; 
lean_dec(v_stx_337_);
lean_dec_ref(v_isTacKind_336_);
lean_dec_ref(v_ignoreTacticKinds_335_);
v___x_384_ = lean_box(0);
v___x_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
return v___x_385_;
}
}
}
LEAN_EXPORT void l_Lean_Linter_Extra_UnreachableTactic_getTactics_0interp(lean_interpreter_value* stack)
{
lean_object* v_ignoreTacticKinds_335_ = stack[0].m_obj;
lean_object* v_isTacKind_336_ = stack[1].m_obj;
lean_object* v_stx_337_ = stack[2].m_obj;
lean_object* v_a_338_ = stack[3].m_obj;
lean_object* v_res_386_;
v_res_386_ = l_Lean_Linter_Extra_UnreachableTactic_getTactics(v_ignoreTacticKinds_335_, v_isTacKind_336_, v_stx_337_, v_a_338_);
stack->m_obj
 = v_res_386_;
}
lean_object* l_Lean_Linter_Extra_UnreachableTactic_getTactics___lam__0(lean_object* v_ignoreTacticKinds_387_, lean_object* v_isTacKind_388_, lean_object* v_x_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_Lean_Linter_Extra_UnreachableTactic_getTactics(v_ignoreTacticKinds_387_, v_isTacKind_388_, v___y_390_, v___y_391_);
return v___x_393_;
}
}
LEAN_EXPORT void l_Lean_Linter_Extra_UnreachableTactic_getTactics___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ignoreTacticKinds_387_ = stack[0].m_obj;
lean_object* v_isTacKind_388_ = stack[1].m_obj;
lean_object* v_x_389_ = stack[2].m_obj;
lean_object* v___y_390_ = stack[3].m_obj;
lean_object* v___y_391_ = stack[4].m_obj;
lean_object* v_res_394_;
v_res_394_ = l_Lean_Linter_Extra_UnreachableTactic_getTactics___lam__0(v_ignoreTacticKinds_387_, v_isTacKind_388_, v_x_389_, v___y_390_, v___y_391_);
stack->m_obj
 = v_res_394_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_getTactics___boxed(lean_object* v_ignoreTacticKinds_395_, lean_object* v_isTacKind_396_, lean_object* v_stx_397_, lean_object* v_a_398_, lean_object* v_a_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lean_Linter_Extra_UnreachableTactic_getTactics(v_ignoreTacticKinds_395_, v_isTacKind_396_, v_stx_397_, v_a_398_);
lean_dec(v_a_398_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__6___redArg(lean_object* v_a_401_, lean_object* v_x_402_){
_start:
{
if (lean_obj_tag(v_x_402_) == 0)
{
return v_x_402_;
}
else
{
lean_object* v_key_403_; lean_object* v_value_404_; lean_object* v_tail_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_414_; 
v_key_403_ = lean_ctor_get(v_x_402_, 0);
v_value_404_ = lean_ctor_get(v_x_402_, 1);
v_tail_405_ = lean_ctor_get(v_x_402_, 2);
v_isSharedCheck_414_ = !lean_is_exclusive(v_x_402_);
if (v_isSharedCheck_414_ == 0)
{
v___x_407_ = v_x_402_;
v_isShared_408_ = v_isSharedCheck_414_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_tail_405_);
lean_inc(v_value_404_);
lean_inc(v_key_403_);
lean_dec(v_x_402_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_414_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
uint8_t v___x_409_; 
v___x_409_ = l_Lean_Syntax_instBEqRange_beq(v_key_403_, v_a_401_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; lean_object* v___x_412_; 
v___x_410_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__6___redArg(v_a_401_, v_tail_405_);
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 2, v___x_410_);
v___x_412_ = v___x_407_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_key_403_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v_value_404_);
lean_ctor_set(v_reuseFailAlloc_413_, 2, v___x_410_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
else
{
lean_del_object(v___x_407_);
lean_dec(v_value_404_);
lean_dec(v_key_403_);
return v_tail_405_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__6___redArg___boxed(lean_object* v_a_415_, lean_object* v_x_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__6___redArg(v_a_415_, v_x_416_);
lean_dec_ref(v_a_415_);
return v_res_417_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5___redArg(lean_object* v_a_418_, lean_object* v_x_419_){
_start:
{
if (lean_obj_tag(v_x_419_) == 0)
{
uint8_t v___x_420_; 
v___x_420_ = 0;
return v___x_420_;
}
else
{
lean_object* v_key_421_; lean_object* v_tail_422_; uint8_t v___x_423_; 
v_key_421_ = lean_ctor_get(v_x_419_, 0);
v_tail_422_ = lean_ctor_get(v_x_419_, 2);
v___x_423_ = l_Lean_Syntax_instBEqRange_beq(v_key_421_, v_a_418_);
if (v___x_423_ == 0)
{
v_x_419_ = v_tail_422_;
goto _start;
}
else
{
return v___x_423_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_418_ = stack[0].m_obj;
lean_object* v_x_419_ = stack[1].m_obj;
uint8_t v_res_425_;
v_res_425_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5___redArg(v_a_418_, v_x_419_);
stack->m_num = v_res_425_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5___redArg___boxed(lean_object* v_a_426_, lean_object* v_x_427_){
_start:
{
uint8_t v_res_428_; lean_object* v_r_429_; 
v_res_428_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5___redArg(v_a_426_, v_x_427_);
lean_dec(v_x_427_);
lean_dec_ref(v_a_426_);
v_r_429_ = lean_box(v_res_428_);
return v_r_429_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2___redArg(lean_object* v_m_430_, lean_object* v_a_431_){
_start:
{
lean_object* v_size_432_; lean_object* v_buckets_433_; lean_object* v___x_434_; uint64_t v___x_435_; uint64_t v___x_436_; uint64_t v___x_437_; uint64_t v_fold_438_; uint64_t v___x_439_; uint64_t v___x_440_; uint64_t v___x_441_; size_t v___x_442_; size_t v___x_443_; size_t v___x_444_; size_t v___x_445_; size_t v___x_446_; lean_object* v_bkt_447_; uint8_t v___x_448_; 
v_size_432_ = lean_ctor_get(v_m_430_, 0);
v_buckets_433_ = lean_ctor_get(v_m_430_, 1);
v___x_434_ = lean_array_get_size(v_buckets_433_);
v___x_435_ = l_Lean_Syntax_instHashableRange_hash(v_a_431_);
v___x_436_ = 32ULL;
v___x_437_ = lean_uint64_shift_right(v___x_435_, v___x_436_);
v_fold_438_ = lean_uint64_xor(v___x_435_, v___x_437_);
v___x_439_ = 16ULL;
v___x_440_ = lean_uint64_shift_right(v_fold_438_, v___x_439_);
v___x_441_ = lean_uint64_xor(v_fold_438_, v___x_440_);
v___x_442_ = lean_uint64_to_usize(v___x_441_);
v___x_443_ = lean_usize_of_nat(v___x_434_);
v___x_444_ = ((size_t)1ULL);
v___x_445_ = lean_usize_sub(v___x_443_, v___x_444_);
v___x_446_ = lean_usize_land(v___x_442_, v___x_445_);
v_bkt_447_ = lean_array_uget_borrowed(v_buckets_433_, v___x_446_);
v___x_448_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5___redArg(v_a_431_, v_bkt_447_);
if (v___x_448_ == 0)
{
return v_m_430_;
}
else
{
lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_461_; 
lean_inc(v_bkt_447_);
lean_inc_ref(v_buckets_433_);
lean_inc(v_size_432_);
v_isSharedCheck_461_ = !lean_is_exclusive(v_m_430_);
if (v_isSharedCheck_461_ == 0)
{
lean_object* v_unused_462_; lean_object* v_unused_463_; 
v_unused_462_ = lean_ctor_get(v_m_430_, 1);
lean_dec(v_unused_462_);
v_unused_463_ = lean_ctor_get(v_m_430_, 0);
lean_dec(v_unused_463_);
v___x_450_ = v_m_430_;
v_isShared_451_ = v_isSharedCheck_461_;
goto v_resetjp_449_;
}
else
{
lean_dec(v_m_430_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_461_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_452_; lean_object* v_buckets_x27_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_459_; 
v___x_452_ = lean_box(0);
v_buckets_x27_453_ = lean_array_uset(v_buckets_433_, v___x_446_, v___x_452_);
v___x_454_ = lean_unsigned_to_nat(1u);
v___x_455_ = lean_nat_sub(v_size_432_, v___x_454_);
lean_dec(v_size_432_);
v___x_456_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__6___redArg(v_a_431_, v_bkt_447_);
v___x_457_ = lean_array_uset(v_buckets_x27_453_, v___x_446_, v___x_456_);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 1, v___x_457_);
lean_ctor_set(v___x_450_, 0, v___x_455_);
v___x_459_ = v___x_450_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v___x_455_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v___x_457_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2___redArg___boxed(lean_object* v_m_464_, lean_object* v_a_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2___redArg(v_m_464_, v_a_465_);
lean_dec_ref(v_a_465_);
return v_res_466_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_467_;
}
}
lean_object* l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics(lean_object* v_x_468_, lean_object* v_a_469_){
_start:
{
switch(lean_obj_tag(v_x_468_))
{
case 0:
{
lean_object* v_t_471_; 
v_t_471_ = lean_ctor_get(v_x_468_, 1);
lean_inc_ref(v_t_471_);
lean_dec_ref_known(v_x_468_, 2);
v_x_468_ = v_t_471_;
goto _start;
}
case 1:
{
lean_object* v_i_473_; 
v_i_473_ = lean_ctor_get(v_x_468_, 0);
if (lean_obj_tag(v_i_473_) == 0)
{
lean_object* v_i_474_; lean_object* v_toElabInfo_475_; lean_object* v_children_476_; lean_object* v_stx_477_; uint8_t v___x_478_; lean_object* v___x_479_; 
v_i_474_ = lean_ctor_get(v_i_473_, 0);
v_toElabInfo_475_ = lean_ctor_get(v_i_474_, 0);
lean_inc_ref(v_toElabInfo_475_);
v_children_476_ = lean_ctor_get(v_x_468_, 1);
lean_inc_ref(v_children_476_);
lean_dec_ref_known(v_x_468_, 2);
v_stx_477_ = lean_ctor_get(v_toElabInfo_475_, 1);
lean_inc(v_stx_477_);
lean_dec_ref(v_toElabInfo_475_);
v___x_478_ = 1;
v___x_479_ = l_Lean_Syntax_getRange_x3f(v_stx_477_, v___x_478_);
lean_dec(v_stx_477_);
if (lean_obj_tag(v___x_479_) == 1)
{
lean_object* v_val_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v_val_480_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_val_480_);
lean_dec_ref_known(v___x_479_, 1);
v___x_481_ = lean_st_ref_take(v_a_469_);
v___x_482_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2___redArg(v___x_481_, v_val_480_);
lean_dec(v_val_480_);
v___x_483_ = lean_st_ref_put(v_a_469_, v___x_482_);
v___x_484_ = l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList(v_children_476_, v_a_469_);
return v___x_484_;
}
else
{
lean_object* v___x_485_; 
lean_dec(v___x_479_);
v___x_485_ = l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList(v_children_476_, v_a_469_);
return v___x_485_;
}
}
else
{
lean_object* v_children_486_; lean_object* v___x_487_; 
v_children_486_ = lean_ctor_get(v_x_468_, 1);
lean_inc_ref(v_children_486_);
lean_dec_ref_known(v_x_468_, 2);
v___x_487_ = l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList(v_children_486_, v_a_469_);
return v___x_487_;
}
}
default: 
{
lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_495_; 
v_isSharedCheck_495_ = !lean_is_exclusive(v_x_468_);
if (v_isSharedCheck_495_ == 0)
{
lean_object* v_unused_496_; 
v_unused_496_ = lean_ctor_get(v_x_468_, 0);
lean_dec(v_unused_496_);
v___x_489_ = v_x_468_;
v_isShared_490_ = v_isSharedCheck_495_;
goto v_resetjp_488_;
}
else
{
lean_dec(v_x_468_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_495_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_491_; lean_object* v___x_493_; 
v___x_491_ = lean_box(0);
if (v_isShared_490_ == 0)
{
lean_ctor_set_tag(v___x_489_, 0);
lean_ctor_set(v___x_489_, 0, v___x_491_);
v___x_493_ = v___x_489_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_491_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_468_ = stack[0].m_obj;
lean_object* v_a_469_ = stack[1].m_obj;
lean_object* v_res_497_;
v_res_497_ = l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics(v_x_468_, v_a_469_);
stack->m_obj
 = v_res_497_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(lean_object* v_as_498_, size_t v_i_499_, size_t v_stop_500_, lean_object* v_b_501_, lean_object* v___y_502_){
_start:
{
uint8_t v___x_504_; 
v___x_504_ = lean_usize_dec_eq(v_i_499_, v_stop_500_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = lean_array_uget_borrowed(v_as_498_, v_i_499_);
lean_inc(v___x_505_);
v___x_506_ = l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics(v___x_505_, v___y_502_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; size_t v___x_508_; size_t v___x_509_; 
v_a_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_a_507_);
lean_dec_ref_known(v___x_506_, 1);
v___x_508_ = ((size_t)1ULL);
v___x_509_ = lean_usize_add(v_i_499_, v___x_508_);
v_i_499_ = v___x_509_;
v_b_501_ = v_a_507_;
goto _start;
}
else
{
return v___x_506_;
}
}
else
{
lean_object* v___x_511_; 
v___x_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_511_, 0, v_b_501_);
return v___x_511_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_498_ = stack[0].m_obj;
size_t v_i_499_ = stack[1].m_num;
size_t v_stop_500_ = stack[2].m_num;
lean_object* v_b_501_ = stack[3].m_obj;
lean_object* v___y_502_ = stack[4].m_obj;
lean_object* v_res_512_;
v_res_512_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(v_as_498_, v_i_499_, v_stop_500_, v_b_501_, v___y_502_);
stack->m_obj
 = v_res_512_;
}
lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__2(lean_object* v_x_513_, lean_object* v___y_514_){
_start:
{
if (lean_obj_tag(v_x_513_) == 0)
{
lean_object* v_cs_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_530_; 
v_cs_516_ = lean_ctor_get(v_x_513_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v_x_513_);
if (v_isSharedCheck_530_ == 0)
{
v___x_518_ = v_x_513_;
v_isShared_519_ = v_isSharedCheck_530_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_cs_516_);
lean_dec(v_x_513_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_530_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; uint8_t v___x_523_; 
v___x_520_ = lean_unsigned_to_nat(0u);
v___x_521_ = lean_array_get_size(v_cs_516_);
v___x_522_ = lean_box(0);
v___x_523_ = lean_nat_dec_lt(v___x_520_, v___x_521_);
if (v___x_523_ == 0)
{
lean_object* v___x_525_; 
lean_dec_ref(v_cs_516_);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 0, v___x_522_);
v___x_525_ = v___x_518_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_522_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
else
{
size_t v___x_527_; size_t v___x_528_; lean_object* v___x_529_; 
lean_del_object(v___x_518_);
v___x_527_ = ((size_t)0ULL);
v___x_528_ = lean_usize_of_nat(v___x_521_);
v___x_529_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__3(v_cs_516_, v___x_527_, v___x_528_, v___x_522_, v___y_514_);
lean_dec_ref(v_cs_516_);
return v___x_529_;
}
}
}
else
{
lean_object* v_vs_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_545_; 
v_vs_531_ = lean_ctor_get(v_x_513_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v_x_513_);
if (v_isSharedCheck_545_ == 0)
{
v___x_533_ = v_x_513_;
v_isShared_534_ = v_isSharedCheck_545_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_vs_531_);
lean_dec(v_x_513_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_545_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; uint8_t v___x_538_; 
v___x_535_ = lean_unsigned_to_nat(0u);
v___x_536_ = lean_array_get_size(v_vs_531_);
v___x_537_ = lean_box(0);
v___x_538_ = lean_nat_dec_lt(v___x_535_, v___x_536_);
if (v___x_538_ == 0)
{
lean_object* v___x_540_; 
lean_dec_ref(v_vs_531_);
if (v_isShared_534_ == 0)
{
lean_ctor_set_tag(v___x_533_, 0);
lean_ctor_set(v___x_533_, 0, v___x_537_);
v___x_540_ = v___x_533_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v___x_537_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
else
{
size_t v___x_542_; size_t v___x_543_; lean_object* v___x_544_; 
lean_del_object(v___x_533_);
v___x_542_ = ((size_t)0ULL);
v___x_543_ = lean_usize_of_nat(v___x_536_);
v___x_544_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(v_vs_531_, v___x_542_, v___x_543_, v___x_537_, v___y_514_);
lean_dec_ref(v_vs_531_);
return v___x_544_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_513_ = stack[0].m_obj;
lean_object* v___y_514_ = stack[1].m_obj;
lean_object* v_res_546_;
v_res_546_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__2(v_x_513_, v___y_514_);
stack->m_obj
 = v_res_546_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__3(lean_object* v_as_547_, size_t v_i_548_, size_t v_stop_549_, lean_object* v_b_550_, lean_object* v___y_551_){
_start:
{
uint8_t v___x_553_; 
v___x_553_ = lean_usize_dec_eq(v_i_548_, v_stop_549_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_554_ = lean_array_uget_borrowed(v_as_547_, v_i_548_);
lean_inc(v___x_554_);
v___x_555_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__2(v___x_554_, v___y_551_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v_a_556_; size_t v___x_557_; size_t v___x_558_; 
v_a_556_ = lean_ctor_get(v___x_555_, 0);
lean_inc(v_a_556_);
lean_dec_ref_known(v___x_555_, 1);
v___x_557_ = ((size_t)1ULL);
v___x_558_ = lean_usize_add(v_i_548_, v___x_557_);
v_i_548_ = v___x_558_;
v_b_550_ = v_a_556_;
goto _start;
}
else
{
return v___x_555_;
}
}
else
{
lean_object* v___x_560_; 
v___x_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_560_, 0, v_b_550_);
return v___x_560_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_547_ = stack[0].m_obj;
size_t v_i_548_ = stack[1].m_num;
size_t v_stop_549_ = stack[2].m_num;
lean_object* v_b_550_ = stack[3].m_obj;
lean_object* v___y_551_ = stack[4].m_obj;
lean_object* v_res_561_;
v_res_561_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__3(v_as_547_, v_i_548_, v_stop_549_, v_b_550_, v___y_551_);
stack->m_obj
 = v_res_561_;
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0(lean_object* v_x_562_, size_t v_x_563_, size_t v_x_564_, lean_object* v___y_565_){
_start:
{
if (lean_obj_tag(v_x_562_) == 0)
{
lean_object* v_cs_567_; lean_object* v___x_568_; size_t v___x_569_; lean_object* v_j_570_; lean_object* v___x_571_; size_t v___x_572_; size_t v___x_573_; size_t v___x_574_; size_t v___x_575_; size_t v___x_576_; size_t v___x_577_; lean_object* v___x_578_; 
v_cs_567_ = lean_ctor_get(v_x_562_, 0);
lean_inc_ref(v_cs_567_);
lean_dec_ref_known(v_x_562_, 1);
v___x_568_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0___closed__0);
v___x_569_ = lean_usize_shift_right(v_x_563_, v_x_564_);
v_j_570_ = lean_usize_to_nat(v___x_569_);
v___x_571_ = lean_array_get_borrowed(v___x_568_, v_cs_567_, v_j_570_);
v___x_572_ = ((size_t)1ULL);
v___x_573_ = lean_usize_shift_left(v___x_572_, v_x_564_);
v___x_574_ = lean_usize_sub(v___x_573_, v___x_572_);
v___x_575_ = lean_usize_land(v_x_563_, v___x_574_);
v___x_576_ = ((size_t)5ULL);
v___x_577_ = lean_usize_sub(v_x_564_, v___x_576_);
lean_inc(v___x_571_);
v___x_578_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0(v___x_571_, v___x_575_, v___x_577_, v___y_565_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_593_; 
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_593_ == 0)
{
lean_object* v_unused_594_; 
v_unused_594_ = lean_ctor_get(v___x_578_, 0);
lean_dec(v_unused_594_);
v___x_580_ = v___x_578_;
v_isShared_581_ = v_isSharedCheck_593_;
goto v_resetjp_579_;
}
else
{
lean_dec(v___x_578_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_593_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; uint8_t v___x_586_; 
v___x_582_ = lean_unsigned_to_nat(1u);
v___x_583_ = lean_nat_add(v_j_570_, v___x_582_);
lean_dec(v_j_570_);
v___x_584_ = lean_array_get_size(v_cs_567_);
v___x_585_ = lean_box(0);
v___x_586_ = lean_nat_dec_lt(v___x_583_, v___x_584_);
if (v___x_586_ == 0)
{
lean_object* v___x_588_; 
lean_dec(v___x_583_);
lean_dec_ref(v_cs_567_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 0, v___x_585_);
v___x_588_ = v___x_580_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_585_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
else
{
size_t v___x_590_; size_t v___x_591_; lean_object* v___x_592_; 
lean_del_object(v___x_580_);
v___x_590_ = lean_usize_of_nat(v___x_583_);
lean_dec(v___x_583_);
v___x_591_ = lean_usize_of_nat(v___x_584_);
v___x_592_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__3(v_cs_567_, v___x_590_, v___x_591_, v___x_585_, v___y_565_);
lean_dec_ref(v_cs_567_);
return v___x_592_;
}
}
}
else
{
lean_dec(v_j_570_);
lean_dec_ref(v_cs_567_);
return v___x_578_;
}
}
else
{
lean_object* v_vs_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_609_; 
v_vs_595_ = lean_ctor_get(v_x_562_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v_x_562_);
if (v_isSharedCheck_609_ == 0)
{
v___x_597_ = v_x_562_;
v_isShared_598_ = v_isSharedCheck_609_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_vs_595_);
lean_dec(v_x_562_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_609_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; uint8_t v___x_602_; 
v___x_599_ = lean_usize_to_nat(v_x_563_);
v___x_600_ = lean_array_get_size(v_vs_595_);
v___x_601_ = lean_box(0);
v___x_602_ = lean_nat_dec_lt(v___x_599_, v___x_600_);
if (v___x_602_ == 0)
{
lean_object* v___x_604_; 
lean_dec(v___x_599_);
lean_dec_ref(v_vs_595_);
if (v_isShared_598_ == 0)
{
lean_ctor_set_tag(v___x_597_, 0);
lean_ctor_set(v___x_597_, 0, v___x_601_);
v___x_604_ = v___x_597_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___x_601_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
else
{
size_t v___x_606_; size_t v___x_607_; lean_object* v___x_608_; 
lean_del_object(v___x_597_);
v___x_606_ = lean_usize_of_nat(v___x_599_);
lean_dec(v___x_599_);
v___x_607_ = lean_usize_of_nat(v___x_600_);
v___x_608_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(v_vs_595_, v___x_606_, v___x_607_, v___x_601_, v___y_565_);
lean_dec_ref(v_vs_595_);
return v___x_608_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_562_ = stack[0].m_obj;
size_t v_x_563_ = stack[1].m_num;
size_t v_x_564_ = stack[2].m_num;
lean_object* v___y_565_ = stack[3].m_obj;
lean_object* v_res_610_;
v_res_610_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0(v_x_562_, v_x_563_, v_x_564_, v___y_565_);
stack->m_obj
 = v_res_610_;
}
lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__2(lean_object* v_t_611_, lean_object* v___y_612_){
_start:
{
lean_object* v_root_614_; lean_object* v_tail_615_; lean_object* v___x_616_; 
v_root_614_ = lean_ctor_get(v_t_611_, 0);
lean_inc_ref(v_root_614_);
v_tail_615_ = lean_ctor_get(v_t_611_, 1);
lean_inc_ref(v_tail_615_);
lean_dec_ref(v_t_611_);
v___x_616_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__2(v_root_614_, v___y_612_);
if (lean_obj_tag(v___x_616_) == 0)
{
lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_630_; 
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_616_);
if (v_isSharedCheck_630_ == 0)
{
lean_object* v_unused_631_; 
v_unused_631_ = lean_ctor_get(v___x_616_, 0);
lean_dec(v_unused_631_);
v___x_618_ = v___x_616_;
v_isShared_619_ = v_isSharedCheck_630_;
goto v_resetjp_617_;
}
else
{
lean_dec(v___x_616_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_630_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; uint8_t v___x_623_; 
v___x_620_ = lean_unsigned_to_nat(0u);
v___x_621_ = lean_array_get_size(v_tail_615_);
v___x_622_ = lean_box(0);
v___x_623_ = lean_nat_dec_lt(v___x_620_, v___x_621_);
if (v___x_623_ == 0)
{
lean_object* v___x_625_; 
lean_dec_ref(v_tail_615_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 0, v___x_622_);
v___x_625_ = v___x_618_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_622_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
else
{
size_t v___x_627_; size_t v___x_628_; lean_object* v___x_629_; 
lean_del_object(v___x_618_);
v___x_627_ = ((size_t)0ULL);
v___x_628_ = lean_usize_of_nat(v___x_621_);
v___x_629_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(v_tail_615_, v___x_627_, v___x_628_, v___x_622_, v___y_612_);
lean_dec_ref(v_tail_615_);
return v___x_629_;
}
}
}
else
{
lean_dec_ref(v_tail_615_);
return v___x_616_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_611_ = stack[0].m_obj;
lean_object* v___y_612_ = stack[1].m_obj;
lean_object* v_res_632_;
v_res_632_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__2(v_t_611_, v___y_612_);
stack->m_obj
 = v_res_632_;
}
lean_object* l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0(lean_object* v_t_633_, lean_object* v_start_634_, lean_object* v___y_635_){
_start:
{
lean_object* v___x_637_; uint8_t v___x_638_; 
v___x_637_ = lean_unsigned_to_nat(0u);
v___x_638_ = lean_nat_dec_eq(v_start_634_, v___x_637_);
if (v___x_638_ == 0)
{
lean_object* v_root_639_; lean_object* v_tail_640_; size_t v_shift_641_; lean_object* v_tailOff_642_; uint8_t v___x_643_; 
v_root_639_ = lean_ctor_get(v_t_633_, 0);
lean_inc_ref(v_root_639_);
v_tail_640_ = lean_ctor_get(v_t_633_, 1);
lean_inc_ref(v_tail_640_);
v_shift_641_ = lean_ctor_get_usize(v_t_633_, 4);
v_tailOff_642_ = lean_ctor_get(v_t_633_, 3);
lean_inc(v_tailOff_642_);
lean_dec_ref(v_t_633_);
v___x_643_ = lean_nat_dec_le(v_tailOff_642_, v_start_634_);
if (v___x_643_ == 0)
{
size_t v___x_644_; lean_object* v___x_645_; 
lean_dec(v_tailOff_642_);
v___x_644_ = lean_usize_of_nat(v_start_634_);
v___x_645_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0(v_root_639_, v___x_644_, v_shift_641_, v___y_635_);
if (lean_obj_tag(v___x_645_) == 0)
{
lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_658_; 
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_658_ == 0)
{
lean_object* v_unused_659_; 
v_unused_659_ = lean_ctor_get(v___x_645_, 0);
lean_dec(v_unused_659_);
v___x_647_ = v___x_645_;
v_isShared_648_ = v_isSharedCheck_658_;
goto v_resetjp_646_;
}
else
{
lean_dec(v___x_645_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_658_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_649_; lean_object* v___x_650_; uint8_t v___x_651_; 
v___x_649_ = lean_array_get_size(v_tail_640_);
v___x_650_ = lean_box(0);
v___x_651_ = lean_nat_dec_lt(v___x_637_, v___x_649_);
if (v___x_651_ == 0)
{
lean_object* v___x_653_; 
lean_dec_ref(v_tail_640_);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 0, v___x_650_);
v___x_653_ = v___x_647_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v___x_650_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
else
{
size_t v___x_655_; size_t v___x_656_; lean_object* v___x_657_; 
lean_del_object(v___x_647_);
v___x_655_ = ((size_t)0ULL);
v___x_656_ = lean_usize_of_nat(v___x_649_);
v___x_657_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(v_tail_640_, v___x_655_, v___x_656_, v___x_650_, v___y_635_);
lean_dec_ref(v_tail_640_);
return v___x_657_;
}
}
}
else
{
lean_dec_ref(v_tail_640_);
return v___x_645_;
}
}
else
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; uint8_t v___x_663_; 
lean_dec_ref(v_root_639_);
v___x_660_ = lean_nat_sub(v_start_634_, v_tailOff_642_);
lean_dec(v_tailOff_642_);
v___x_661_ = lean_array_get_size(v_tail_640_);
v___x_662_ = lean_box(0);
v___x_663_ = lean_nat_dec_lt(v___x_660_, v___x_661_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; 
lean_dec(v___x_660_);
lean_dec_ref(v_tail_640_);
v___x_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_664_, 0, v___x_662_);
return v___x_664_;
}
else
{
size_t v___x_665_; size_t v___x_666_; lean_object* v___x_667_; 
v___x_665_ = lean_usize_of_nat(v___x_660_);
lean_dec(v___x_660_);
v___x_666_ = lean_usize_of_nat(v___x_661_);
v___x_667_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(v_tail_640_, v___x_665_, v___x_666_, v___x_662_, v___y_635_);
lean_dec_ref(v_tail_640_);
return v___x_667_;
}
}
}
else
{
lean_object* v___x_668_; 
v___x_668_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__2(v_t_633_, v___y_635_);
return v___x_668_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_633_ = stack[0].m_obj;
lean_object* v_start_634_ = stack[1].m_obj;
lean_object* v___y_635_ = stack[2].m_obj;
lean_object* v_res_669_;
v_res_669_ = l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0(v_t_633_, v_start_634_, v___y_635_);
stack->m_obj
 = v_res_669_;
}
lean_object* l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList(lean_object* v_trees_670_, lean_object* v_a_671_){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = lean_unsigned_to_nat(0u);
v___x_674_ = l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0(v_trees_670_, v___x_673_, v_a_671_);
return v___x_674_;
}
}
LEAN_EXPORT void l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_0interp(lean_interpreter_value* stack)
{
lean_object* v_trees_670_ = stack[0].m_obj;
lean_object* v_a_671_ = stack[1].m_obj;
lean_object* v_res_675_;
v_res_675_ = l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList(v_trees_670_, v_a_671_);
stack->m_obj
 = v_res_675_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList___boxed(lean_object* v_trees_676_, lean_object* v_a_677_, lean_object* v_a_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList(v_trees_676_, v_a_677_);
lean_dec(v_a_677_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1___boxed(lean_object* v_as_680_, lean_object* v_i_681_, lean_object* v_stop_682_, lean_object* v_b_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
size_t v_i_boxed_686_; size_t v_stop_boxed_687_; lean_object* v_res_688_; 
v_i_boxed_686_ = lean_unbox_usize(v_i_681_);
lean_dec(v_i_681_);
v_stop_boxed_687_ = lean_unbox_usize(v_stop_682_);
lean_dec(v_stop_682_);
v_res_688_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(v_as_680_, v_i_boxed_686_, v_stop_boxed_687_, v_b_683_, v___y_684_);
lean_dec(v___y_684_);
lean_dec_ref(v_as_680_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__3___boxed(lean_object* v_as_689_, lean_object* v_i_690_, lean_object* v_stop_691_, lean_object* v_b_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
size_t v_i_boxed_695_; size_t v_stop_boxed_696_; lean_object* v_res_697_; 
v_i_boxed_695_ = lean_unbox_usize(v_i_690_);
lean_dec(v_i_690_);
v_stop_boxed_696_ = lean_unbox_usize(v_stop_691_);
lean_dec(v_stop_691_);
v_res_697_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__3(v_as_689_, v_i_boxed_695_, v_stop_boxed_696_, v_b_692_, v___y_693_);
lean_dec(v___y_693_);
lean_dec_ref(v_as_689_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__2___boxed(lean_object* v_t_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__2(v_t_698_, v___y_699_);
lean_dec(v___y_699_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__2___boxed(lean_object* v_x_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__2(v_x_702_, v___y_703_);
lean_dec(v___y_703_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics___boxed(lean_object* v_x_706_, lean_object* v_a_707_, lean_object* v_a_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics(v_x_706_, v_a_707_);
lean_dec(v_a_707_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0___boxed(lean_object* v_t_710_, lean_object* v_start_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0(v_t_710_, v_start_711_, v___y_712_);
lean_dec(v___y_712_);
lean_dec(v_start_711_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0___boxed(lean_object* v_x_715_, lean_object* v_x_716_, lean_object* v_x_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
size_t v_x_2433__boxed_720_; size_t v_x_2434__boxed_721_; lean_object* v_res_722_; 
v_x_2433__boxed_720_ = lean_unbox_usize(v_x_716_);
lean_dec(v_x_716_);
v_x_2434__boxed_721_ = lean_unbox_usize(v_x_717_);
lean_dec(v_x_717_);
v_res_722_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0(v_x_715_, v_x_2433__boxed_720_, v_x_2434__boxed_721_, v___y_718_);
lean_dec(v___y_718_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2(lean_object* v_00_u03b2_723_, lean_object* v_m_724_, lean_object* v_a_725_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2___redArg(v_m_724_, v_a_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2___boxed(lean_object* v_00_u03b2_727_, lean_object* v_m_728_, lean_object* v_a_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2(v_00_u03b2_727_, v_m_728_, v_a_729_);
lean_dec_ref(v_a_729_);
return v_res_730_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5(lean_object* v_00_u03b2_731_, lean_object* v_a_732_, lean_object* v_x_733_){
_start:
{
uint8_t v___x_734_; 
v___x_734_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5___redArg(v_a_732_, v_x_733_);
return v___x_734_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_732_ = stack[1].m_obj;
lean_object* v_x_733_ = stack[2].m_obj;
uint8_t v_res_735_;
v_res_735_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5(lean_box(0), v_a_732_, v_x_733_);
stack->m_num = v_res_735_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5___boxed(lean_object* v_00_u03b2_736_, lean_object* v_a_737_, lean_object* v_x_738_){
_start:
{
uint8_t v_res_739_; lean_object* v_r_740_; 
v_res_739_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5(v_00_u03b2_736_, v_a_737_, v_x_738_);
lean_dec(v_x_738_);
lean_dec_ref(v_a_737_);
v_r_740_ = lean_box(v_res_739_);
return v_r_740_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__6(lean_object* v_00_u03b2_741_, lean_object* v_a_742_, lean_object* v_x_743_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__6___redArg(v_a_742_, v_x_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__6___boxed(lean_object* v_00_u03b2_745_, lean_object* v_a_746_, lean_object* v_x_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__6(v_00_u03b2_745_, v_a_746_, v_x_747_);
lean_dec_ref(v_a_746_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__0(lean_object* v_a_749_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = lean_nat_to_int(v_a_749_);
return v___x_750_;
}
}
lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___redArg(lean_object* v___y_751_){
_start:
{
lean_object* v___x_753_; lean_object* v_infoState_754_; lean_object* v_trees_755_; lean_object* v___x_756_; 
v___x_753_ = lean_st_ref_get(v___y_751_);
v_infoState_754_ = lean_ctor_get(v___x_753_, 8);
lean_inc_ref(v_infoState_754_);
lean_dec(v___x_753_);
v_trees_755_ = lean_ctor_get(v_infoState_754_, 2);
lean_inc_ref(v_trees_755_);
lean_dec_ref(v_infoState_754_);
v___x_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_756_, 0, v_trees_755_);
return v___x_756_;
}
}
LEAN_EXPORT void l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_751_ = stack[0].m_obj;
lean_object* v_res_757_;
v_res_757_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___redArg(v___y_751_);
stack->m_obj
 = v_res_757_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___redArg___boxed(lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___redArg(v___y_758_);
lean_dec(v___y_758_);
return v_res_760_;
}
}
lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5(lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___redArg(v___y_762_);
return v___x_764_;
}
}
LEAN_EXPORT void l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_761_ = stack[0].m_obj;
lean_object* v___y_762_ = stack[1].m_obj;
lean_object* v_res_765_;
v_res_765_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5(v___y_761_, v___y_762_);
stack->m_obj
 = v_res_765_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___boxed(lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5(v___y_766_, v___y_767_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8(lean_object* v_x_770_, lean_object* v_x_771_){
_start:
{
if (lean_obj_tag(v_x_771_) == 0)
{
return v_x_770_;
}
else
{
lean_object* v_key_772_; lean_object* v_value_773_; lean_object* v_tail_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v_key_772_ = lean_ctor_get(v_x_771_, 0);
v_value_773_ = lean_ctor_get(v_x_771_, 1);
v_tail_774_ = lean_ctor_get(v_x_771_, 2);
lean_inc(v_value_773_);
lean_inc(v_key_772_);
v___x_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_775_, 0, v_key_772_);
lean_ctor_set(v___x_775_, 1, v_value_773_);
v___x_776_ = lean_array_push(v_x_770_, v___x_775_);
v_x_770_ = v___x_776_;
v_x_771_ = v_tail_774_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8___boxed(lean_object* v_x_778_, lean_object* v_x_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8(v_x_778_, v_x_779_);
lean_dec(v_x_779_);
return v_res_780_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9(lean_object* v_as_781_, size_t v_i_782_, size_t v_stop_783_, lean_object* v_b_784_){
_start:
{
uint8_t v___x_785_; 
v___x_785_ = lean_usize_dec_eq(v_i_782_, v_stop_783_);
if (v___x_785_ == 0)
{
lean_object* v___x_786_; lean_object* v___x_787_; size_t v___x_788_; size_t v___x_789_; 
v___x_786_ = lean_array_uget_borrowed(v_as_781_, v_i_782_);
v___x_787_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8(v_b_784_, v___x_786_);
v___x_788_ = ((size_t)1ULL);
v___x_789_ = lean_usize_add(v_i_782_, v___x_788_);
v_i_782_ = v___x_789_;
v_b_784_ = v___x_787_;
goto _start;
}
else
{
return v_b_784_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_781_ = stack[0].m_obj;
size_t v_i_782_ = stack[1].m_num;
size_t v_stop_783_ = stack[2].m_num;
lean_object* v_b_784_ = stack[3].m_obj;
lean_object* v_res_791_;
v_res_791_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9(v_as_781_, v_i_782_, v_stop_783_, v_b_784_);
stack->m_obj
 = v_res_791_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9___boxed(lean_object* v_as_792_, lean_object* v_i_793_, lean_object* v_stop_794_, lean_object* v_b_795_){
_start:
{
size_t v_i_boxed_796_; size_t v_stop_boxed_797_; lean_object* v_res_798_; 
v_i_boxed_796_ = lean_unbox_usize(v_i_793_);
lean_dec(v_i_793_);
v_stop_boxed_797_ = lean_unbox_usize(v_stop_794_);
lean_dec(v_stop_794_);
v_res_798_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9(v_as_792_, v_i_boxed_796_, v_stop_boxed_797_, v_b_795_);
lean_dec_ref(v_as_792_);
return v_res_798_;
}
}
lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1___redArg(lean_object* v_o_799_, lean_object* v___y_800_){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v_env_804_; lean_object* v___x_805_; lean_object* v_toEnvExtension_806_; lean_object* v_asyncMode_807_; lean_object* v___x_808_; uint8_t v___x_809_; lean_object* v___x_810_; lean_object* v_merged_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_819_; 
v___x_802_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_803_ = lean_st_ref_get(v___y_800_);
v_env_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc_ref(v_env_804_);
lean_dec(v___x_803_);
v___x_805_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_806_ = lean_ctor_get(v___x_805_, 0);
v_asyncMode_807_ = lean_ctor_get(v_toEnvExtension_806_, 2);
v___x_808_ = lean_box(0);
v___x_809_ = 0;
v___x_810_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_802_, v___x_805_, v_env_804_, v_asyncMode_807_, v___x_808_, v___x_809_);
v_merged_811_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_819_ == 0)
{
lean_object* v_unused_820_; 
v_unused_820_ = lean_ctor_get(v___x_810_, 1);
lean_dec(v_unused_820_);
v___x_813_ = v___x_810_;
v_isShared_814_ = v_isSharedCheck_819_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_merged_811_);
lean_dec(v___x_810_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_819_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_816_; 
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 1, v_merged_811_);
lean_ctor_set(v___x_813_, 0, v_o_799_);
v___x_816_ = v___x_813_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_o_799_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v_merged_811_);
v___x_816_ = v_reuseFailAlloc_818_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
lean_object* v___x_817_; 
v___x_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_817_, 0, v___x_816_);
return v___x_817_;
}
}
}
}
LEAN_EXPORT void l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_799_ = stack[0].m_obj;
lean_object* v___y_800_ = stack[1].m_obj;
lean_object* v_res_821_;
v_res_821_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1___redArg(v_o_799_, v___y_800_);
stack->m_obj
 = v_res_821_;
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1___redArg___boxed(lean_object* v_o_822_, lean_object* v___y_823_, lean_object* v___y_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1___redArg(v_o_822_, v___y_823_);
lean_dec(v___y_823_);
return v_res_825_;
}
}
lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1(lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v_scopes_831_; lean_object* v___x_832_; lean_object* v_opts_833_; lean_object* v___x_834_; 
v___x_829_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_830_ = lean_st_ref_get(v___y_827_);
v_scopes_831_ = lean_ctor_get(v___x_830_, 2);
lean_inc(v_scopes_831_);
lean_dec(v___x_830_);
v___x_832_ = l_List_head_x21___redArg(v___x_829_, v_scopes_831_);
lean_dec(v_scopes_831_);
v_opts_833_ = lean_ctor_get(v___x_832_, 1);
lean_inc_ref(v_opts_833_);
lean_dec(v___x_832_);
v___x_834_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1___redArg(v_opts_833_, v___y_827_);
return v___x_834_;
}
}
LEAN_EXPORT void l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_826_ = stack[0].m_obj;
lean_object* v___y_827_ = stack[1].m_obj;
lean_object* v_res_835_;
v_res_835_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1(v___y_826_, v___y_827_);
stack->m_obj
 = v_res_835_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1___boxed(lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1(v___y_836_, v___y_837_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___lam__0(lean_object* v_r_840_){
_start:
{
lean_object* v_start_841_; lean_object* v_stop_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_851_; 
v_start_841_ = lean_ctor_get(v_r_840_, 0);
v_stop_842_ = lean_ctor_get(v_r_840_, 1);
v_isSharedCheck_851_ = !lean_is_exclusive(v_r_840_);
if (v_isSharedCheck_851_ == 0)
{
v___x_844_ = v_r_840_;
v_isShared_845_ = v_isSharedCheck_851_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_stop_842_);
lean_inc(v_start_841_);
lean_dec(v_r_840_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_851_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_849_; 
v___x_846_ = lean_nat_to_int(v_stop_842_);
v___x_847_ = lean_int_neg(v___x_846_);
lean_dec(v___x_846_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 1, v___x_847_);
v___x_849_ = v___x_844_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_start_841_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v___x_847_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___lam__1(lean_object* v___f_852_, lean_object* v___f_853_, lean_object* v___f_854_, uint8_t v___x_855_, lean_object* v_x1_856_, lean_object* v_x2_857_){
_start:
{
lean_object* v_fst_858_; lean_object* v_fst_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_11062__overap_862_; lean_object* v___x_863_; uint8_t v___x_864_; 
v_fst_858_ = lean_ctor_get(v_x1_856_, 0);
lean_inc(v_fst_858_);
lean_dec_ref(v_x1_856_);
v_fst_859_ = lean_ctor_get(v_x2_857_, 0);
lean_inc(v_fst_859_);
lean_dec_ref(v_x2_857_);
lean_inc_ref(v___f_852_);
v___x_860_ = lean_apply_1(v___f_852_, v_fst_858_);
v___x_861_ = lean_apply_1(v___f_852_, v_fst_859_);
v___x_11062__overap_862_ = l_lexOrd___redArg(v___f_853_, v___f_854_);
v___x_863_ = lean_apply_2(v___x_11062__overap_862_, v___x_860_, v___x_861_);
v___x_864_ = lean_unbox(v___x_863_);
if (v___x_864_ == 0)
{
return v___x_855_;
}
else
{
uint8_t v___x_865_; 
v___x_865_ = 0;
return v___x_865_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_852_ = stack[0].m_obj;
lean_object* v___f_853_ = stack[1].m_obj;
lean_object* v___f_854_ = stack[2].m_obj;
uint8_t v___x_855_ = stack[3].m_num;
lean_object* v_x1_856_ = stack[4].m_obj;
lean_object* v_x2_857_ = stack[5].m_obj;
uint8_t v_res_866_;
v_res_866_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___lam__1(v___f_852_, v___f_853_, v___f_854_, v___x_855_, v_x1_856_, v_x2_857_);
stack->m_num = v_res_866_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___lam__1___boxed(lean_object* v___f_867_, lean_object* v___f_868_, lean_object* v___f_869_, lean_object* v___x_870_, lean_object* v_x1_871_, lean_object* v_x2_872_){
_start:
{
uint8_t v___x_11271__boxed_873_; uint8_t v_res_874_; lean_object* v_r_875_; 
v___x_11271__boxed_873_ = lean_unbox(v___x_870_);
v_res_874_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___lam__1(v___f_867_, v___f_868_, v___f_869_, v___x_11271__boxed_873_, v_x1_871_, v_x2_872_);
v_r_875_ = lean_box(v_res_874_);
return v_r_875_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7_spec__11___redArg(lean_object* v_hi_878_, lean_object* v_pivot_879_, lean_object* v_as_880_, lean_object* v_i_881_, lean_object* v_k_882_){
_start:
{
uint8_t v___x_887_; 
v___x_887_ = lean_nat_dec_lt(v_k_882_, v_hi_878_);
if (v___x_887_ == 0)
{
lean_object* v___x_888_; lean_object* v___x_889_; 
lean_dec(v_k_882_);
lean_dec_ref(v_pivot_879_);
v___x_888_ = lean_array_fswap(v_as_880_, v_i_881_, v_hi_878_);
v___x_889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_889_, 0, v_i_881_);
lean_ctor_set(v___x_889_, 1, v___x_888_);
return v___x_889_;
}
else
{
lean_object* v___x_890_; lean_object* v_fst_891_; lean_object* v_fst_892_; lean_object* v___f_893_; lean_object* v___f_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_10790__overap_897_; lean_object* v___x_898_; uint8_t v___x_899_; 
v___x_890_ = lean_array_fget_borrowed(v_as_880_, v_k_882_);
v_fst_891_ = lean_ctor_get(v___x_890_, 0);
v_fst_892_ = lean_ctor_get(v_pivot_879_, 0);
v___f_893_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7_spec__11___redArg___closed__0));
v___f_894_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7_spec__11___redArg___closed__1));
lean_inc(v_fst_891_);
v___x_895_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___lam__0(v_fst_891_);
lean_inc(v_fst_892_);
v___x_896_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___lam__0(v_fst_892_);
v___x_10790__overap_897_ = l_lexOrd___redArg(v___f_893_, v___f_894_);
v___x_898_ = lean_apply_2(v___x_10790__overap_897_, v___x_895_, v___x_896_);
v___x_899_ = lean_unbox(v___x_898_);
if (v___x_899_ == 0)
{
if (v___x_887_ == 0)
{
goto v___jp_883_;
}
else
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_900_ = lean_array_fswap(v_as_880_, v_i_881_, v_k_882_);
v___x_901_ = lean_unsigned_to_nat(1u);
v___x_902_ = lean_nat_add(v_i_881_, v___x_901_);
lean_dec(v_i_881_);
v___x_903_ = lean_nat_add(v_k_882_, v___x_901_);
lean_dec(v_k_882_);
v_as_880_ = v___x_900_;
v_i_881_ = v___x_902_;
v_k_882_ = v___x_903_;
goto _start;
}
}
else
{
goto v___jp_883_;
}
}
v___jp_883_:
{
lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_884_ = lean_unsigned_to_nat(1u);
v___x_885_ = lean_nat_add(v_k_882_, v___x_884_);
lean_dec(v_k_882_);
v_k_882_ = v___x_885_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7_spec__11___redArg___boxed(lean_object* v_hi_905_, lean_object* v_pivot_906_, lean_object* v_as_907_, lean_object* v_i_908_, lean_object* v_k_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7_spec__11___redArg(v_hi_905_, v_pivot_906_, v_as_907_, v_i_908_, v_k_909_);
lean_dec(v_hi_905_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg(lean_object* v_n_912_, lean_object* v_as_913_, lean_object* v_lo_914_, lean_object* v_hi_915_){
_start:
{
lean_object* v___y_917_; uint8_t v___x_927_; 
v___x_927_ = lean_nat_dec_lt(v_lo_914_, v_hi_915_);
if (v___x_927_ == 0)
{
lean_dec(v_lo_914_);
return v_as_913_;
}
else
{
lean_object* v___f_928_; lean_object* v___f_929_; lean_object* v___f_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v_mid_933_; lean_object* v___y_935_; lean_object* v___y_941_; lean_object* v___x_946_; lean_object* v___x_947_; uint8_t v___x_948_; 
v___f_928_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___closed__0));
v___f_929_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7_spec__11___redArg___closed__0));
v___f_930_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7_spec__11___redArg___closed__1));
v___x_931_ = lean_nat_add(v_lo_914_, v_hi_915_);
v___x_932_ = lean_unsigned_to_nat(1u);
v_mid_933_ = lean_nat_shiftr(v___x_931_, v___x_932_);
lean_dec(v___x_931_);
v___x_946_ = lean_array_fget_borrowed(v_as_913_, v_mid_933_);
v___x_947_ = lean_array_fget_borrowed(v_as_913_, v_lo_914_);
lean_inc(v___x_947_);
lean_inc(v___x_946_);
v___x_948_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___lam__1(v___f_928_, v___f_929_, v___f_930_, v___x_927_, v___x_946_, v___x_947_);
if (v___x_948_ == 0)
{
v___y_941_ = v_as_913_;
goto v___jp_940_;
}
else
{
lean_object* v___x_949_; 
v___x_949_ = lean_array_fswap(v_as_913_, v_lo_914_, v_mid_933_);
v___y_941_ = v___x_949_;
goto v___jp_940_;
}
v___jp_934_:
{
lean_object* v___x_936_; lean_object* v___x_937_; uint8_t v___x_938_; 
v___x_936_ = lean_array_fget_borrowed(v___y_935_, v_mid_933_);
v___x_937_ = lean_array_fget_borrowed(v___y_935_, v_hi_915_);
lean_inc(v___x_937_);
lean_inc(v___x_936_);
v___x_938_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___lam__1(v___f_928_, v___f_929_, v___f_930_, v___x_927_, v___x_936_, v___x_937_);
if (v___x_938_ == 0)
{
lean_dec(v_mid_933_);
v___y_917_ = v___y_935_;
goto v___jp_916_;
}
else
{
lean_object* v___x_939_; 
v___x_939_ = lean_array_fswap(v___y_935_, v_mid_933_, v_hi_915_);
lean_dec(v_mid_933_);
v___y_917_ = v___x_939_;
goto v___jp_916_;
}
}
v___jp_940_:
{
lean_object* v___x_942_; lean_object* v___x_943_; uint8_t v___x_944_; 
v___x_942_ = lean_array_fget_borrowed(v___y_941_, v_hi_915_);
v___x_943_ = lean_array_fget_borrowed(v___y_941_, v_lo_914_);
lean_inc(v___x_943_);
lean_inc(v___x_942_);
v___x_944_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___lam__1(v___f_928_, v___f_929_, v___f_930_, v___x_927_, v___x_942_, v___x_943_);
if (v___x_944_ == 0)
{
v___y_935_ = v___y_941_;
goto v___jp_934_;
}
else
{
lean_object* v___x_945_; 
v___x_945_ = lean_array_fswap(v___y_941_, v_lo_914_, v_hi_915_);
v___y_935_ = v___x_945_;
goto v___jp_934_;
}
}
}
v___jp_916_:
{
lean_object* v_pivot_918_; lean_object* v___x_919_; lean_object* v_fst_920_; lean_object* v_snd_921_; uint8_t v___x_922_; 
v_pivot_918_ = lean_array_fget(v___y_917_, v_hi_915_);
lean_inc_n(v_lo_914_, 2);
v___x_919_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7_spec__11___redArg(v_hi_915_, v_pivot_918_, v___y_917_, v_lo_914_, v_lo_914_);
v_fst_920_ = lean_ctor_get(v___x_919_, 0);
lean_inc(v_fst_920_);
v_snd_921_ = lean_ctor_get(v___x_919_, 1);
lean_inc(v_snd_921_);
lean_dec_ref(v___x_919_);
v___x_922_ = lean_nat_dec_le(v_hi_915_, v_fst_920_);
if (v___x_922_ == 0)
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_923_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg(v_n_912_, v_snd_921_, v_lo_914_, v_fst_920_);
v___x_924_ = lean_unsigned_to_nat(1u);
v___x_925_ = lean_nat_add(v_fst_920_, v___x_924_);
lean_dec(v_fst_920_);
v_as_913_ = v___x_923_;
v_lo_914_ = v___x_925_;
goto _start;
}
else
{
lean_dec(v_fst_920_);
lean_dec(v_lo_914_);
return v_snd_921_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg___boxed(lean_object* v_n_950_, lean_object* v_as_951_, lean_object* v_lo_952_, lean_object* v_hi_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg(v_n_950_, v_as_951_, v_lo_952_, v_hi_953_);
lean_dec(v_hi_953_);
lean_dec(v_n_950_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19_spec__21_spec__25___redArg(lean_object* v_x_955_, lean_object* v_x_956_){
_start:
{
if (lean_obj_tag(v_x_956_) == 0)
{
return v_x_955_;
}
else
{
lean_object* v_key_957_; lean_object* v_value_958_; lean_object* v_tail_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_982_; 
v_key_957_ = lean_ctor_get(v_x_956_, 0);
v_value_958_ = lean_ctor_get(v_x_956_, 1);
v_tail_959_ = lean_ctor_get(v_x_956_, 2);
v_isSharedCheck_982_ = !lean_is_exclusive(v_x_956_);
if (v_isSharedCheck_982_ == 0)
{
v___x_961_ = v_x_956_;
v_isShared_962_ = v_isSharedCheck_982_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_tail_959_);
lean_inc(v_value_958_);
lean_inc(v_key_957_);
lean_dec(v_x_956_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_982_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_963_; uint64_t v___x_964_; uint64_t v___x_965_; uint64_t v___x_966_; uint64_t v_fold_967_; uint64_t v___x_968_; uint64_t v___x_969_; uint64_t v___x_970_; size_t v___x_971_; size_t v___x_972_; size_t v___x_973_; size_t v___x_974_; size_t v___x_975_; lean_object* v___x_976_; lean_object* v___x_978_; 
v___x_963_ = lean_array_get_size(v_x_955_);
v___x_964_ = l_Lean_Syntax_instHashableRange_hash(v_key_957_);
v___x_965_ = 32ULL;
v___x_966_ = lean_uint64_shift_right(v___x_964_, v___x_965_);
v_fold_967_ = lean_uint64_xor(v___x_964_, v___x_966_);
v___x_968_ = 16ULL;
v___x_969_ = lean_uint64_shift_right(v_fold_967_, v___x_968_);
v___x_970_ = lean_uint64_xor(v_fold_967_, v___x_969_);
v___x_971_ = lean_uint64_to_usize(v___x_970_);
v___x_972_ = lean_usize_of_nat(v___x_963_);
v___x_973_ = ((size_t)1ULL);
v___x_974_ = lean_usize_sub(v___x_972_, v___x_973_);
v___x_975_ = lean_usize_land(v___x_971_, v___x_974_);
v___x_976_ = lean_array_uget_borrowed(v_x_955_, v___x_975_);
lean_inc(v___x_976_);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 2, v___x_976_);
v___x_978_ = v___x_961_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_key_957_);
lean_ctor_set(v_reuseFailAlloc_981_, 1, v_value_958_);
lean_ctor_set(v_reuseFailAlloc_981_, 2, v___x_976_);
v___x_978_ = v_reuseFailAlloc_981_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
lean_object* v___x_979_; 
v___x_979_ = lean_array_uset(v_x_955_, v___x_975_, v___x_978_);
v_x_955_ = v___x_979_;
v_x_956_ = v_tail_959_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19_spec__21___redArg(lean_object* v_i_983_, lean_object* v_source_984_, lean_object* v_target_985_){
_start:
{
lean_object* v___x_986_; uint8_t v___x_987_; 
v___x_986_ = lean_array_get_size(v_source_984_);
v___x_987_ = lean_nat_dec_lt(v_i_983_, v___x_986_);
if (v___x_987_ == 0)
{
lean_dec_ref(v_source_984_);
lean_dec(v_i_983_);
return v_target_985_;
}
else
{
lean_object* v_es_988_; lean_object* v___x_989_; lean_object* v_source_990_; lean_object* v_target_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v_es_988_ = lean_array_fget(v_source_984_, v_i_983_);
v___x_989_ = lean_box(0);
v_source_990_ = lean_array_fset(v_source_984_, v_i_983_, v___x_989_);
v_target_991_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19_spec__21_spec__25___redArg(v_target_985_, v_es_988_);
v___x_992_ = lean_unsigned_to_nat(1u);
v___x_993_ = lean_nat_add(v_i_983_, v___x_992_);
lean_dec(v_i_983_);
v_i_983_ = v___x_993_;
v_source_984_ = v_source_990_;
v_target_985_ = v_target_991_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19___redArg(lean_object* v_data_995_){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v_nbuckets_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_996_ = lean_array_get_size(v_data_995_);
v___x_997_ = lean_unsigned_to_nat(2u);
v_nbuckets_998_ = lean_nat_mul(v___x_996_, v___x_997_);
v___x_999_ = lean_unsigned_to_nat(0u);
v___x_1000_ = lean_box(0);
v___x_1001_ = lean_mk_array(v_nbuckets_998_, v___x_1000_);
v___x_1002_ = lean_array_propagate_mark(v_data_995_, v___x_1001_);
v___x_1003_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19_spec__21___redArg(v___x_999_, v_data_995_, v___x_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__20___redArg(lean_object* v_a_1004_, lean_object* v_b_1005_, lean_object* v_x_1006_){
_start:
{
if (lean_obj_tag(v_x_1006_) == 0)
{
lean_dec(v_b_1005_);
lean_dec_ref(v_a_1004_);
return v_x_1006_;
}
else
{
lean_object* v_key_1007_; lean_object* v_value_1008_; lean_object* v_tail_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1021_; 
v_key_1007_ = lean_ctor_get(v_x_1006_, 0);
v_value_1008_ = lean_ctor_get(v_x_1006_, 1);
v_tail_1009_ = lean_ctor_get(v_x_1006_, 2);
v_isSharedCheck_1021_ = !lean_is_exclusive(v_x_1006_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1011_ = v_x_1006_;
v_isShared_1012_ = v_isSharedCheck_1021_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_tail_1009_);
lean_inc(v_value_1008_);
lean_inc(v_key_1007_);
lean_dec(v_x_1006_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1021_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
uint8_t v___x_1013_; 
v___x_1013_ = l_Lean_Syntax_instBEqRange_beq(v_key_1007_, v_a_1004_);
if (v___x_1013_ == 0)
{
lean_object* v___x_1014_; lean_object* v___x_1016_; 
v___x_1014_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__20___redArg(v_a_1004_, v_b_1005_, v_tail_1009_);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 2, v___x_1014_);
v___x_1016_ = v___x_1011_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_key_1007_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v_value_1008_);
lean_ctor_set(v_reuseFailAlloc_1017_, 2, v___x_1014_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
else
{
lean_object* v___x_1019_; 
lean_dec(v_value_1008_);
lean_dec(v_key_1007_);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 1, v_b_1005_);
lean_ctor_set(v___x_1011_, 0, v_a_1004_);
v___x_1019_ = v___x_1011_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_a_1004_);
lean_ctor_set(v_reuseFailAlloc_1020_, 1, v_b_1005_);
lean_ctor_set(v_reuseFailAlloc_1020_, 2, v_tail_1009_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15___redArg(lean_object* v_m_1022_, lean_object* v_a_1023_, lean_object* v_b_1024_){
_start:
{
lean_object* v_size_1025_; lean_object* v_buckets_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1069_; 
v_size_1025_ = lean_ctor_get(v_m_1022_, 0);
v_buckets_1026_ = lean_ctor_get(v_m_1022_, 1);
v_isSharedCheck_1069_ = !lean_is_exclusive(v_m_1022_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1028_ = v_m_1022_;
v_isShared_1029_ = v_isSharedCheck_1069_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_buckets_1026_);
lean_inc(v_size_1025_);
lean_dec(v_m_1022_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1069_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1030_; uint64_t v___x_1031_; uint64_t v___x_1032_; uint64_t v___x_1033_; uint64_t v_fold_1034_; uint64_t v___x_1035_; uint64_t v___x_1036_; uint64_t v___x_1037_; size_t v___x_1038_; size_t v___x_1039_; size_t v___x_1040_; size_t v___x_1041_; size_t v___x_1042_; lean_object* v_bkt_1043_; uint8_t v___x_1044_; 
v___x_1030_ = lean_array_get_size(v_buckets_1026_);
v___x_1031_ = l_Lean_Syntax_instHashableRange_hash(v_a_1023_);
v___x_1032_ = 32ULL;
v___x_1033_ = lean_uint64_shift_right(v___x_1031_, v___x_1032_);
v_fold_1034_ = lean_uint64_xor(v___x_1031_, v___x_1033_);
v___x_1035_ = 16ULL;
v___x_1036_ = lean_uint64_shift_right(v_fold_1034_, v___x_1035_);
v___x_1037_ = lean_uint64_xor(v_fold_1034_, v___x_1036_);
v___x_1038_ = lean_uint64_to_usize(v___x_1037_);
v___x_1039_ = lean_usize_of_nat(v___x_1030_);
v___x_1040_ = ((size_t)1ULL);
v___x_1041_ = lean_usize_sub(v___x_1039_, v___x_1040_);
v___x_1042_ = lean_usize_land(v___x_1038_, v___x_1041_);
v_bkt_1043_ = lean_array_uget_borrowed(v_buckets_1026_, v___x_1042_);
v___x_1044_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5___redArg(v_a_1023_, v_bkt_1043_);
if (v___x_1044_ == 0)
{
lean_object* v___x_1045_; lean_object* v_size_x27_1046_; lean_object* v___x_1047_; lean_object* v_buckets_x27_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; uint8_t v___x_1054_; 
v___x_1045_ = lean_unsigned_to_nat(1u);
v_size_x27_1046_ = lean_nat_add(v_size_1025_, v___x_1045_);
lean_dec(v_size_1025_);
lean_inc(v_bkt_1043_);
v___x_1047_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1047_, 0, v_a_1023_);
lean_ctor_set(v___x_1047_, 1, v_b_1024_);
lean_ctor_set(v___x_1047_, 2, v_bkt_1043_);
v_buckets_x27_1048_ = lean_array_uset(v_buckets_1026_, v___x_1042_, v___x_1047_);
v___x_1049_ = lean_unsigned_to_nat(4u);
v___x_1050_ = lean_nat_mul(v_size_x27_1046_, v___x_1049_);
v___x_1051_ = lean_unsigned_to_nat(3u);
v___x_1052_ = lean_nat_div(v___x_1050_, v___x_1051_);
lean_dec(v___x_1050_);
v___x_1053_ = lean_array_get_size(v_buckets_x27_1048_);
v___x_1054_ = lean_nat_dec_le(v___x_1052_, v___x_1053_);
lean_dec(v___x_1052_);
if (v___x_1054_ == 0)
{
lean_object* v_val_1055_; lean_object* v___x_1057_; 
v_val_1055_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19___redArg(v_buckets_x27_1048_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 1, v_val_1055_);
lean_ctor_set(v___x_1028_, 0, v_size_x27_1046_);
v___x_1057_ = v___x_1028_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_size_x27_1046_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v_val_1055_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
else
{
lean_object* v___x_1060_; 
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 1, v_buckets_x27_1048_);
lean_ctor_set(v___x_1028_, 0, v_size_x27_1046_);
v___x_1060_ = v___x_1028_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_size_x27_1046_);
lean_ctor_set(v_reuseFailAlloc_1061_, 1, v_buckets_x27_1048_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
else
{
lean_object* v___x_1062_; lean_object* v_buckets_x27_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1067_; 
lean_inc(v_bkt_1043_);
v___x_1062_ = lean_box(0);
v_buckets_x27_1063_ = lean_array_uset(v_buckets_1026_, v___x_1042_, v___x_1062_);
v___x_1064_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__20___redArg(v_a_1023_, v_b_1024_, v_bkt_1043_);
v___x_1065_ = lean_array_uset(v_buckets_x27_1063_, v___x_1042_, v___x_1064_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 1, v___x_1065_);
v___x_1067_ = v___x_1028_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_size_1025_);
lean_ctor_set(v_reuseFailAlloc_1068_, 1, v___x_1065_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4_spec__7_spec__11___redArg(lean_object* v_keys_1070_, lean_object* v_i_1071_, lean_object* v_k_1072_){
_start:
{
lean_object* v___x_1073_; uint8_t v___x_1074_; 
v___x_1073_ = lean_array_get_size(v_keys_1070_);
v___x_1074_ = lean_nat_dec_lt(v_i_1071_, v___x_1073_);
if (v___x_1074_ == 0)
{
lean_dec(v_i_1071_);
return v___x_1074_;
}
else
{
lean_object* v_k_x27_1075_; uint8_t v___x_1076_; 
v_k_x27_1075_ = lean_array_fget_borrowed(v_keys_1070_, v_i_1071_);
v___x_1076_ = lean_name_eq(v_k_1072_, v_k_x27_1075_);
if (v___x_1076_ == 0)
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = lean_unsigned_to_nat(1u);
v___x_1078_ = lean_nat_add(v_i_1071_, v___x_1077_);
lean_dec(v_i_1071_);
v_i_1071_ = v___x_1078_;
goto _start;
}
else
{
lean_dec(v_i_1071_);
return v___x_1074_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4_spec__7_spec__11___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_1070_ = stack[0].m_obj;
lean_object* v_i_1071_ = stack[1].m_obj;
lean_object* v_k_1072_ = stack[2].m_obj;
uint8_t v_res_1080_;
v_res_1080_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4_spec__7_spec__11___redArg(v_keys_1070_, v_i_1071_, v_k_1072_);
stack->m_num = v_res_1080_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4_spec__7_spec__11___redArg___boxed(lean_object* v_keys_1081_, lean_object* v_i_1082_, lean_object* v_k_1083_){
_start:
{
uint8_t v_res_1084_; lean_object* v_r_1085_; 
v_res_1084_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4_spec__7_spec__11___redArg(v_keys_1081_, v_i_1082_, v_k_1083_);
lean_dec(v_k_1083_);
lean_dec_ref(v_keys_1081_);
v_r_1085_ = lean_box(v_res_1084_);
return v_r_1085_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4_spec__7___redArg(lean_object* v_x_1086_, size_t v_x_1087_, lean_object* v_x_1088_){
_start:
{
if (lean_obj_tag(v_x_1086_) == 0)
{
lean_object* v_es_1089_; lean_object* v___x_1090_; size_t v___x_1091_; size_t v___x_1092_; lean_object* v_j_1093_; lean_object* v___x_1094_; 
v_es_1089_ = lean_ctor_get(v_x_1086_, 0);
v___x_1090_ = lean_box(2);
v___x_1091_ = ((size_t)31ULL);
v___x_1092_ = lean_usize_land(v_x_1087_, v___x_1091_);
v_j_1093_ = lean_usize_to_nat(v___x_1092_);
v___x_1094_ = lean_array_get_borrowed(v___x_1090_, v_es_1089_, v_j_1093_);
lean_dec(v_j_1093_);
switch(lean_obj_tag(v___x_1094_))
{
case 0:
{
lean_object* v_key_1095_; uint8_t v___x_1096_; 
v_key_1095_ = lean_ctor_get(v___x_1094_, 0);
v___x_1096_ = lean_name_eq(v_x_1088_, v_key_1095_);
return v___x_1096_;
}
case 1:
{
lean_object* v_node_1097_; size_t v___x_1098_; size_t v___x_1099_; 
v_node_1097_ = lean_ctor_get(v___x_1094_, 0);
v___x_1098_ = ((size_t)5ULL);
v___x_1099_ = lean_usize_shift_right(v_x_1087_, v___x_1098_);
v_x_1086_ = v_node_1097_;
v_x_1087_ = v___x_1099_;
goto _start;
}
default: 
{
uint8_t v___x_1101_; 
v___x_1101_ = 0;
return v___x_1101_;
}
}
}
else
{
lean_object* v_ks_1102_; lean_object* v___x_1103_; uint8_t v___x_1104_; 
v_ks_1102_ = lean_ctor_get(v_x_1086_, 0);
v___x_1103_ = lean_unsigned_to_nat(0u);
v___x_1104_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4_spec__7_spec__11___redArg(v_ks_1102_, v___x_1103_, v_x_1088_);
return v___x_1104_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1086_ = stack[0].m_obj;
size_t v_x_1087_ = stack[1].m_num;
lean_object* v_x_1088_ = stack[2].m_obj;
uint8_t v_res_1105_;
v_res_1105_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4_spec__7___redArg(v_x_1086_, v_x_1087_, v_x_1088_);
stack->m_num = v_res_1105_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4_spec__7___redArg___boxed(lean_object* v_x_1106_, lean_object* v_x_1107_, lean_object* v_x_1108_){
_start:
{
size_t v_x_11787__boxed_1109_; uint8_t v_res_1110_; lean_object* v_r_1111_; 
v_x_11787__boxed_1109_ = lean_unbox_usize(v_x_1107_);
lean_dec(v_x_1107_);
v_res_1110_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4_spec__7___redArg(v_x_1106_, v_x_11787__boxed_1109_, v_x_1108_);
lean_dec(v_x_1108_);
lean_dec_ref(v_x_1106_);
v_r_1111_ = lean_box(v_res_1110_);
return v_r_1111_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4___redArg(lean_object* v_x_1112_, lean_object* v_x_1113_){
_start:
{
uint64_t v___y_1115_; 
if (lean_obj_tag(v_x_1113_) == 0)
{
uint64_t v___x_1118_; 
v___x_1118_ = 1723ULL;
v___y_1115_ = v___x_1118_;
goto v___jp_1114_;
}
else
{
uint64_t v_hash_1119_; 
v_hash_1119_ = lean_ctor_get_uint64(v_x_1113_, sizeof(void*)*2);
v___y_1115_ = v_hash_1119_;
goto v___jp_1114_;
}
v___jp_1114_:
{
size_t v___x_1116_; uint8_t v___x_1117_; 
v___x_1116_ = lean_uint64_to_usize(v___y_1115_);
v___x_1117_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4_spec__7___redArg(v_x_1112_, v___x_1116_, v_x_1113_);
return v___x_1117_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1112_ = stack[0].m_obj;
lean_object* v_x_1113_ = stack[1].m_obj;
uint8_t v_res_1120_;
v_res_1120_ = l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4___redArg(v_x_1112_, v_x_1113_);
stack->m_num = v_res_1120_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4___redArg___boxed(lean_object* v_x_1121_, lean_object* v_x_1122_){
_start:
{
uint8_t v_res_1123_; lean_object* v_r_1124_; 
v_res_1123_ = l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4___redArg(v_x_1121_, v_x_1122_);
lean_dec(v_x_1122_);
lean_dec_ref(v_x_1121_);
v_r_1124_ = lean_box(v_res_1123_);
return v_r_1124_;
}
}
lean_object* l_Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10(lean_object* v___x_1125_, lean_object* v___x_1126_, uint8_t v___y_1127_, lean_object* v_ignoreTacticKinds_1128_, lean_object* v_stx_1129_, lean_object* v_a_1130_){
_start:
{
lean_object* v___y_1133_; uint8_t v___y_1134_; 
if (lean_obj_tag(v_stx_1129_) == 1)
{
lean_object* v_kind_1152_; lean_object* v_args_1153_; lean_object* v___y_1155_; uint8_t v___x_1158_; 
v_kind_1152_ = lean_ctor_get(v_stx_1129_, 1);
v_args_1153_ = lean_ctor_get(v_stx_1129_, 2);
v___x_1158_ = l_Lean_Linter_Extra_UnreachableTactic_isIgnoreTacticKind(v_ignoreTacticKinds_1128_, v_kind_1152_);
if (v___x_1158_ == 0)
{
lean_object* v___x_1159_; lean_object* v___x_1160_; uint8_t v___x_1161_; 
v___x_1159_ = lean_unsigned_to_nat(0u);
v___x_1160_ = lean_array_get_size(v_args_1153_);
v___x_1161_ = lean_nat_dec_lt(v___x_1159_, v___x_1160_);
if (v___x_1161_ == 0)
{
v___y_1155_ = v_a_1130_;
goto v___jp_1154_;
}
else
{
lean_object* v___x_1162_; size_t v___x_1163_; size_t v___x_1164_; lean_object* v___x_1165_; 
v___x_1162_ = lean_box(0);
v___x_1163_ = ((size_t)0ULL);
v___x_1164_ = lean_usize_of_nat(v___x_1160_);
v___x_1165_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__16(v___x_1125_, v___x_1126_, v___y_1127_, v_ignoreTacticKinds_1128_, v_args_1153_, v___x_1163_, v___x_1164_, v___x_1162_, v_a_1130_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_dec_ref_known(v___x_1165_, 1);
v___y_1155_ = v_a_1130_;
goto v___jp_1154_;
}
else
{
lean_dec_ref_known(v_stx_1129_, 3);
return v___x_1165_;
}
}
}
else
{
v___y_1155_ = v_a_1130_;
goto v___jp_1154_;
}
v___jp_1154_:
{
uint8_t v___x_1156_; 
v___x_1156_ = l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4___redArg(v___x_1125_, v_kind_1152_);
if (v___x_1156_ == 0)
{
uint8_t v___x_1157_; 
v___x_1157_ = l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4___redArg(v___x_1126_, v_kind_1152_);
v___y_1133_ = v___y_1155_;
v___y_1134_ = v___x_1157_;
goto v___jp_1132_;
}
else
{
v___y_1133_ = v___y_1155_;
v___y_1134_ = v___y_1127_;
goto v___jp_1132_;
}
}
}
else
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
lean_dec(v_stx_1129_);
v___x_1166_ = lean_box(0);
v___x_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1166_);
return v___x_1167_;
}
v___jp_1132_:
{
if (v___y_1134_ == 0)
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
lean_dec(v_stx_1129_);
v___x_1135_ = lean_box(0);
v___x_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1135_);
return v___x_1136_;
}
else
{
lean_object* v___x_1137_; 
v___x_1137_ = l_Lean_Syntax_getRange_x3f(v_stx_1129_, v___y_1134_);
if (lean_obj_tag(v___x_1137_) == 1)
{
lean_object* v_val_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1149_; 
v_val_1138_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1140_ = v___x_1137_;
v_isShared_1141_ = v_isSharedCheck_1149_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_val_1138_);
lean_dec(v___x_1137_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1149_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1147_; 
v___x_1142_ = lean_st_ref_take(v___y_1133_);
v___x_1143_ = lean_box(0);
v___x_1144_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15___redArg(v___x_1142_, v_val_1138_, v_stx_1129_);
v___x_1145_ = lean_st_ref_put(v___y_1133_, v___x_1144_);
if (v_isShared_1141_ == 0)
{
lean_ctor_set_tag(v___x_1140_, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1143_);
v___x_1147_ = v___x_1140_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1143_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
else
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
lean_dec(v___x_1137_);
lean_dec(v_stx_1129_);
v___x_1150_ = lean_box(0);
v___x_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1150_);
return v___x_1151_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1125_ = stack[0].m_obj;
lean_object* v___x_1126_ = stack[1].m_obj;
uint8_t v___y_1127_ = stack[2].m_num;
lean_object* v_ignoreTacticKinds_1128_ = stack[3].m_obj;
lean_object* v_stx_1129_ = stack[4].m_obj;
lean_object* v_a_1130_ = stack[5].m_obj;
lean_object* v_res_1168_;
v_res_1168_ = l_Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10(v___x_1125_, v___x_1126_, v___y_1127_, v_ignoreTacticKinds_1128_, v_stx_1129_, v_a_1130_);
stack->m_obj
 = v_res_1168_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__16(lean_object* v___x_1169_, lean_object* v___x_1170_, uint8_t v___y_1171_, lean_object* v_ignoreTacticKinds_1172_, lean_object* v_as_1173_, size_t v_i_1174_, size_t v_stop_1175_, lean_object* v_b_1176_, lean_object* v___y_1177_){
_start:
{
uint8_t v___x_1179_; 
v___x_1179_ = lean_usize_dec_eq(v_i_1174_, v_stop_1175_);
if (v___x_1179_ == 0)
{
lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1180_ = lean_array_uget_borrowed(v_as_1173_, v_i_1174_);
lean_inc(v___x_1180_);
v___x_1181_ = l_Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10(v___x_1169_, v___x_1170_, v___y_1171_, v_ignoreTacticKinds_1172_, v___x_1180_, v___y_1177_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1182_; size_t v___x_1183_; size_t v___x_1184_; 
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
lean_inc(v_a_1182_);
lean_dec_ref_known(v___x_1181_, 1);
v___x_1183_ = ((size_t)1ULL);
v___x_1184_ = lean_usize_add(v_i_1174_, v___x_1183_);
v_i_1174_ = v___x_1184_;
v_b_1176_ = v_a_1182_;
goto _start;
}
else
{
return v___x_1181_;
}
}
else
{
lean_object* v___x_1186_; 
v___x_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1186_, 0, v_b_1176_);
return v___x_1186_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__16_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1169_ = stack[0].m_obj;
lean_object* v___x_1170_ = stack[1].m_obj;
uint8_t v___y_1171_ = stack[2].m_num;
lean_object* v_ignoreTacticKinds_1172_ = stack[3].m_obj;
lean_object* v_as_1173_ = stack[4].m_obj;
size_t v_i_1174_ = stack[5].m_num;
size_t v_stop_1175_ = stack[6].m_num;
lean_object* v_b_1176_ = stack[7].m_obj;
lean_object* v___y_1177_ = stack[8].m_obj;
lean_object* v_res_1187_;
v_res_1187_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__16(v___x_1169_, v___x_1170_, v___y_1171_, v_ignoreTacticKinds_1172_, v_as_1173_, v_i_1174_, v_stop_1175_, v_b_1176_, v___y_1177_);
stack->m_obj
 = v_res_1187_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__16___boxed(lean_object* v___x_1188_, lean_object* v___x_1189_, lean_object* v___y_1190_, lean_object* v_ignoreTacticKinds_1191_, lean_object* v_as_1192_, lean_object* v_i_1193_, lean_object* v_stop_1194_, lean_object* v_b_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
uint8_t v___y_11875__boxed_1198_; size_t v_i_boxed_1199_; size_t v_stop_boxed_1200_; lean_object* v_res_1201_; 
v___y_11875__boxed_1198_ = lean_unbox(v___y_1190_);
v_i_boxed_1199_ = lean_unbox_usize(v_i_1193_);
lean_dec(v_i_1193_);
v_stop_boxed_1200_ = lean_unbox_usize(v_stop_1194_);
lean_dec(v_stop_1194_);
v_res_1201_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__16(v___x_1188_, v___x_1189_, v___y_11875__boxed_1198_, v_ignoreTacticKinds_1191_, v_as_1192_, v_i_boxed_1199_, v_stop_boxed_1200_, v_b_1195_, v___y_1196_);
lean_dec(v___y_1196_);
lean_dec_ref(v_as_1192_);
lean_dec_ref(v_ignoreTacticKinds_1191_);
lean_dec_ref(v___x_1189_);
lean_dec_ref(v___x_1188_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10___boxed(lean_object* v___x_1202_, lean_object* v___x_1203_, lean_object* v___y_1204_, lean_object* v_ignoreTacticKinds_1205_, lean_object* v_stx_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_){
_start:
{
uint8_t v___y_11889__boxed_1209_; lean_object* v_res_1210_; 
v___y_11889__boxed_1209_ = lean_unbox(v___y_1204_);
v_res_1210_ = l_Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10(v___x_1202_, v___x_1203_, v___y_11889__boxed_1209_, v_ignoreTacticKinds_1205_, v_stx_1206_, v_a_1207_);
lean_dec(v_a_1207_);
lean_dec_ref(v_ignoreTacticKinds_1205_);
lean_dec_ref(v___x_1203_);
lean_dec_ref(v___x_1202_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8___redArg(lean_object* v_keys_1211_, lean_object* v_vals_1212_, lean_object* v_i_1213_, lean_object* v_k_1214_){
_start:
{
lean_object* v___x_1215_; uint8_t v___x_1216_; 
v___x_1215_ = lean_array_get_size(v_keys_1211_);
v___x_1216_ = lean_nat_dec_lt(v_i_1213_, v___x_1215_);
if (v___x_1216_ == 0)
{
lean_object* v___x_1217_; 
lean_dec(v_i_1213_);
v___x_1217_ = lean_box(0);
return v___x_1217_;
}
else
{
lean_object* v_k_x27_1218_; uint8_t v___x_1219_; 
v_k_x27_1218_ = lean_array_fget_borrowed(v_keys_1211_, v_i_1213_);
v___x_1219_ = lean_name_eq(v_k_1214_, v_k_x27_1218_);
if (v___x_1219_ == 0)
{
lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1220_ = lean_unsigned_to_nat(1u);
v___x_1221_ = lean_nat_add(v_i_1213_, v___x_1220_);
lean_dec(v_i_1213_);
v_i_1213_ = v___x_1221_;
goto _start;
}
else
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = lean_array_fget_borrowed(v_vals_1212_, v_i_1213_);
lean_dec(v_i_1213_);
lean_inc(v___x_1223_);
v___x_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
return v___x_1224_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_keys_1225_, lean_object* v_vals_1226_, lean_object* v_i_1227_, lean_object* v_k_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8___redArg(v_keys_1225_, v_vals_1226_, v_i_1227_, v_k_1228_);
lean_dec(v_k_1228_);
lean_dec_ref(v_vals_1226_);
lean_dec_ref(v_keys_1225_);
return v_res_1229_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5___redArg(lean_object* v_x_1230_, size_t v_x_1231_, lean_object* v_x_1232_){
_start:
{
if (lean_obj_tag(v_x_1230_) == 0)
{
lean_object* v_es_1233_; lean_object* v___x_1234_; size_t v___x_1235_; size_t v___x_1236_; lean_object* v_j_1237_; lean_object* v___x_1238_; 
v_es_1233_ = lean_ctor_get(v_x_1230_, 0);
v___x_1234_ = lean_box(2);
v___x_1235_ = ((size_t)31ULL);
v___x_1236_ = lean_usize_land(v_x_1231_, v___x_1235_);
v_j_1237_ = lean_usize_to_nat(v___x_1236_);
v___x_1238_ = lean_array_get_borrowed(v___x_1234_, v_es_1233_, v_j_1237_);
lean_dec(v_j_1237_);
switch(lean_obj_tag(v___x_1238_))
{
case 0:
{
lean_object* v_key_1239_; lean_object* v_val_1240_; uint8_t v___x_1241_; 
v_key_1239_ = lean_ctor_get(v___x_1238_, 0);
v_val_1240_ = lean_ctor_get(v___x_1238_, 1);
v___x_1241_ = lean_name_eq(v_x_1232_, v_key_1239_);
if (v___x_1241_ == 0)
{
lean_object* v___x_1242_; 
v___x_1242_ = lean_box(0);
return v___x_1242_;
}
else
{
lean_object* v___x_1243_; 
lean_inc(v_val_1240_);
v___x_1243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1243_, 0, v_val_1240_);
return v___x_1243_;
}
}
case 1:
{
lean_object* v_node_1244_; size_t v___x_1245_; size_t v___x_1246_; 
v_node_1244_ = lean_ctor_get(v___x_1238_, 0);
v___x_1245_ = ((size_t)5ULL);
v___x_1246_ = lean_usize_shift_right(v_x_1231_, v___x_1245_);
v_x_1230_ = v_node_1244_;
v_x_1231_ = v___x_1246_;
goto _start;
}
default: 
{
lean_object* v___x_1248_; 
v___x_1248_ = lean_box(0);
return v___x_1248_;
}
}
}
else
{
lean_object* v_ks_1249_; lean_object* v_vs_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v_ks_1249_ = lean_ctor_get(v_x_1230_, 0);
v_vs_1250_ = lean_ctor_get(v_x_1230_, 1);
v___x_1251_ = lean_unsigned_to_nat(0u);
v___x_1252_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8___redArg(v_ks_1249_, v_vs_1250_, v___x_1251_, v_x_1232_);
return v___x_1252_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1230_ = stack[0].m_obj;
size_t v_x_1231_ = stack[1].m_num;
lean_object* v_x_1232_ = stack[2].m_obj;
lean_object* v_res_1253_;
v_res_1253_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5___redArg(v_x_1230_, v_x_1231_, v_x_1232_);
stack->m_obj
 = v_res_1253_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5___redArg___boxed(lean_object* v_x_1254_, lean_object* v_x_1255_, lean_object* v_x_1256_){
_start:
{
size_t v_x_12082__boxed_1257_; lean_object* v_res_1258_; 
v_x_12082__boxed_1257_ = lean_unbox_usize(v_x_1255_);
lean_dec(v_x_1255_);
v_res_1258_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5___redArg(v_x_1254_, v_x_12082__boxed_1257_, v_x_1256_);
lean_dec(v_x_1256_);
lean_dec_ref(v_x_1254_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3___redArg(lean_object* v_x_1259_, lean_object* v_x_1260_){
_start:
{
uint64_t v___y_1262_; 
if (lean_obj_tag(v_x_1260_) == 0)
{
uint64_t v___x_1265_; 
v___x_1265_ = 1723ULL;
v___y_1262_ = v___x_1265_;
goto v___jp_1261_;
}
else
{
uint64_t v_hash_1266_; 
v_hash_1266_ = lean_ctor_get_uint64(v_x_1260_, sizeof(void*)*2);
v___y_1262_ = v_hash_1266_;
goto v___jp_1261_;
}
v___jp_1261_:
{
size_t v___x_1263_; lean_object* v___x_1264_; 
v___x_1263_ = lean_uint64_to_usize(v___y_1262_);
v___x_1264_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5___redArg(v_x_1259_, v___x_1263_, v_x_1260_);
return v___x_1264_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3___redArg___boxed(lean_object* v_x_1267_, lean_object* v_x_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3___redArg(v_x_1267_, v_x_1268_);
lean_dec(v_x_1268_);
lean_dec_ref(v_x_1267_);
return v_res_1269_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__20(lean_object* v_opts_1270_, lean_object* v_opt_1271_){
_start:
{
lean_object* v_name_1272_; lean_object* v_defValue_1273_; lean_object* v_map_1274_; lean_object* v___x_1275_; 
v_name_1272_ = lean_ctor_get(v_opt_1271_, 0);
v_defValue_1273_ = lean_ctor_get(v_opt_1271_, 1);
v_map_1274_ = lean_ctor_get(v_opts_1270_, 0);
v___x_1275_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1274_, v_name_1272_);
if (lean_obj_tag(v___x_1275_) == 0)
{
uint8_t v___x_1276_; 
v___x_1276_ = lean_unbox(v_defValue_1273_);
return v___x_1276_;
}
else
{
lean_object* v_val_1277_; 
v_val_1277_ = lean_ctor_get(v___x_1275_, 0);
lean_inc(v_val_1277_);
lean_dec_ref_known(v___x_1275_, 1);
if (lean_obj_tag(v_val_1277_) == 1)
{
uint8_t v_v_1278_; 
v_v_1278_ = lean_ctor_get_uint8(v_val_1277_, 0);
lean_dec_ref_known(v_val_1277_, 0);
return v_v_1278_;
}
else
{
uint8_t v___x_1279_; 
lean_dec(v_val_1277_);
v___x_1279_ = lean_unbox(v_defValue_1273_);
return v___x_1279_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__20_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_1270_ = stack[0].m_obj;
lean_object* v_opt_1271_ = stack[1].m_obj;
uint8_t v_res_1280_;
v_res_1280_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__20(v_opts_1270_, v_opt_1271_);
stack->m_num = v_res_1280_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__20___boxed(lean_object* v_opts_1281_, lean_object* v_opt_1282_){
_start:
{
uint8_t v_res_1283_; lean_object* v_r_1284_; 
v_res_1283_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__20(v_opts_1281_, v_opt_1282_);
lean_dec_ref(v_opt_1282_);
lean_dec_ref(v_opts_1281_);
v_r_1284_ = lean_box(v_res_1283_);
return v_r_1284_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__0(void){
_start:
{
lean_object* v___x_1285_; 
v___x_1285_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1285_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__1(void){
_start:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1286_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__0);
v___x_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1286_);
return v___x_1287_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__2(void){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1288_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1289_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__1);
v___x_1290_ = lean_unsigned_to_nat(0u);
v___x_1291_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1290_);
lean_ctor_set(v___x_1291_, 1, v___x_1290_);
lean_ctor_set(v___x_1291_, 2, v___x_1290_);
lean_ctor_set(v___x_1291_, 3, v___x_1290_);
lean_ctor_set(v___x_1291_, 4, v___x_1289_);
lean_ctor_set(v___x_1291_, 5, v___x_1289_);
lean_ctor_set(v___x_1291_, 6, v___x_1289_);
lean_ctor_set(v___x_1291_, 7, v___x_1289_);
lean_ctor_set(v___x_1291_, 8, v___x_1289_);
lean_ctor_set(v___x_1291_, 9, v___x_1289_);
lean_ctor_set(v___x_1291_, 10, v___x_1289_);
lean_ctor_set(v___x_1291_, 11, v___x_1288_);
return v___x_1291_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__3(void){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1292_ = lean_unsigned_to_nat(32u);
v___x_1293_ = lean_mk_empty_array_with_capacity(v___x_1292_);
v___x_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1293_);
return v___x_1294_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__4(void){
_start:
{
size_t v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1295_ = ((size_t)5ULL);
v___x_1296_ = lean_unsigned_to_nat(0u);
v___x_1297_ = lean_unsigned_to_nat(32u);
v___x_1298_ = lean_mk_empty_array_with_capacity(v___x_1297_);
v___x_1299_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__3);
v___x_1300_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1300_, 0, v___x_1299_);
lean_ctor_set(v___x_1300_, 1, v___x_1298_);
lean_ctor_set(v___x_1300_, 2, v___x_1296_);
lean_ctor_set(v___x_1300_, 3, v___x_1296_);
lean_ctor_set_usize(v___x_1300_, 4, v___x_1295_);
return v___x_1300_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__5(void){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1301_ = lean_box(1);
v___x_1302_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__4);
v___x_1303_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__1);
v___x_1304_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1303_);
lean_ctor_set(v___x_1304_, 1, v___x_1302_);
lean_ctor_set(v___x_1304_, 2, v___x_1301_);
return v___x_1304_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg(lean_object* v_msgData_1305_, lean_object* v___y_1306_){
_start:
{
lean_object* v___x_1308_; lean_object* v_env_1309_; uint8_t v___x_1310_; lean_object* v_env_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v_scopes_1314_; lean_object* v___x_1315_; lean_object* v_opts_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1308_ = lean_st_ref_get(v___y_1306_);
v_env_1309_ = lean_ctor_get(v___x_1308_, 0);
lean_inc_ref(v_env_1309_);
lean_dec(v___x_1308_);
v___x_1310_ = 0;
v_env_1311_ = l_Lean_Environment_setRecordingDeps(v_env_1309_, v___x_1310_);
v___x_1312_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1313_ = lean_st_ref_get(v___y_1306_);
v_scopes_1314_ = lean_ctor_get(v___x_1313_, 2);
lean_inc(v_scopes_1314_);
lean_dec(v___x_1313_);
v___x_1315_ = l_List_head_x21___redArg(v___x_1312_, v_scopes_1314_);
lean_dec(v_scopes_1314_);
v_opts_1316_ = lean_ctor_get(v___x_1315_, 1);
lean_inc_ref(v_opts_1316_);
lean_dec(v___x_1315_);
v___x_1317_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__2);
v___x_1318_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__5);
v___x_1319_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1319_, 0, v_env_1311_);
lean_ctor_set(v___x_1319_, 1, v___x_1317_);
lean_ctor_set(v___x_1319_, 2, v___x_1318_);
lean_ctor_set(v___x_1319_, 3, v_opts_1316_);
v___x_1320_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
lean_ctor_set(v___x_1320_, 1, v_msgData_1305_);
v___x_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1320_);
return v___x_1321_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1305_ = stack[0].m_obj;
lean_object* v___y_1306_ = stack[1].m_obj;
lean_object* v_res_1322_;
v_res_1322_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg(v_msgData_1305_, v___y_1306_);
stack->m_obj
 = v_res_1322_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___boxed(lean_object* v_msgData_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg(v_msgData_1323_, v___y_1324_);
lean_dec(v___y_1324_);
return v_res_1326_;
}
}
uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13___lam__0(uint8_t v_suppressElabErrors_1328_, uint8_t v___y_1329_, lean_object* v_x_1330_){
_start:
{
if (lean_obj_tag(v_x_1330_) == 1)
{
lean_object* v_pre_1331_; 
v_pre_1331_ = lean_ctor_get(v_x_1330_, 0);
if (lean_obj_tag(v_pre_1331_) == 0)
{
lean_object* v_str_1332_; lean_object* v___x_1333_; uint8_t v___x_1334_; 
v_str_1332_ = lean_ctor_get(v_x_1330_, 1);
v___x_1333_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13___lam__0___closed__0));
v___x_1334_ = lean_string_dec_eq(v_str_1332_, v___x_1333_);
if (v___x_1334_ == 0)
{
return v___x_1334_;
}
else
{
return v_suppressElabErrors_1328_;
}
}
else
{
return v___y_1329_;
}
}
else
{
return v___y_1329_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_1328_ = stack[0].m_num;
uint8_t v___y_1329_ = stack[1].m_num;
lean_object* v_x_1330_ = stack[2].m_obj;
uint8_t v_res_1335_;
v_res_1335_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13___lam__0(v_suppressElabErrors_1328_, v___y_1329_, v_x_1330_);
stack->m_num = v_res_1335_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13___lam__0___boxed(lean_object* v_suppressElabErrors_1336_, lean_object* v___y_1337_, lean_object* v_x_1338_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1339_; uint8_t v___y_12335__boxed_1340_; uint8_t v_res_1341_; lean_object* v_r_1342_; 
v_suppressElabErrors_boxed_1339_ = lean_unbox(v_suppressElabErrors_1336_);
v___y_12335__boxed_1340_ = lean_unbox(v___y_1337_);
v_res_1341_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13___lam__0(v_suppressElabErrors_boxed_1339_, v___y_12335__boxed_1340_, v_x_1338_);
lean_dec(v_x_1338_);
v_r_1342_ = lean_box(v_res_1341_);
return v_r_1342_;
}
}
lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13(lean_object* v_ref_1344_, lean_object* v_msgData_1345_, uint8_t v_severity_1346_, uint8_t v_isSilent_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v___y_1352_; lean_object* v___y_1353_; uint8_t v___y_1354_; lean_object* v___y_1355_; uint8_t v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; uint8_t v___y_1417_; lean_object* v___y_1418_; uint8_t v___y_1419_; uint8_t v___y_1420_; lean_object* v___y_1421_; uint8_t v___y_1445_; lean_object* v___y_1446_; uint8_t v___y_1447_; uint8_t v___y_1448_; lean_object* v___y_1449_; uint8_t v___y_1453_; uint8_t v___y_1454_; uint8_t v___y_1455_; uint8_t v___x_1470_; uint8_t v___y_1472_; uint8_t v___y_1473_; uint8_t v___y_1474_; uint8_t v___y_1476_; uint8_t v___x_1488_; 
v___x_1470_ = 2;
v___x_1488_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1346_, v___x_1470_);
if (v___x_1488_ == 0)
{
v___y_1476_ = v___x_1488_;
goto v___jp_1475_;
}
else
{
uint8_t v___x_1489_; 
lean_inc_ref(v_msgData_1345_);
v___x_1489_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1345_);
v___y_1476_ = v___x_1489_;
goto v___jp_1475_;
}
v___jp_1351_:
{
lean_object* v___x_1360_; 
v___x_1360_ = l_Lean_Elab_Command_getScope___redArg(v___y_1359_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v_a_1361_; lean_object* v_currNamespace_1362_; lean_object* v___x_1363_; 
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_a_1361_);
lean_dec_ref_known(v___x_1360_, 1);
v_currNamespace_1362_ = lean_ctor_get(v_a_1361_, 2);
lean_inc(v_currNamespace_1362_);
lean_dec(v_a_1361_);
v___x_1363_ = l_Lean_Elab_Command_getScope___redArg(v___y_1359_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1399_; 
v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1366_ = v___x_1363_;
v_isShared_1367_ = v_isSharedCheck_1399_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1363_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1399_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v_openDecls_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v_env_1373_; lean_object* v_messages_1374_; lean_object* v_scopes_1375_; lean_object* v_usedQuotCtxts_1376_; lean_object* v_nextMacroScope_1377_; lean_object* v_maxRecDepth_1378_; lean_object* v_ngen_1379_; lean_object* v_auxDeclNGen_1380_; lean_object* v_infoState_1381_; lean_object* v_traceState_1382_; lean_object* v_snapshotTasks_1383_; lean_object* v_prevLinterStates_1384_; lean_object* v_codeQualityEntryTasks_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1398_; 
v_openDecls_1368_ = lean_ctor_get(v_a_1364_, 3);
lean_inc(v_openDecls_1368_);
lean_dec(v_a_1364_);
v___x_1369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1369_, 0, v_currNamespace_1362_);
lean_ctor_set(v___x_1369_, 1, v_openDecls_1368_);
v___x_1370_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1369_);
lean_ctor_set(v___x_1370_, 1, v___y_1357_);
lean_inc_ref(v___y_1355_);
lean_inc_ref(v___y_1358_);
v___x_1371_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1371_, 0, v___y_1358_);
lean_ctor_set(v___x_1371_, 1, v___y_1353_);
lean_ctor_set(v___x_1371_, 2, v___y_1352_);
lean_ctor_set(v___x_1371_, 3, v___y_1355_);
lean_ctor_set(v___x_1371_, 4, v___x_1370_);
lean_ctor_set_uint8(v___x_1371_, sizeof(void*)*5, v___y_1354_);
lean_ctor_set_uint8(v___x_1371_, sizeof(void*)*5 + 1, v___y_1356_);
lean_ctor_set_uint8(v___x_1371_, sizeof(void*)*5 + 2, v_isSilent_1347_);
v___x_1372_ = lean_st_ref_take(v___y_1359_);
v_env_1373_ = lean_ctor_get(v___x_1372_, 0);
v_messages_1374_ = lean_ctor_get(v___x_1372_, 1);
v_scopes_1375_ = lean_ctor_get(v___x_1372_, 2);
v_usedQuotCtxts_1376_ = lean_ctor_get(v___x_1372_, 3);
v_nextMacroScope_1377_ = lean_ctor_get(v___x_1372_, 4);
v_maxRecDepth_1378_ = lean_ctor_get(v___x_1372_, 5);
v_ngen_1379_ = lean_ctor_get(v___x_1372_, 6);
v_auxDeclNGen_1380_ = lean_ctor_get(v___x_1372_, 7);
v_infoState_1381_ = lean_ctor_get(v___x_1372_, 8);
v_traceState_1382_ = lean_ctor_get(v___x_1372_, 9);
v_snapshotTasks_1383_ = lean_ctor_get(v___x_1372_, 10);
v_prevLinterStates_1384_ = lean_ctor_get(v___x_1372_, 11);
v_codeQualityEntryTasks_1385_ = lean_ctor_get(v___x_1372_, 12);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1387_ = v___x_1372_;
v_isShared_1388_ = v_isSharedCheck_1398_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1385_);
lean_inc(v_prevLinterStates_1384_);
lean_inc(v_snapshotTasks_1383_);
lean_inc(v_traceState_1382_);
lean_inc(v_infoState_1381_);
lean_inc(v_auxDeclNGen_1380_);
lean_inc(v_ngen_1379_);
lean_inc(v_maxRecDepth_1378_);
lean_inc(v_nextMacroScope_1377_);
lean_inc(v_usedQuotCtxts_1376_);
lean_inc(v_scopes_1375_);
lean_inc(v_messages_1374_);
lean_inc(v_env_1373_);
lean_dec(v___x_1372_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1398_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1392_; 
v___x_1389_ = lean_box(0);
v___x_1390_ = l_Lean_MessageLog_add(v___x_1371_, v_messages_1374_);
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 1, v___x_1390_);
v___x_1392_ = v___x_1387_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_env_1373_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v___x_1390_);
lean_ctor_set(v_reuseFailAlloc_1397_, 2, v_scopes_1375_);
lean_ctor_set(v_reuseFailAlloc_1397_, 3, v_usedQuotCtxts_1376_);
lean_ctor_set(v_reuseFailAlloc_1397_, 4, v_nextMacroScope_1377_);
lean_ctor_set(v_reuseFailAlloc_1397_, 5, v_maxRecDepth_1378_);
lean_ctor_set(v_reuseFailAlloc_1397_, 6, v_ngen_1379_);
lean_ctor_set(v_reuseFailAlloc_1397_, 7, v_auxDeclNGen_1380_);
lean_ctor_set(v_reuseFailAlloc_1397_, 8, v_infoState_1381_);
lean_ctor_set(v_reuseFailAlloc_1397_, 9, v_traceState_1382_);
lean_ctor_set(v_reuseFailAlloc_1397_, 10, v_snapshotTasks_1383_);
lean_ctor_set(v_reuseFailAlloc_1397_, 11, v_prevLinterStates_1384_);
lean_ctor_set(v_reuseFailAlloc_1397_, 12, v_codeQualityEntryTasks_1385_);
v___x_1392_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
lean_object* v___x_1393_; lean_object* v___x_1395_; 
v___x_1393_ = lean_st_ref_put(v___y_1359_, v___x_1392_);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 0, v___x_1389_);
v___x_1395_ = v___x_1366_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1389_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
}
}
else
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1407_; 
lean_dec(v_currNamespace_1362_);
lean_dec_ref(v___y_1357_);
lean_dec_ref(v___y_1353_);
lean_dec(v___y_1352_);
v_a_1400_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1402_ = v___x_1363_;
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1363_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1405_; 
if (v_isShared_1403_ == 0)
{
v___x_1405_ = v___x_1402_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_a_1400_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
else
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1415_; 
lean_dec_ref(v___y_1357_);
lean_dec_ref(v___y_1353_);
lean_dec(v___y_1352_);
v_a_1408_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1410_ = v___x_1360_;
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1360_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
if (v_isShared_1411_ == 0)
{
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_a_1408_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
v___jp_1416_:
{
lean_object* v_fileName_1422_; lean_object* v_fileMap_1423_; uint8_t v_suppressElabErrors_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___f_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1443_; 
v_fileName_1422_ = lean_ctor_get(v___y_1348_, 0);
v_fileMap_1423_ = lean_ctor_get(v___y_1348_, 1);
v_suppressElabErrors_1424_ = lean_ctor_get_uint8(v___y_1348_, sizeof(void*)*10);
v___x_1425_ = lean_box(v_suppressElabErrors_1424_);
v___x_1426_ = lean_box(v___y_1417_);
v___f_1427_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1427_, 0, v___x_1425_);
lean_closure_set(v___f_1427_, 1, v___x_1426_);
v___x_1428_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1345_);
v___x_1429_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg(v___x_1428_, v___y_1349_);
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1432_ = v___x_1429_;
v_isShared_1433_ = v_isSharedCheck_1443_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1429_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1443_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
lean_inc_ref_n(v_fileMap_1423_, 2);
v___x_1434_ = l_Lean_FileMap_toPosition(v_fileMap_1423_, v___y_1418_);
lean_dec(v___y_1418_);
v___x_1435_ = l_Lean_FileMap_toPosition(v_fileMap_1423_, v___y_1421_);
lean_dec(v___y_1421_);
v___x_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1435_);
v___x_1437_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13___closed__0));
if (v_suppressElabErrors_1424_ == 0)
{
lean_del_object(v___x_1432_);
lean_dec_ref(v___f_1427_);
v___y_1352_ = v___x_1436_;
v___y_1353_ = v___x_1434_;
v___y_1354_ = v___y_1419_;
v___y_1355_ = v___x_1437_;
v___y_1356_ = v___y_1420_;
v___y_1357_ = v_a_1430_;
v___y_1358_ = v_fileName_1422_;
v___y_1359_ = v___y_1349_;
goto v___jp_1351_;
}
else
{
uint8_t v___x_1438_; 
lean_inc(v_a_1430_);
v___x_1438_ = l_Lean_MessageData_hasTag(v___f_1427_, v_a_1430_);
if (v___x_1438_ == 0)
{
lean_object* v___x_1439_; lean_object* v___x_1441_; 
lean_dec_ref_known(v___x_1436_, 1);
lean_dec_ref(v___x_1434_);
lean_dec(v_a_1430_);
v___x_1439_ = lean_box(0);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 0, v___x_1439_);
v___x_1441_ = v___x_1432_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1439_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
else
{
lean_del_object(v___x_1432_);
v___y_1352_ = v___x_1436_;
v___y_1353_ = v___x_1434_;
v___y_1354_ = v___y_1419_;
v___y_1355_ = v___x_1437_;
v___y_1356_ = v___y_1420_;
v___y_1357_ = v_a_1430_;
v___y_1358_ = v_fileName_1422_;
v___y_1359_ = v___y_1349_;
goto v___jp_1351_;
}
}
}
}
v___jp_1444_:
{
lean_object* v___x_1450_; 
v___x_1450_ = l_Lean_Syntax_getTailPos_x3f(v___y_1446_, v___y_1447_);
lean_dec(v___y_1446_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_inc(v___y_1449_);
v___y_1417_ = v___y_1445_;
v___y_1418_ = v___y_1449_;
v___y_1419_ = v___y_1447_;
v___y_1420_ = v___y_1448_;
v___y_1421_ = v___y_1449_;
goto v___jp_1416_;
}
else
{
lean_object* v_val_1451_; 
v_val_1451_ = lean_ctor_get(v___x_1450_, 0);
lean_inc(v_val_1451_);
lean_dec_ref_known(v___x_1450_, 1);
v___y_1417_ = v___y_1445_;
v___y_1418_ = v___y_1449_;
v___y_1419_ = v___y_1447_;
v___y_1420_ = v___y_1448_;
v___y_1421_ = v_val_1451_;
goto v___jp_1416_;
}
}
v___jp_1452_:
{
lean_object* v___x_1456_; 
v___x_1456_ = l_Lean_Elab_Command_getRef___redArg(v___y_1348_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v_a_1457_; lean_object* v_ref_1458_; lean_object* v___x_1459_; 
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
lean_inc(v_a_1457_);
lean_dec_ref_known(v___x_1456_, 1);
v_ref_1458_ = l_Lean_replaceRef(v_ref_1344_, v_a_1457_);
lean_dec(v_a_1457_);
v___x_1459_ = l_Lean_Syntax_getPos_x3f(v_ref_1458_, v___y_1454_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v___x_1460_; 
v___x_1460_ = lean_unsigned_to_nat(0u);
v___y_1445_ = v___y_1453_;
v___y_1446_ = v_ref_1458_;
v___y_1447_ = v___y_1454_;
v___y_1448_ = v___y_1455_;
v___y_1449_ = v___x_1460_;
goto v___jp_1444_;
}
else
{
lean_object* v_val_1461_; 
v_val_1461_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_val_1461_);
lean_dec_ref_known(v___x_1459_, 1);
v___y_1445_ = v___y_1453_;
v___y_1446_ = v_ref_1458_;
v___y_1447_ = v___y_1454_;
v___y_1448_ = v___y_1455_;
v___y_1449_ = v_val_1461_;
goto v___jp_1444_;
}
}
else
{
lean_object* v_a_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1469_; 
lean_dec_ref(v_msgData_1345_);
v_a_1462_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1464_ = v___x_1456_;
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_a_1462_);
lean_dec(v___x_1456_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1467_; 
if (v_isShared_1465_ == 0)
{
v___x_1467_ = v___x_1464_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_a_1462_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
}
v___jp_1471_:
{
if (v___y_1474_ == 0)
{
v___y_1453_ = v___y_1472_;
v___y_1454_ = v___y_1473_;
v___y_1455_ = v_severity_1346_;
goto v___jp_1452_;
}
else
{
v___y_1453_ = v___y_1472_;
v___y_1454_ = v___y_1473_;
v___y_1455_ = v___x_1470_;
goto v___jp_1452_;
}
}
v___jp_1475_:
{
if (v___y_1476_ == 0)
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v_scopes_1479_; lean_object* v___x_1480_; lean_object* v_opts_1481_; uint8_t v___x_1482_; uint8_t v___x_1483_; 
v___x_1477_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1478_ = lean_st_ref_get(v___y_1349_);
v_scopes_1479_ = lean_ctor_get(v___x_1478_, 2);
lean_inc(v_scopes_1479_);
lean_dec(v___x_1478_);
v___x_1480_ = l_List_head_x21___redArg(v___x_1477_, v_scopes_1479_);
lean_dec(v_scopes_1479_);
v_opts_1481_ = lean_ctor_get(v___x_1480_, 1);
lean_inc_ref(v_opts_1481_);
lean_dec(v___x_1480_);
v___x_1482_ = 1;
v___x_1483_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1346_, v___x_1482_);
if (v___x_1483_ == 0)
{
lean_dec_ref(v_opts_1481_);
v___y_1472_ = v___y_1476_;
v___y_1473_ = v___y_1476_;
v___y_1474_ = v___x_1483_;
goto v___jp_1471_;
}
else
{
lean_object* v___x_1484_; uint8_t v___x_1485_; 
v___x_1484_ = l_Lean_warningAsError;
v___x_1485_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__20(v_opts_1481_, v___x_1484_);
lean_dec_ref(v_opts_1481_);
v___y_1472_ = v___y_1476_;
v___y_1473_ = v___y_1476_;
v___y_1474_ = v___x_1485_;
goto v___jp_1471_;
}
}
else
{
lean_object* v___x_1486_; lean_object* v___x_1487_; 
lean_dec_ref(v_msgData_1345_);
v___x_1486_ = lean_box(0);
v___x_1487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1486_);
return v___x_1487_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1344_ = stack[0].m_obj;
lean_object* v_msgData_1345_ = stack[1].m_obj;
uint8_t v_severity_1346_ = stack[2].m_num;
uint8_t v_isSilent_1347_ = stack[3].m_num;
lean_object* v___y_1348_ = stack[4].m_obj;
lean_object* v___y_1349_ = stack[5].m_obj;
lean_object* v_res_1490_;
v_res_1490_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13(v_ref_1344_, v_msgData_1345_, v_severity_1346_, v_isSilent_1347_, v___y_1348_, v___y_1349_);
stack->m_obj
 = v_res_1490_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13___boxed(lean_object* v_ref_1491_, lean_object* v_msgData_1492_, lean_object* v_severity_1493_, lean_object* v_isSilent_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
uint8_t v_severity_boxed_1498_; uint8_t v_isSilent_boxed_1499_; lean_object* v_res_1500_; 
v_severity_boxed_1498_ = lean_unbox(v_severity_1493_);
v_isSilent_boxed_1499_ = lean_unbox(v_isSilent_1494_);
v_res_1500_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13(v_ref_1491_, v_msgData_1492_, v_severity_boxed_1498_, v_isSilent_boxed_1499_, v___y_1495_, v___y_1496_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v_ref_1491_);
return v_res_1500_;
}
}
lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5(lean_object* v_ref_1501_, lean_object* v_msgData_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
uint8_t v___x_1506_; uint8_t v___x_1507_; lean_object* v___x_1508_; 
v___x_1506_ = 1;
v___x_1507_ = 0;
v___x_1508_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13(v_ref_1501_, v_msgData_1502_, v___x_1506_, v___x_1507_, v___y_1503_, v___y_1504_);
return v___x_1508_;
}
}
LEAN_EXPORT void l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1501_ = stack[0].m_obj;
lean_object* v_msgData_1502_ = stack[1].m_obj;
lean_object* v___y_1503_ = stack[2].m_obj;
lean_object* v___y_1504_ = stack[3].m_obj;
lean_object* v_res_1509_;
v_res_1509_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5(v_ref_1501_, v_msgData_1502_, v___y_1503_, v___y_1504_);
stack->m_obj
 = v_res_1509_;
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5___boxed(lean_object* v_ref_1510_, lean_object* v_msgData_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5(v_ref_1510_, v_msgData_1511_, v___y_1512_, v___y_1513_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
lean_dec(v_ref_1510_);
return v_res_1515_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1517_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__0));
v___x_1518_ = l_Lean_stringToMessageData(v___x_1517_);
return v___x_1518_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1520_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__2));
v___x_1521_ = l_Lean_stringToMessageData(v___x_1520_);
return v___x_1521_;
}
}
lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3(lean_object* v_linterOption_1522_, lean_object* v_stx_1523_, lean_object* v_msg_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v_name_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1546_; 
v_name_1528_ = lean_ctor_get(v_linterOption_1522_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v_linterOption_1522_);
if (v_isSharedCheck_1546_ == 0)
{
lean_object* v_unused_1547_; 
v_unused_1547_ = lean_ctor_get(v_linterOption_1522_, 1);
lean_dec(v_unused_1547_);
v___x_1530_ = v_linterOption_1522_;
v_isShared_1531_ = v_isSharedCheck_1546_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_name_1528_);
lean_dec(v_linterOption_1522_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1546_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1535_; 
v___x_1532_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__1);
lean_inc(v_name_1528_);
v___x_1533_ = l_Lean_MessageData_ofName(v_name_1528_);
if (v_isShared_1531_ == 0)
{
lean_ctor_set_tag(v___x_1530_, 7);
lean_ctor_set(v___x_1530_, 1, v___x_1533_);
lean_ctor_set(v___x_1530_, 0, v___x_1532_);
v___x_1535_ = v___x_1530_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1532_);
lean_ctor_set(v_reuseFailAlloc_1545_, 1, v___x_1533_);
v___x_1535_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v_disable_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1536_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__3);
v___x_1537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1535_);
lean_ctor_set(v___x_1537_, 1, v___x_1536_);
v_disable_1538_ = l_Lean_MessageData_note(v___x_1537_);
v___x_1539_ = l_Lean_Linter_linterMessageTag;
v___x_1540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1540_, 0, v_msg_1524_);
lean_ctor_set(v___x_1540_, 1, v_disable_1538_);
v___x_1541_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1539_);
lean_ctor_set(v___x_1541_, 1, v___x_1540_);
v___x_1542_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1542_, 0, v_name_1528_);
lean_ctor_set(v___x_1542_, 1, v___x_1541_);
lean_inc(v_stx_1523_);
v___x_1543_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_1543_, 0, v_stx_1523_);
lean_ctor_set(v___x_1543_, 1, v___x_1542_);
v___x_1544_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5(v_stx_1523_, v___x_1543_, v___y_1525_, v___y_1526_);
lean_dec(v_stx_1523_);
return v___x_1544_;
}
}
}
}
LEAN_EXPORT void l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_linterOption_1522_ = stack[0].m_obj;
lean_object* v_stx_1523_ = stack[1].m_obj;
lean_object* v_msg_1524_ = stack[2].m_obj;
lean_object* v___y_1525_ = stack[3].m_obj;
lean_object* v___y_1526_ = stack[4].m_obj;
lean_object* v_res_1548_;
v_res_1548_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3(v_linterOption_1522_, v_stx_1523_, v_msg_1524_, v___y_1525_, v___y_1526_);
stack->m_obj
 = v_res_1548_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___boxed(lean_object* v_linterOption_1549_, lean_object* v_stx_1550_, lean_object* v_msg_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3(v_linterOption_1549_, v_stx_1550_, v_msg_1551_, v___y_1552_, v___y_1553_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
return v_res_1555_;
}
}
lean_object* l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2(lean_object* v_linterOption_1556_, lean_object* v_stx_1557_, lean_object* v_msg_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
lean_object* v___x_1562_; lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1573_; 
v___x_1562_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1(v___y_1559_, v___y_1560_);
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1565_ = v___x_1562_;
v_isShared_1566_ = v_isSharedCheck_1573_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1562_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1573_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
uint8_t v___x_1567_; 
v___x_1567_ = l_Lean_Linter_getLinterValue(v_linterOption_1556_, v_a_1563_);
lean_dec(v_a_1563_);
if (v___x_1567_ == 0)
{
lean_object* v___x_1568_; lean_object* v___x_1570_; 
lean_dec_ref(v_msg_1558_);
lean_dec(v_stx_1557_);
lean_dec_ref(v_linterOption_1556_);
v___x_1568_ = lean_box(0);
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 0, v___x_1568_);
v___x_1570_ = v___x_1565_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1568_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
else
{
lean_object* v___x_1572_; 
lean_del_object(v___x_1565_);
v___x_1572_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3(v_linterOption_1556_, v_stx_1557_, v_msg_1558_, v___y_1559_, v___y_1560_);
return v___x_1572_;
}
}
}
}
LEAN_EXPORT void l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_linterOption_1556_ = stack[0].m_obj;
lean_object* v_stx_1557_ = stack[1].m_obj;
lean_object* v_msg_1558_ = stack[2].m_obj;
lean_object* v___y_1559_ = stack[3].m_obj;
lean_object* v___y_1560_ = stack[4].m_obj;
lean_object* v_res_1574_;
v_res_1574_ = l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2(v_linterOption_1556_, v_stx_1557_, v_msg_1558_, v___y_1559_, v___y_1560_);
stack->m_obj
 = v_res_1574_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2___boxed(lean_object* v_linterOption_1575_, lean_object* v_stx_1576_, lean_object* v_msg_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2(v_linterOption_1575_, v_stx_1576_, v_msg_1577_, v___y_1578_, v___y_1579_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
return v_res_1581_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___closed__2(void){
_start:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1585_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___closed__1));
v___x_1586_ = l_Lean_MessageData_ofFormat(v___x_1585_);
return v___x_1586_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6(lean_object* v_as_1587_, size_t v_sz_1588_, size_t v_i_1589_, lean_object* v_b_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_){
_start:
{
lean_object* v_a_1595_; uint8_t v___x_1599_; 
v___x_1599_ = lean_usize_dec_lt(v_i_1589_, v_sz_1588_);
if (v___x_1599_ == 0)
{
lean_object* v___x_1600_; 
v___x_1600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1600_, 0, v_b_1590_);
return v___x_1600_;
}
else
{
lean_object* v_a_1601_; lean_object* v_fst_1602_; lean_object* v_snd_1603_; lean_object* v_start_1604_; lean_object* v_stop_1605_; lean_object* v_start_1606_; lean_object* v_stop_1607_; lean_object* v___x_1608_; uint8_t v___y_1610_; uint8_t v___x_1621_; 
v_a_1601_ = lean_array_uget_borrowed(v_as_1587_, v_i_1589_);
v_fst_1602_ = lean_ctor_get(v_a_1601_, 0);
v_snd_1603_ = lean_ctor_get(v_a_1601_, 1);
v_start_1604_ = lean_ctor_get(v_b_1590_, 0);
v_stop_1605_ = lean_ctor_get(v_b_1590_, 1);
v_start_1606_ = lean_ctor_get(v_fst_1602_, 0);
v_stop_1607_ = lean_ctor_get(v_fst_1602_, 1);
v___x_1608_ = l_Lean_Linter_Extra_linter_extra_unreachableTactic;
v___x_1621_ = lean_nat_dec_le(v_start_1604_, v_start_1606_);
if (v___x_1621_ == 0)
{
v___y_1610_ = v___x_1621_;
goto v___jp_1609_;
}
else
{
uint8_t v___x_1622_; 
v___x_1622_ = lean_nat_dec_le(v_stop_1607_, v_stop_1605_);
v___y_1610_ = v___x_1622_;
goto v___jp_1609_;
}
v___jp_1609_:
{
if (v___y_1610_ == 0)
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
lean_dec_ref(v_b_1590_);
v___x_1611_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___closed__2);
lean_inc(v_snd_1603_);
v___x_1612_ = l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2(v___x_1608_, v_snd_1603_, v___x_1611_, v___y_1591_, v___y_1592_);
if (lean_obj_tag(v___x_1612_) == 0)
{
lean_dec_ref_known(v___x_1612_, 1);
lean_inc(v_fst_1602_);
v_a_1595_ = v_fst_1602_;
goto v___jp_1594_;
}
else
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1620_; 
v_a_1613_ = lean_ctor_get(v___x_1612_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1615_ = v___x_1612_;
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1612_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1618_; 
if (v_isShared_1616_ == 0)
{
v___x_1618_ = v___x_1615_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_a_1613_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
}
else
{
v_a_1595_ = v_b_1590_;
goto v___jp_1594_;
}
}
}
v___jp_1594_:
{
size_t v___x_1596_; size_t v___x_1597_; 
v___x_1596_ = ((size_t)1ULL);
v___x_1597_ = lean_usize_add(v_i_1589_, v___x_1596_);
v_i_1589_ = v___x_1597_;
v_b_1590_ = v_a_1595_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1587_ = stack[0].m_obj;
size_t v_sz_1588_ = stack[1].m_num;
size_t v_i_1589_ = stack[2].m_num;
lean_object* v_b_1590_ = stack[3].m_obj;
lean_object* v___y_1591_ = stack[4].m_obj;
lean_object* v___y_1592_ = stack[5].m_obj;
lean_object* v_res_1623_;
v_res_1623_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6(v_as_1587_, v_sz_1588_, v_i_1589_, v_b_1590_, v___y_1591_, v___y_1592_);
stack->m_obj
 = v_res_1623_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___boxed(lean_object* v_as_1624_, lean_object* v_sz_1625_, lean_object* v_i_1626_, lean_object* v_b_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_){
_start:
{
size_t v_sz_boxed_1631_; size_t v_i_boxed_1632_; lean_object* v_res_1633_; 
v_sz_boxed_1631_ = lean_unbox_usize(v_sz_1625_);
lean_dec(v_sz_1625_);
v_i_boxed_1632_ = lean_unbox_usize(v_i_1626_);
lean_dec(v_i_1626_);
v_res_1633_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6(v_as_1624_, v_sz_boxed_1631_, v_i_boxed_1632_, v_b_1627_, v___y_1628_, v___y_1629_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
lean_dec_ref(v_as_1624_);
return v_res_1633_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1640_ = lean_box(0);
v___x_1641_ = lean_unsigned_to_nat(16u);
v___x_1642_ = lean_mk_array(v___x_1641_, v___x_1640_);
return v___x_1642_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1643_ = lean_obj_once(&l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__4, &l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__4_once, _init_l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__4);
v___x_1644_ = lean_unsigned_to_nat(0u);
v___x_1645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1644_);
lean_ctor_set(v___x_1645_, 1, v___x_1643_);
return v___x_1645_;
}
}
lean_object* l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0(lean_object* v___x_1646_, lean_object* v_stx_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1675_; lean_object* v___y_1676_; lean_object* v___y_1677_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1689_; lean_object* v___y_1690_; lean_object* v___y_1698_; lean_object* v___y_1699_; lean_object* v___y_1700_; lean_object* v___x_1723_; lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1779_; 
v___x_1723_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1(v___y_1648_, v___y_1649_);
v_a_1724_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1726_ = v___x_1723_;
v_isShared_1727_ = v_isSharedCheck_1779_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1723_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1779_;
goto v_resetjp_1725_;
}
v___jp_1651_:
{
size_t v_sz_1654_; size_t v___x_1655_; lean_object* v___x_1656_; 
v_sz_1654_ = lean_array_size(v___y_1653_);
v___x_1655_ = ((size_t)0ULL);
v___x_1656_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6(v___y_1653_, v_sz_1654_, v___x_1655_, v___y_1652_, v___y_1648_, v___y_1649_);
lean_dec_ref(v___y_1653_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1664_; 
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1664_ == 0)
{
lean_object* v_unused_1665_; 
v_unused_1665_ = lean_ctor_get(v___x_1656_, 0);
lean_dec(v_unused_1665_);
v___x_1658_ = v___x_1656_;
v_isShared_1659_ = v_isSharedCheck_1664_;
goto v_resetjp_1657_;
}
else
{
lean_dec(v___x_1656_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1664_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1660_; lean_object* v___x_1662_; 
v___x_1660_ = lean_box(0);
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 0, v___x_1660_);
v___x_1662_ = v___x_1658_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v___x_1660_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
else
{
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1673_; 
v_a_1666_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1668_ = v___x_1656_;
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v___x_1656_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1671_; 
if (v_isShared_1669_ == 0)
{
v___x_1671_ = v___x_1668_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_a_1666_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
}
v___jp_1674_:
{
lean_object* v___x_1680_; 
v___x_1680_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg(v___y_1675_, v___y_1676_, v___y_1678_, v___y_1679_);
lean_dec(v___y_1679_);
lean_dec(v___y_1675_);
v___y_1652_ = v___y_1677_;
v___y_1653_ = v___x_1680_;
goto v___jp_1651_;
}
v___jp_1681_:
{
uint8_t v___x_1687_; 
v___x_1687_ = lean_nat_dec_le(v___y_1686_, v___y_1685_);
if (v___x_1687_ == 0)
{
lean_dec(v___y_1685_);
lean_inc(v___y_1686_);
v___y_1675_ = v___y_1682_;
v___y_1676_ = v___y_1683_;
v___y_1677_ = v___y_1684_;
v___y_1678_ = v___y_1686_;
v___y_1679_ = v___y_1686_;
goto v___jp_1674_;
}
else
{
v___y_1675_ = v___y_1682_;
v___y_1676_ = v___y_1683_;
v___y_1677_ = v___y_1684_;
v___y_1678_ = v___y_1686_;
v___y_1679_ = v___y_1685_;
goto v___jp_1674_;
}
}
v___jp_1688_:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; uint8_t v___x_1693_; 
lean_inc_n(v___y_1689_, 2);
v___x_1691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1691_, 0, v___y_1689_);
lean_ctor_set(v___x_1691_, 1, v___y_1689_);
v___x_1692_ = lean_array_get_size(v___y_1690_);
v___x_1693_ = lean_nat_dec_eq(v___x_1692_, v___y_1689_);
if (v___x_1693_ == 0)
{
lean_object* v___x_1694_; lean_object* v___x_1695_; uint8_t v___x_1696_; 
v___x_1694_ = lean_unsigned_to_nat(1u);
v___x_1695_ = lean_nat_sub(v___x_1692_, v___x_1694_);
v___x_1696_ = lean_nat_dec_le(v___y_1689_, v___x_1695_);
if (v___x_1696_ == 0)
{
lean_dec(v___y_1689_);
lean_inc(v___x_1695_);
v___y_1682_ = v___x_1692_;
v___y_1683_ = v___y_1690_;
v___y_1684_ = v___x_1691_;
v___y_1685_ = v___x_1695_;
v___y_1686_ = v___x_1695_;
goto v___jp_1681_;
}
else
{
v___y_1682_ = v___x_1692_;
v___y_1683_ = v___y_1690_;
v___y_1684_ = v___x_1691_;
v___y_1685_ = v___x_1695_;
v___y_1686_ = v___y_1689_;
goto v___jp_1681_;
}
}
else
{
lean_dec(v___y_1689_);
v___y_1652_ = v___x_1691_;
v___y_1653_ = v___y_1690_;
goto v___jp_1651_;
}
}
v___jp_1697_:
{
if (lean_obj_tag(v___y_1700_) == 0)
{
lean_object* v___x_1701_; lean_object* v_size_1702_; lean_object* v_buckets_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; uint8_t v___x_1706_; 
lean_dec_ref_known(v___y_1700_, 1);
v___x_1701_ = lean_st_ref_get(v___y_1699_);
lean_dec(v___y_1699_);
v_size_1702_ = lean_ctor_get(v___x_1701_, 0);
lean_inc(v_size_1702_);
v_buckets_1703_ = lean_ctor_get(v___x_1701_, 1);
lean_inc_ref(v_buckets_1703_);
lean_dec(v___x_1701_);
v___x_1704_ = lean_mk_empty_array_with_capacity(v_size_1702_);
lean_dec(v_size_1702_);
v___x_1705_ = lean_array_get_size(v_buckets_1703_);
v___x_1706_ = lean_nat_dec_lt(v___y_1698_, v___x_1705_);
if (v___x_1706_ == 0)
{
lean_dec_ref(v_buckets_1703_);
v___y_1689_ = v___y_1698_;
v___y_1690_ = v___x_1704_;
goto v___jp_1688_;
}
else
{
size_t v___x_1707_; size_t v___x_1708_; lean_object* v___x_1709_; 
v___x_1707_ = ((size_t)0ULL);
v___x_1708_ = lean_usize_of_nat(v___x_1705_);
v___x_1709_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9(v_buckets_1703_, v___x_1707_, v___x_1708_, v___x_1704_);
lean_dec_ref(v_buckets_1703_);
v___y_1689_ = v___y_1698_;
v___y_1690_ = v___x_1709_;
goto v___jp_1688_;
}
}
else
{
lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1722_; 
lean_dec(v___y_1699_);
lean_dec(v___y_1698_);
v_a_1710_ = lean_ctor_get(v___y_1700_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___y_1700_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1712_ = v___y_1700_;
v_isShared_1713_ = v_isSharedCheck_1722_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_dec(v___y_1700_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1722_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v_ref_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1720_; 
v_ref_1714_ = lean_ctor_get(v___y_1648_, 7);
v___x_1715_ = lean_io_error_to_string(v_a_1710_);
v___x_1716_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1715_);
v___x_1717_ = l_Lean_MessageData_ofFormat(v___x_1716_);
lean_inc(v_ref_1714_);
v___x_1718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1718_, 0, v_ref_1714_);
lean_ctor_set(v___x_1718_, 1, v___x_1717_);
if (v_isShared_1713_ == 0)
{
lean_ctor_set(v___x_1712_, 0, v___x_1718_);
v___x_1720_ = v___x_1712_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v___x_1718_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
}
v_resetjp_1725_:
{
lean_object* v___x_1728_; uint8_t v___y_1730_; lean_object* v___x_1775_; uint8_t v___x_1776_; 
v___x_1728_ = lean_st_ref_get(v___y_1649_);
v___x_1775_ = l_Lean_Linter_Extra_linter_extra_unreachableTactic;
v___x_1776_ = l_Lean_Linter_getLinterValue(v___x_1775_, v_a_1724_);
lean_dec(v_a_1724_);
if (v___x_1776_ == 0)
{
lean_dec(v___x_1728_);
v___y_1730_ = v___x_1776_;
goto v___jp_1729_;
}
else
{
lean_object* v_infoState_1777_; uint8_t v_enabled_1778_; 
v_infoState_1777_ = lean_ctor_get(v___x_1728_, 8);
lean_inc_ref(v_infoState_1777_);
lean_dec(v___x_1728_);
v_enabled_1778_ = lean_ctor_get_uint8(v_infoState_1777_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1777_);
v___y_1730_ = v_enabled_1778_;
goto v___jp_1729_;
}
v___jp_1729_:
{
if (v___y_1730_ == 0)
{
lean_object* v___x_1731_; lean_object* v___x_1733_; 
lean_dec(v_stx_1647_);
v___x_1731_ = lean_box(0);
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 0, v___x_1731_);
v___x_1733_ = v___x_1726_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v___x_1731_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
else
{
lean_object* v___x_1735_; lean_object* v_messages_1736_; uint8_t v___x_1737_; 
v___x_1735_ = lean_st_ref_get(v___y_1649_);
v_messages_1736_ = lean_ctor_get(v___x_1735_, 1);
lean_inc_ref(v_messages_1736_);
lean_dec(v___x_1735_);
v___x_1737_ = l_Lean_MessageLog_hasErrors(v_messages_1736_);
lean_dec_ref(v_messages_1736_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1738_; lean_object* v_env_1739_; lean_object* v___x_1740_; lean_object* v_ext_1741_; lean_object* v_toEnvExtension_1742_; lean_object* v_asyncMode_1743_; lean_object* v___x_1744_; lean_object* v_categories_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
v___x_1738_ = lean_st_ref_get(v___y_1649_);
v_env_1739_ = lean_ctor_get(v___x_1738_, 0);
lean_inc_ref(v_env_1739_);
lean_dec(v___x_1738_);
v___x_1740_ = l_Lean_Parser_parserExtension;
v_ext_1741_ = lean_ctor_get(v___x_1740_, 1);
v_toEnvExtension_1742_ = lean_ctor_get(v_ext_1741_, 0);
v_asyncMode_1743_ = lean_ctor_get(v_toEnvExtension_1742_, 2);
v___x_1744_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1646_, v___x_1740_, v_env_1739_, v_asyncMode_1743_, v___x_1737_);
v_categories_1745_ = lean_ctor_get(v___x_1744_, 2);
lean_inc_ref(v_categories_1745_);
lean_dec(v___x_1744_);
v___x_1746_ = ((lean_object*)(l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__1));
v___x_1747_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3___redArg(v_categories_1745_, v___x_1746_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v___x_1748_; lean_object* v___x_1750_; 
lean_dec_ref(v_categories_1745_);
lean_dec(v_stx_1647_);
v___x_1748_ = lean_box(0);
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 0, v___x_1748_);
v___x_1750_ = v___x_1726_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v___x_1748_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
else
{
lean_object* v_val_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v_val_1752_ = lean_ctor_get(v___x_1747_, 0);
lean_inc(v_val_1752_);
lean_dec_ref_known(v___x_1747_, 1);
v___x_1753_ = ((lean_object*)(l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__3));
v___x_1754_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3___redArg(v_categories_1745_, v___x_1753_);
lean_dec_ref(v_categories_1745_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v___x_1755_; lean_object* v___x_1757_; 
lean_dec(v_val_1752_);
lean_dec(v_stx_1647_);
v___x_1755_ = lean_box(0);
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 0, v___x_1755_);
v___x_1757_ = v___x_1726_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1755_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
else
{
lean_object* v_val_1759_; lean_object* v_kinds_1760_; lean_object* v_kinds_1761_; lean_object* v___x_1762_; lean_object* v_a_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
lean_del_object(v___x_1726_);
v_val_1759_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_val_1759_);
lean_dec_ref_known(v___x_1754_, 1);
v_kinds_1760_ = lean_ctor_get(v_val_1752_, 1);
lean_inc_ref(v_kinds_1760_);
lean_dec(v_val_1752_);
v_kinds_1761_ = lean_ctor_get(v_val_1759_, 1);
lean_inc_ref(v_kinds_1761_);
lean_dec(v_val_1759_);
v___x_1762_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___redArg(v___y_1649_);
v_a_1763_ = lean_ctor_get(v___x_1762_, 0);
lean_inc(v_a_1763_);
lean_dec_ref(v___x_1762_);
v___x_1764_ = l_Lean_Linter_Extra_UnreachableTactic_ignoreTacticKindsRef;
v___x_1765_ = lean_unsigned_to_nat(0u);
v___x_1766_ = lean_obj_once(&l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__5, &l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__5_once, _init_l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__5);
v___x_1767_ = lean_st_mk_ref(v___x_1766_);
v___x_1768_ = lean_st_ref_get(v___x_1764_);
v___x_1769_ = l_Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10(v_kinds_1760_, v_kinds_1761_, v___y_1730_, v___x_1768_, v_stx_1647_, v___x_1767_);
lean_dec(v___x_1768_);
lean_dec_ref(v_kinds_1761_);
lean_dec_ref(v_kinds_1760_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v___x_1770_; 
lean_dec_ref_known(v___x_1769_, 1);
v___x_1770_ = l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList(v_a_1763_, v___x_1767_);
v___y_1698_ = v___x_1765_;
v___y_1699_ = v___x_1767_;
v___y_1700_ = v___x_1770_;
goto v___jp_1697_;
}
else
{
lean_dec(v_a_1763_);
v___y_1698_ = v___x_1765_;
v___y_1699_ = v___x_1767_;
v___y_1700_ = v___x_1769_;
goto v___jp_1697_;
}
}
}
}
else
{
lean_object* v___x_1771_; lean_object* v___x_1773_; 
lean_dec(v_stx_1647_);
v___x_1771_ = lean_box(0);
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 0, v___x_1771_);
v___x_1773_ = v___x_1726_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v___x_1771_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1646_ = stack[0].m_obj;
lean_object* v_stx_1647_ = stack[1].m_obj;
lean_object* v___y_1648_ = stack[2].m_obj;
lean_object* v___y_1649_ = stack[3].m_obj;
lean_object* v_res_1780_;
v_res_1780_ = l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0(v___x_1646_, v_stx_1647_, v___y_1648_, v___y_1649_);
stack->m_obj
 = v_res_1780_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___boxed(lean_object* v___x_1781_, lean_object* v_stx_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0(v___x_1781_, v_stx_1782_, v___y_1783_, v___y_1784_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec_ref(v___x_1781_);
return v_res_1786_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__0(void){
_start:
{
lean_object* v___x_1787_; lean_object* v___f_1788_; 
v___x_1787_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___f_1788_ = lean_alloc_closure((void*)(l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___boxed), 5, 1);
lean_closure_set(v___f_1788_, 0, v___x_1787_);
return v___f_1788_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__1(void){
_start:
{
lean_object* v___f_1789_; lean_object* v___x_1790_; 
v___f_1789_ = lean_obj_once(&l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__0, &l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__0_once, _init_l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__0);
v___x_1790_ = lean_alloc_closure((void*)(l_Lean_withSetOptionIn___boxed), 6, 2);
lean_closure_set(v___x_1790_, 0, lean_box(0));
lean_closure_set(v___x_1790_, 1, v___f_1789_);
return v___x_1790_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__5(void){
_start:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1799_ = ((lean_object*)(l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__4));
v___x_1800_ = lean_obj_once(&l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__1, &l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__1_once, _init_l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__1);
v___x_1801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1800_);
lean_ctor_set(v___x_1801_, 1, v___x_1799_);
return v___x_1801_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter(void){
_start:
{
lean_object* v___x_1802_; 
v___x_1802_ = lean_obj_once(&l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__5, &l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__5_once, _init_l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__5);
return v___x_1802_;
}
}
lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1(lean_object* v_o_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
lean_object* v___x_1807_; 
v___x_1807_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1___redArg(v_o_1803_, v___y_1805_);
return v___x_1807_;
}
}
LEAN_EXPORT void l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_1803_ = stack[0].m_obj;
lean_object* v___y_1804_ = stack[1].m_obj;
lean_object* v___y_1805_ = stack[2].m_obj;
lean_object* v_res_1808_;
v_res_1808_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1(v_o_1803_, v___y_1804_, v___y_1805_);
stack->m_obj
 = v_res_1808_;
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1___boxed(lean_object* v_o_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1(v_o_1809_, v___y_1810_, v___y_1811_);
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3(lean_object* v_00_u03b2_1814_, lean_object* v_x_1815_, lean_object* v_x_1816_){
_start:
{
lean_object* v___x_1817_; 
v___x_1817_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3___redArg(v_x_1815_, v_x_1816_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3___boxed(lean_object* v_00_u03b2_1818_, lean_object* v_x_1819_, lean_object* v_x_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3(v_00_u03b2_1818_, v_x_1819_, v_x_1820_);
lean_dec(v_x_1820_);
lean_dec_ref(v_x_1819_);
return v_res_1821_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4(lean_object* v_00_u03b2_1822_, lean_object* v_x_1823_, lean_object* v_x_1824_){
_start:
{
uint8_t v___x_1825_; 
v___x_1825_ = l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4___redArg(v_x_1823_, v_x_1824_);
return v___x_1825_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1823_ = stack[1].m_obj;
lean_object* v_x_1824_ = stack[2].m_obj;
uint8_t v_res_1826_;
v_res_1826_ = l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4(lean_box(0), v_x_1823_, v_x_1824_);
stack->m_num = v_res_1826_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4___boxed(lean_object* v_00_u03b2_1827_, lean_object* v_x_1828_, lean_object* v_x_1829_){
_start:
{
uint8_t v_res_1830_; lean_object* v_r_1831_; 
v_res_1830_ = l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4(v_00_u03b2_1827_, v_x_1828_, v_x_1829_);
lean_dec(v_x_1829_);
lean_dec_ref(v_x_1828_);
v_r_1831_ = lean_box(v_res_1830_);
return v_r_1831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7(lean_object* v_n_1832_, lean_object* v_as_1833_, lean_object* v_lo_1834_, lean_object* v_hi_1835_, lean_object* v_w_1836_, lean_object* v_hlo_1837_, lean_object* v_hhi_1838_){
_start:
{
lean_object* v___x_1839_; 
v___x_1839_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___redArg(v_n_1832_, v_as_1833_, v_lo_1834_, v_hi_1835_);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___boxed(lean_object* v_n_1840_, lean_object* v_as_1841_, lean_object* v_lo_1842_, lean_object* v_hi_1843_, lean_object* v_w_1844_, lean_object* v_hlo_1845_, lean_object* v_hhi_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7(v_n_1840_, v_as_1841_, v_lo_1842_, v_hi_1843_, v_w_1844_, v_hlo_1845_, v_hhi_1846_);
lean_dec(v_hi_1843_);
lean_dec(v_n_1840_);
return v_res_1847_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5(lean_object* v_00_u03b2_1848_, lean_object* v_x_1849_, size_t v_x_1850_, lean_object* v_x_1851_){
_start:
{
lean_object* v___x_1852_; 
v___x_1852_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5___redArg(v_x_1849_, v_x_1850_, v_x_1851_);
return v___x_1852_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1849_ = stack[1].m_obj;
size_t v_x_1850_ = stack[2].m_num;
lean_object* v_x_1851_ = stack[3].m_obj;
lean_object* v_res_1853_;
v_res_1853_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5(lean_box(0), v_x_1849_, v_x_1850_, v_x_1851_);
stack->m_obj
 = v_res_1853_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5___boxed(lean_object* v_00_u03b2_1854_, lean_object* v_x_1855_, lean_object* v_x_1856_, lean_object* v_x_1857_){
_start:
{
size_t v_x_13547__boxed_1858_; lean_object* v_res_1859_; 
v_x_13547__boxed_1858_ = lean_unbox_usize(v_x_1856_);
lean_dec(v_x_1856_);
v_res_1859_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5(v_00_u03b2_1854_, v_x_1855_, v_x_13547__boxed_1858_, v_x_1857_);
lean_dec(v_x_1857_);
lean_dec_ref(v_x_1855_);
return v_res_1859_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4_spec__7(lean_object* v_00_u03b2_1860_, lean_object* v_x_1861_, size_t v_x_1862_, lean_object* v_x_1863_){
_start:
{
uint8_t v___x_1864_; 
v___x_1864_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4_spec__7___redArg(v_x_1861_, v_x_1862_, v_x_1863_);
return v___x_1864_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1861_ = stack[1].m_obj;
size_t v_x_1862_ = stack[2].m_num;
lean_object* v_x_1863_ = stack[3].m_obj;
uint8_t v_res_1865_;
v_res_1865_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4_spec__7(lean_box(0), v_x_1861_, v_x_1862_, v_x_1863_);
stack->m_num = v_res_1865_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4_spec__7___boxed(lean_object* v_00_u03b2_1866_, lean_object* v_x_1867_, lean_object* v_x_1868_, lean_object* v_x_1869_){
_start:
{
size_t v_x_13565__boxed_1870_; uint8_t v_res_1871_; lean_object* v_r_1872_; 
v_x_13565__boxed_1870_ = lean_unbox_usize(v_x_1868_);
lean_dec(v_x_1868_);
v_res_1871_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4_spec__7(v_00_u03b2_1866_, v_x_1867_, v_x_13565__boxed_1870_, v_x_1869_);
lean_dec(v_x_1869_);
lean_dec_ref(v_x_1867_);
v_r_1872_ = lean_box(v_res_1871_);
return v_r_1872_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7_spec__11(lean_object* v_n_1873_, lean_object* v_lo_1874_, lean_object* v_hi_1875_, lean_object* v_hhi_1876_, lean_object* v_pivot_1877_, lean_object* v_as_1878_, lean_object* v_i_1879_, lean_object* v_k_1880_, lean_object* v_ilo_1881_, lean_object* v_ik_1882_, lean_object* v_w_1883_){
_start:
{
lean_object* v___x_1884_; 
v___x_1884_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7_spec__11___redArg(v_hi_1875_, v_pivot_1877_, v_as_1878_, v_i_1879_, v_k_1880_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7_spec__11___boxed(lean_object* v_n_1885_, lean_object* v_lo_1886_, lean_object* v_hi_1887_, lean_object* v_hhi_1888_, lean_object* v_pivot_1889_, lean_object* v_as_1890_, lean_object* v_i_1891_, lean_object* v_k_1892_, lean_object* v_ilo_1893_, lean_object* v_ik_1894_, lean_object* v_w_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7_spec__11(v_n_1885_, v_lo_1886_, v_hi_1887_, v_hhi_1888_, v_pivot_1889_, v_as_1890_, v_i_1891_, v_k_1892_, v_ilo_1893_, v_ik_1894_, v_w_1895_);
lean_dec(v_hi_1887_);
lean_dec(v_lo_1886_);
lean_dec(v_n_1885_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15(lean_object* v_00_u03b2_1897_, lean_object* v_m_1898_, lean_object* v_a_1899_, lean_object* v_b_1900_){
_start:
{
lean_object* v___x_1901_; 
v___x_1901_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15___redArg(v_m_1898_, v_a_1899_, v_b_1900_);
return v___x_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8(lean_object* v_00_u03b2_1902_, lean_object* v_keys_1903_, lean_object* v_vals_1904_, lean_object* v_heq_1905_, lean_object* v_i_1906_, lean_object* v_k_1907_){
_start:
{
lean_object* v___x_1908_; 
v___x_1908_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8___redArg(v_keys_1903_, v_vals_1904_, v_i_1906_, v_k_1907_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1909_, lean_object* v_keys_1910_, lean_object* v_vals_1911_, lean_object* v_heq_1912_, lean_object* v_i_1913_, lean_object* v_k_1914_){
_start:
{
lean_object* v_res_1915_; 
v_res_1915_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8(v_00_u03b2_1909_, v_keys_1910_, v_vals_1911_, v_heq_1912_, v_i_1913_, v_k_1914_);
lean_dec(v_k_1914_);
lean_dec_ref(v_vals_1911_);
lean_dec_ref(v_keys_1910_);
return v_res_1915_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4_spec__7_spec__11(lean_object* v_00_u03b2_1916_, lean_object* v_keys_1917_, lean_object* v_vals_1918_, lean_object* v_heq_1919_, lean_object* v_i_1920_, lean_object* v_k_1921_){
_start:
{
uint8_t v___x_1922_; 
v___x_1922_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4_spec__7_spec__11___redArg(v_keys_1917_, v_i_1920_, v_k_1921_);
return v___x_1922_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4_spec__7_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_1917_ = stack[1].m_obj;
lean_object* v_vals_1918_ = stack[2].m_obj;
lean_object* v_i_1920_ = stack[4].m_obj;
lean_object* v_k_1921_ = stack[5].m_obj;
uint8_t v_res_1923_;
v_res_1923_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4_spec__7_spec__11(lean_box(0), v_keys_1917_, v_vals_1918_, lean_box(0), v_i_1920_, v_k_1921_);
stack->m_num = v_res_1923_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4_spec__7_spec__11___boxed(lean_object* v_00_u03b2_1924_, lean_object* v_keys_1925_, lean_object* v_vals_1926_, lean_object* v_heq_1927_, lean_object* v_i_1928_, lean_object* v_k_1929_){
_start:
{
uint8_t v_res_1930_; lean_object* v_r_1931_; 
v_res_1930_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4_spec__7_spec__11(v_00_u03b2_1924_, v_keys_1925_, v_vals_1926_, v_heq_1927_, v_i_1928_, v_k_1929_);
lean_dec(v_k_1929_);
lean_dec_ref(v_vals_1926_);
lean_dec_ref(v_keys_1925_);
v_r_1931_ = lean_box(v_res_1930_);
return v_r_1931_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19(lean_object* v_00_u03b2_1932_, lean_object* v_data_1933_){
_start:
{
lean_object* v___x_1934_; 
v___x_1934_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19___redArg(v_data_1933_);
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__20(lean_object* v_00_u03b2_1935_, lean_object* v_a_1936_, lean_object* v_b_1937_, lean_object* v_x_1938_){
_start:
{
lean_object* v___x_1939_; 
v___x_1939_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__20___redArg(v_a_1936_, v_b_1937_, v_x_1938_);
return v___x_1939_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19(lean_object* v_msgData_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v___x_1944_; 
v___x_1944_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg(v_msgData_1940_, v___y_1942_);
return v___x_1944_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1940_ = stack[0].m_obj;
lean_object* v___y_1941_ = stack[1].m_obj;
lean_object* v___y_1942_ = stack[2].m_obj;
lean_object* v_res_1945_;
v_res_1945_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19(v_msgData_1940_, v___y_1941_, v___y_1942_);
stack->m_obj
 = v_res_1945_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___boxed(lean_object* v_msgData_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_){
_start:
{
lean_object* v_res_1950_; 
v_res_1950_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19(v_msgData_1946_, v___y_1947_, v___y_1948_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19_spec__21(lean_object* v_00_u03b2_1951_, lean_object* v_i_1952_, lean_object* v_source_1953_, lean_object* v_target_1954_){
_start:
{
lean_object* v___x_1955_; 
v___x_1955_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19_spec__21___redArg(v_i_1952_, v_source_1953_, v_target_1954_);
return v___x_1955_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19_spec__21_spec__25(lean_object* v_00_u03b2_1956_, lean_object* v_x_1957_, lean_object* v_x_1958_){
_start:
{
lean_object* v___x_1959_; 
v___x_1959_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19_spec__21_spec__25___redArg(v_x_1957_, v_x_1958_);
return v___x_1959_;
}
}
lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_1366347041____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1961_ = l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter;
v___x_1962_ = l_Lean_Elab_Command_addLinter(v___x_1961_);
return v___x_1962_;
}
}
LEAN_EXPORT void l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_1366347041____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1963_;
v_res_1963_ = l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_1366347041____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1963_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_1366347041____hygCtx___hyg_2____boxed(lean_object* v_a_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_1366347041____hygCtx___hyg_2_();
return v_res_1965_;
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
l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter = _init_l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter();
lean_mark_persistent(l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter);
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
