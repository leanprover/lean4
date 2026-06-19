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
uint8_t l_Lean_Syntax_instBEqRange_beq(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Syntax_instBEqRange_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_instHashableRange_hash___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_NameHashSet_contains(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l_instOrdNat___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instOrdInt___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_lexOrd___redArg(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
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
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
extern lean_object* l_Lean_Linter_linterSetsExt;
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
extern lean_object* l_Lean_Linter_linterMessageTag;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
extern lean_object* l_Lean_Parser_parserExtension;
extern lean_object* l_Lean_Parser_ParserExtension_instInhabitedState_default;
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameHashSet_insert(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_withSetOptionIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "this tactic is never executed"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13_spec__16___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19_spec__21_spec__25___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19_spec__21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__20___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___lam__0(lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instOrdNat___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9___redArg___closed__0_value;
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instOrdInt___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__0 = (const lean_object*)&l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__0_value;
static const lean_closure_object l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_withSetOptionIn___boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__0_value)} };
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__20(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19_spec__21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19_spec__21_spec__25(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_a_64_, lean_object* v_x_65_){
_start:
{
if (lean_obj_tag(v_x_65_) == 0)
{
uint8_t v___x_66_; 
v___x_66_ = 0;
return v___x_66_;
}
else
{
lean_object* v_key_67_; lean_object* v_tail_68_; uint8_t v___x_69_; 
v_key_67_ = lean_ctor_get(v_x_65_, 0);
v_tail_68_ = lean_ctor_get(v_x_65_, 2);
v___x_69_ = lean_name_eq(v_key_67_, v_a_64_);
if (v___x_69_ == 0)
{
v_x_65_ = v_tail_68_;
goto _start;
}
else
{
return v___x_69_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_a_71_, lean_object* v_x_72_){
_start:
{
uint8_t v_res_73_; lean_object* v_r_74_; 
v_res_73_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_71_, v_x_72_);
lean_dec(v_x_72_);
lean_dec(v_a_71_);
v_r_74_ = lean_box(v_res_73_);
return v_r_74_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_75_; uint64_t v___x_76_; 
v___x_75_ = lean_unsigned_to_nat(1723u);
v___x_76_ = lean_uint64_of_nat(v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_77_, lean_object* v_x_78_){
_start:
{
if (lean_obj_tag(v_x_78_) == 0)
{
return v_x_77_;
}
else
{
lean_object* v_key_79_; lean_object* v_value_80_; lean_object* v_tail_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_107_; 
v_key_79_ = lean_ctor_get(v_x_78_, 0);
v_value_80_ = lean_ctor_get(v_x_78_, 1);
v_tail_81_ = lean_ctor_get(v_x_78_, 2);
v_isSharedCheck_107_ = !lean_is_exclusive(v_x_78_);
if (v_isSharedCheck_107_ == 0)
{
v___x_83_ = v_x_78_;
v_isShared_84_ = v_isSharedCheck_107_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_tail_81_);
lean_inc(v_value_80_);
lean_inc(v_key_79_);
lean_dec(v_x_78_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_107_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_85_; uint64_t v___y_87_; 
v___x_85_ = lean_array_get_size(v_x_77_);
if (lean_obj_tag(v_key_79_) == 0)
{
uint64_t v___x_105_; 
v___x_105_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
v___y_87_ = v___x_105_;
goto v___jp_86_;
}
else
{
uint64_t v_hash_106_; 
v_hash_106_ = lean_ctor_get_uint64(v_key_79_, sizeof(void*)*2);
v___y_87_ = v_hash_106_;
goto v___jp_86_;
}
v___jp_86_:
{
uint64_t v___x_88_; uint64_t v___x_89_; uint64_t v_fold_90_; uint64_t v___x_91_; uint64_t v___x_92_; uint64_t v___x_93_; size_t v___x_94_; size_t v___x_95_; size_t v___x_96_; size_t v___x_97_; size_t v___x_98_; lean_object* v___x_99_; lean_object* v___x_101_; 
v___x_88_ = 32ULL;
v___x_89_ = lean_uint64_shift_right(v___y_87_, v___x_88_);
v_fold_90_ = lean_uint64_xor(v___y_87_, v___x_89_);
v___x_91_ = 16ULL;
v___x_92_ = lean_uint64_shift_right(v_fold_90_, v___x_91_);
v___x_93_ = lean_uint64_xor(v_fold_90_, v___x_92_);
v___x_94_ = lean_uint64_to_usize(v___x_93_);
v___x_95_ = lean_usize_of_nat(v___x_85_);
v___x_96_ = ((size_t)1ULL);
v___x_97_ = lean_usize_sub(v___x_95_, v___x_96_);
v___x_98_ = lean_usize_land(v___x_94_, v___x_97_);
v___x_99_ = lean_array_uget_borrowed(v_x_77_, v___x_98_);
lean_inc(v___x_99_);
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 2, v___x_99_);
v___x_101_ = v___x_83_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v_key_79_);
lean_ctor_set(v_reuseFailAlloc_104_, 1, v_value_80_);
lean_ctor_set(v_reuseFailAlloc_104_, 2, v___x_99_);
v___x_101_ = v_reuseFailAlloc_104_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
lean_object* v___x_102_; 
v___x_102_ = lean_array_uset(v_x_77_, v___x_98_, v___x_101_);
v_x_77_ = v___x_102_;
v_x_78_ = v_tail_81_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(lean_object* v_i_108_, lean_object* v_source_109_, lean_object* v_target_110_){
_start:
{
lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_111_ = lean_array_get_size(v_source_109_);
v___x_112_ = lean_nat_dec_lt(v_i_108_, v___x_111_);
if (v___x_112_ == 0)
{
lean_dec_ref(v_source_109_);
lean_dec(v_i_108_);
return v_target_110_;
}
else
{
lean_object* v_es_113_; lean_object* v___x_114_; lean_object* v_source_115_; lean_object* v_target_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v_es_113_ = lean_array_fget(v_source_109_, v_i_108_);
v___x_114_ = lean_box(0);
v_source_115_ = lean_array_fset(v_source_109_, v_i_108_, v___x_114_);
v_target_116_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg(v_target_110_, v_es_113_);
v___x_117_ = lean_unsigned_to_nat(1u);
v___x_118_ = lean_nat_add(v_i_108_, v___x_117_);
lean_dec(v_i_108_);
v_i_108_ = v___x_118_;
v_source_109_ = v_source_115_;
v_target_110_ = v_target_116_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_data_120_){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v_nbuckets_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_121_ = lean_array_get_size(v_data_120_);
v___x_122_ = lean_unsigned_to_nat(2u);
v_nbuckets_123_ = lean_nat_mul(v___x_121_, v___x_122_);
v___x_124_ = lean_unsigned_to_nat(0u);
v___x_125_ = lean_box(0);
v___x_126_ = lean_mk_array(v_nbuckets_123_, v___x_125_);
v___x_127_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v___x_124_, v_data_120_, v___x_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(lean_object* v_m_128_, lean_object* v_a_129_, lean_object* v_b_130_){
_start:
{
lean_object* v_size_131_; lean_object* v_buckets_132_; lean_object* v___x_133_; uint64_t v___y_135_; 
v_size_131_ = lean_ctor_get(v_m_128_, 0);
v_buckets_132_ = lean_ctor_get(v_m_128_, 1);
v___x_133_ = lean_array_get_size(v_buckets_132_);
if (lean_obj_tag(v_a_129_) == 0)
{
uint64_t v___x_172_; 
v___x_172_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
v___y_135_ = v___x_172_;
goto v___jp_134_;
}
else
{
uint64_t v_hash_173_; 
v_hash_173_ = lean_ctor_get_uint64(v_a_129_, sizeof(void*)*2);
v___y_135_ = v_hash_173_;
goto v___jp_134_;
}
v___jp_134_:
{
uint64_t v___x_136_; uint64_t v___x_137_; uint64_t v_fold_138_; uint64_t v___x_139_; uint64_t v___x_140_; uint64_t v___x_141_; size_t v___x_142_; size_t v___x_143_; size_t v___x_144_; size_t v___x_145_; size_t v___x_146_; lean_object* v_bkt_147_; uint8_t v___x_148_; 
v___x_136_ = 32ULL;
v___x_137_ = lean_uint64_shift_right(v___y_135_, v___x_136_);
v_fold_138_ = lean_uint64_xor(v___y_135_, v___x_137_);
v___x_139_ = 16ULL;
v___x_140_ = lean_uint64_shift_right(v_fold_138_, v___x_139_);
v___x_141_ = lean_uint64_xor(v_fold_138_, v___x_140_);
v___x_142_ = lean_uint64_to_usize(v___x_141_);
v___x_143_ = lean_usize_of_nat(v___x_133_);
v___x_144_ = ((size_t)1ULL);
v___x_145_ = lean_usize_sub(v___x_143_, v___x_144_);
v___x_146_ = lean_usize_land(v___x_142_, v___x_145_);
v_bkt_147_ = lean_array_uget_borrowed(v_buckets_132_, v___x_146_);
v___x_148_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_129_, v_bkt_147_);
if (v___x_148_ == 0)
{
lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_169_; 
lean_inc_ref(v_buckets_132_);
lean_inc(v_size_131_);
v_isSharedCheck_169_ = !lean_is_exclusive(v_m_128_);
if (v_isSharedCheck_169_ == 0)
{
lean_object* v_unused_170_; lean_object* v_unused_171_; 
v_unused_170_ = lean_ctor_get(v_m_128_, 1);
lean_dec(v_unused_170_);
v_unused_171_ = lean_ctor_get(v_m_128_, 0);
lean_dec(v_unused_171_);
v___x_150_ = v_m_128_;
v_isShared_151_ = v_isSharedCheck_169_;
goto v_resetjp_149_;
}
else
{
lean_dec(v_m_128_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_169_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_152_; lean_object* v_size_x27_153_; lean_object* v___x_154_; lean_object* v_buckets_x27_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; uint8_t v___x_161_; 
v___x_152_ = lean_unsigned_to_nat(1u);
v_size_x27_153_ = lean_nat_add(v_size_131_, v___x_152_);
lean_dec(v_size_131_);
lean_inc(v_bkt_147_);
v___x_154_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_154_, 0, v_a_129_);
lean_ctor_set(v___x_154_, 1, v_b_130_);
lean_ctor_set(v___x_154_, 2, v_bkt_147_);
v_buckets_x27_155_ = lean_array_uset(v_buckets_132_, v___x_146_, v___x_154_);
v___x_156_ = lean_unsigned_to_nat(4u);
v___x_157_ = lean_nat_mul(v_size_x27_153_, v___x_156_);
v___x_158_ = lean_unsigned_to_nat(3u);
v___x_159_ = lean_nat_div(v___x_157_, v___x_158_);
lean_dec(v___x_157_);
v___x_160_ = lean_array_get_size(v_buckets_x27_155_);
v___x_161_ = lean_nat_dec_le(v___x_159_, v___x_160_);
lean_dec(v___x_159_);
if (v___x_161_ == 0)
{
lean_object* v_val_162_; lean_object* v___x_164_; 
v_val_162_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1___redArg(v_buckets_x27_155_);
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 1, v_val_162_);
lean_ctor_set(v___x_150_, 0, v_size_x27_153_);
v___x_164_ = v___x_150_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_size_x27_153_);
lean_ctor_set(v_reuseFailAlloc_165_, 1, v_val_162_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
else
{
lean_object* v___x_167_; 
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 1, v_buckets_x27_155_);
lean_ctor_set(v___x_150_, 0, v_size_x27_153_);
v___x_167_ = v___x_150_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_size_x27_153_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v_buckets_x27_155_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
}
else
{
lean_dec(v_b_130_);
lean_dec(v_a_129_);
return v_m_128_;
}
}
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__0_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_174_ = lean_box(0);
v___x_175_ = lean_unsigned_to_nat(16u);
v___x_176_ = lean_mk_array(v___x_175_, v___x_174_);
return v___x_176_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__1_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_177_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__0_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__0_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__0_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
v___x_178_ = lean_unsigned_to_nat(0u);
v___x_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
lean_ctor_set(v___x_179_, 1, v___x_177_);
return v___x_179_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_188_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__5_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_));
v___x_189_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__1_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__1_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__1_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
v___x_190_ = l_Lean_NameHashSet_insert(v___x_189_, v___x_188_);
return v___x_190_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_197_ = lean_box(0);
v___x_198_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__8_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_));
v___x_199_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
v___x_200_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___x_199_, v___x_198_, v___x_197_);
return v___x_200_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__13_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_208_ = lean_box(0);
v___x_209_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__12_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_));
v___x_210_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
v___x_211_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___x_210_, v___x_209_, v___x_208_);
return v___x_211_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__16_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_218_ = lean_box(0);
v___x_219_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__15_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_));
v___x_220_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__13_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__13_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__13_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
v___x_221_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___x_220_, v___x_219_, v___x_218_);
return v___x_221_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__20_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_229_ = lean_box(0);
v___x_230_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__19_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_));
v___x_231_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__16_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__16_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__16_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
v___x_232_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___x_231_, v___x_230_, v___x_229_);
return v___x_232_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__23_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_239_ = lean_box(0);
v___x_240_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__22_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_));
v___x_241_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__20_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__20_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__20_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
v___x_242_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___x_241_, v___x_240_, v___x_239_);
return v___x_242_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__26_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_249_ = lean_box(0);
v___x_250_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__25_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_));
v___x_251_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__23_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__23_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__23_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
v___x_252_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___x_251_, v___x_250_, v___x_249_);
return v___x_252_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__29_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_259_ = lean_box(0);
v___x_260_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__28_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_));
v___x_261_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__26_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__26_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__26_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
v___x_262_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___x_261_, v___x_260_, v___x_259_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_264_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__29_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__29_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__29_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
v___x_265_ = lean_st_mk_ref(v___x_264_);
v___x_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2____boxed(lean_object* v_a_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_();
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_269_, lean_object* v_m_270_, lean_object* v_a_271_, lean_object* v_b_272_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v_m_270_, v_a_271_, v_b_272_);
return v___x_273_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_274_, lean_object* v_a_275_, lean_object* v_x_276_){
_start:
{
uint8_t v___x_277_; 
v___x_277_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_275_, v_x_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_278_, lean_object* v_a_279_, lean_object* v_x_280_){
_start:
{
uint8_t v_res_281_; lean_object* v_r_282_; 
v_res_281_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_278_, v_a_279_, v_x_280_);
lean_dec(v_x_280_);
lean_dec(v_a_279_);
v_r_282_ = lean_box(v_res_281_);
return v_r_282_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_00_u03b2_283_, lean_object* v_data_284_){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1___redArg(v_data_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2(lean_object* v_00_u03b2_286_, lean_object* v_i_287_, lean_object* v_source_288_, lean_object* v_target_289_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v_i_287_, v_source_288_, v_target_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_291_, lean_object* v_x_292_, lean_object* v_x_293_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg(v_x_292_, v_x_293_);
return v___x_294_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_Extra_UnreachableTactic_isIgnoreTacticKind(lean_object* v_ignoreTacticKinds_296_, lean_object* v_k_297_){
_start:
{
if (lean_obj_tag(v_k_297_) == 1)
{
lean_object* v_str_298_; lean_object* v___x_299_; uint8_t v___x_300_; 
v_str_298_ = lean_ctor_get(v_k_297_, 1);
v___x_299_ = ((lean_object*)(l_Lean_Linter_Extra_UnreachableTactic_isIgnoreTacticKind___closed__0));
v___x_300_ = lean_string_dec_eq(v_str_298_, v___x_299_);
if (v___x_300_ == 0)
{
uint8_t v___x_301_; 
v___x_301_ = l_Lean_NameHashSet_contains(v_ignoreTacticKinds_296_, v_k_297_);
return v___x_301_;
}
else
{
return v___x_300_;
}
}
else
{
uint8_t v___x_302_; 
v___x_302_ = l_Lean_NameHashSet_contains(v_ignoreTacticKinds_296_, v_k_297_);
return v___x_302_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_isIgnoreTacticKind___boxed(lean_object* v_ignoreTacticKinds_303_, lean_object* v_k_304_){
_start:
{
uint8_t v_res_305_; lean_object* v_r_306_; 
v_res_305_ = l_Lean_Linter_Extra_UnreachableTactic_isIgnoreTacticKind(v_ignoreTacticKinds_303_, v_k_304_);
lean_dec(v_k_304_);
lean_dec_ref(v_ignoreTacticKinds_303_);
v_r_306_ = lean_box(v_res_305_);
return v_r_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_addIgnoreTacticKind(lean_object* v_kind_307_){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_309_ = l_Lean_Linter_Extra_UnreachableTactic_ignoreTacticKindsRef;
v___x_310_ = lean_st_ref_take(v___x_309_);
v___x_311_ = l_Lean_NameHashSet_insert(v___x_310_, v_kind_307_);
v___x_312_ = lean_st_ref_set(v___x_309_, v___x_311_);
v___x_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_addIgnoreTacticKind___boxed(lean_object* v_kind_314_, lean_object* v_a_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Lean_Linter_Extra_UnreachableTactic_addIgnoreTacticKind(v_kind_314_);
return v_res_316_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__0(void){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = l_instMonadEIO(lean_box(0));
return v___x_317_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__1(void){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = lean_obj_once(&l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__0, &l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__0_once, _init_l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__0);
v___x_319_ = l_StateRefT_x27_instMonad___redArg(v___x_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_getTactics___lam__0___boxed(lean_object* v_ignoreTacticKinds_322_, lean_object* v_isTacKind_323_, lean_object* v_x_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Lean_Linter_Extra_UnreachableTactic_getTactics___lam__0(v_ignoreTacticKinds_322_, v_isTacKind_323_, v_x_324_, v___y_325_, v___y_326_);
lean_dec(v___y_326_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_getTactics(lean_object* v_ignoreTacticKinds_329_, lean_object* v_isTacKind_330_, lean_object* v_stx_331_, lean_object* v_a_332_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = lean_obj_once(&l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__1, &l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__1_once, _init_l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__1);
if (lean_obj_tag(v_stx_331_) == 1)
{
lean_object* v_kind_335_; lean_object* v_args_336_; lean_object* v___y_338_; lean_object* v___y_362_; uint8_t v___x_363_; 
v_kind_335_ = lean_ctor_get(v_stx_331_, 1);
v_args_336_ = lean_ctor_get(v_stx_331_, 2);
v___x_363_ = l_Lean_Linter_Extra_UnreachableTactic_isIgnoreTacticKind(v_ignoreTacticKinds_329_, v_kind_335_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; lean_object* v___x_365_; uint8_t v___x_366_; 
v___x_364_ = lean_unsigned_to_nat(0u);
v___x_365_ = lean_array_get_size(v_args_336_);
v___x_366_ = lean_nat_dec_lt(v___x_364_, v___x_365_);
if (v___x_366_ == 0)
{
lean_dec_ref(v_ignoreTacticKinds_329_);
v___y_338_ = v_a_332_;
goto v___jp_337_;
}
else
{
lean_object* v___f_367_; lean_object* v___x_368_; uint8_t v___x_369_; 
lean_inc_ref(v_isTacKind_330_);
v___f_367_ = lean_alloc_closure((void*)(l_Lean_Linter_Extra_UnreachableTactic_getTactics___lam__0___boxed), 6, 2);
lean_closure_set(v___f_367_, 0, v_ignoreTacticKinds_329_);
lean_closure_set(v___f_367_, 1, v_isTacKind_330_);
v___x_368_ = lean_box(0);
v___x_369_ = lean_nat_dec_le(v___x_365_, v___x_365_);
if (v___x_369_ == 0)
{
if (v___x_366_ == 0)
{
lean_dec_ref(v___f_367_);
v___y_338_ = v_a_332_;
goto v___jp_337_;
}
else
{
size_t v___x_370_; size_t v___x_371_; lean_object* v___x_1198__overap_372_; lean_object* v___x_373_; 
v___x_370_ = ((size_t)0ULL);
v___x_371_ = lean_usize_of_nat(v___x_365_);
lean_inc_ref(v_args_336_);
v___x_1198__overap_372_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_334_, v___f_367_, v_args_336_, v___x_370_, v___x_371_, v___x_368_);
lean_inc(v_a_332_);
v___x_373_ = lean_apply_2(v___x_1198__overap_372_, v_a_332_, lean_box(0));
v___y_362_ = v___x_373_;
goto v___jp_361_;
}
}
else
{
size_t v___x_374_; size_t v___x_375_; lean_object* v___x_1202__overap_376_; lean_object* v___x_377_; 
v___x_374_ = ((size_t)0ULL);
v___x_375_ = lean_usize_of_nat(v___x_365_);
lean_inc_ref(v_args_336_);
v___x_1202__overap_376_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_334_, v___f_367_, v_args_336_, v___x_374_, v___x_375_, v___x_368_);
lean_inc(v_a_332_);
v___x_377_ = lean_apply_2(v___x_1202__overap_376_, v_a_332_, lean_box(0));
v___y_362_ = v___x_377_;
goto v___jp_361_;
}
}
}
else
{
lean_dec_ref(v_ignoreTacticKinds_329_);
v___y_338_ = v_a_332_;
goto v___jp_337_;
}
v___jp_337_:
{
lean_object* v___x_339_; uint8_t v___x_340_; 
lean_inc(v_kind_335_);
v___x_339_ = lean_apply_1(v_isTacKind_330_, v_kind_335_);
v___x_340_ = lean_unbox(v___x_339_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; lean_object* v___x_342_; 
lean_dec_ref_known(v_stx_331_, 3);
v___x_341_ = lean_box(0);
v___x_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
return v___x_342_;
}
else
{
uint8_t v___x_343_; lean_object* v___x_344_; 
v___x_343_ = lean_unbox(v___x_339_);
v___x_344_ = l_Lean_Syntax_getRange_x3f(v_stx_331_, v___x_343_);
if (lean_obj_tag(v___x_344_) == 1)
{
lean_object* v_val_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_358_; 
v_val_345_ = lean_ctor_get(v___x_344_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_358_ == 0)
{
v___x_347_ = v___x_344_;
v_isShared_348_ = v_isSharedCheck_358_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_val_345_);
lean_dec(v___x_344_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_358_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_356_; 
v___x_349_ = lean_st_ref_take(v___y_338_);
v___x_350_ = ((lean_object*)(l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__2));
v___x_351_ = ((lean_object*)(l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__3));
v___x_352_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_350_, v___x_351_, v___x_349_, v_val_345_, v_stx_331_);
v___x_353_ = lean_st_ref_set(v___y_338_, v___x_352_);
v___x_354_ = lean_box(0);
if (v_isShared_348_ == 0)
{
lean_ctor_set_tag(v___x_347_, 0);
lean_ctor_set(v___x_347_, 0, v___x_354_);
v___x_356_ = v___x_347_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v___x_354_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
else
{
lean_object* v___x_359_; lean_object* v___x_360_; 
lean_dec(v___x_344_);
lean_dec_ref_known(v_stx_331_, 3);
v___x_359_ = lean_box(0);
v___x_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
return v___x_360_;
}
}
}
v___jp_361_:
{
if (lean_obj_tag(v___y_362_) == 0)
{
lean_dec_ref_known(v___y_362_, 1);
v___y_338_ = v_a_332_;
goto v___jp_337_;
}
else
{
lean_dec_ref_known(v_stx_331_, 3);
lean_dec_ref(v_isTacKind_330_);
return v___y_362_;
}
}
}
else
{
lean_object* v___x_378_; lean_object* v___x_379_; 
lean_dec(v_stx_331_);
lean_dec_ref(v_isTacKind_330_);
lean_dec_ref(v_ignoreTacticKinds_329_);
v___x_378_ = lean_box(0);
v___x_379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
return v___x_379_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_getTactics___lam__0(lean_object* v_ignoreTacticKinds_380_, lean_object* v_isTacKind_381_, lean_object* v_x_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Lean_Linter_Extra_UnreachableTactic_getTactics(v_ignoreTacticKinds_380_, v_isTacKind_381_, v___y_383_, v___y_384_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_getTactics___boxed(lean_object* v_ignoreTacticKinds_387_, lean_object* v_isTacKind_388_, lean_object* v_stx_389_, lean_object* v_a_390_, lean_object* v_a_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Lean_Linter_Extra_UnreachableTactic_getTactics(v_ignoreTacticKinds_387_, v_isTacKind_388_, v_stx_389_, v_a_390_);
lean_dec(v_a_390_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__6___redArg(lean_object* v_a_393_, lean_object* v_x_394_){
_start:
{
if (lean_obj_tag(v_x_394_) == 0)
{
return v_x_394_;
}
else
{
lean_object* v_key_395_; lean_object* v_value_396_; lean_object* v_tail_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_406_; 
v_key_395_ = lean_ctor_get(v_x_394_, 0);
v_value_396_ = lean_ctor_get(v_x_394_, 1);
v_tail_397_ = lean_ctor_get(v_x_394_, 2);
v_isSharedCheck_406_ = !lean_is_exclusive(v_x_394_);
if (v_isSharedCheck_406_ == 0)
{
v___x_399_ = v_x_394_;
v_isShared_400_ = v_isSharedCheck_406_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_tail_397_);
lean_inc(v_value_396_);
lean_inc(v_key_395_);
lean_dec(v_x_394_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_406_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
uint8_t v___x_401_; 
v___x_401_ = l_Lean_Syntax_instBEqRange_beq(v_key_395_, v_a_393_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; lean_object* v___x_404_; 
v___x_402_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__6___redArg(v_a_393_, v_tail_397_);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 2, v___x_402_);
v___x_404_ = v___x_399_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_key_395_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v_value_396_);
lean_ctor_set(v_reuseFailAlloc_405_, 2, v___x_402_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
else
{
lean_del_object(v___x_399_);
lean_dec(v_value_396_);
lean_dec(v_key_395_);
return v_tail_397_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__6___redArg___boxed(lean_object* v_a_407_, lean_object* v_x_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__6___redArg(v_a_407_, v_x_408_);
lean_dec_ref(v_a_407_);
return v_res_409_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5___redArg(lean_object* v_a_410_, lean_object* v_x_411_){
_start:
{
if (lean_obj_tag(v_x_411_) == 0)
{
uint8_t v___x_412_; 
v___x_412_ = 0;
return v___x_412_;
}
else
{
lean_object* v_key_413_; lean_object* v_tail_414_; uint8_t v___x_415_; 
v_key_413_ = lean_ctor_get(v_x_411_, 0);
v_tail_414_ = lean_ctor_get(v_x_411_, 2);
v___x_415_ = l_Lean_Syntax_instBEqRange_beq(v_key_413_, v_a_410_);
if (v___x_415_ == 0)
{
v_x_411_ = v_tail_414_;
goto _start;
}
else
{
return v___x_415_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5___redArg___boxed(lean_object* v_a_417_, lean_object* v_x_418_){
_start:
{
uint8_t v_res_419_; lean_object* v_r_420_; 
v_res_419_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5___redArg(v_a_417_, v_x_418_);
lean_dec(v_x_418_);
lean_dec_ref(v_a_417_);
v_r_420_ = lean_box(v_res_419_);
return v_r_420_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2___redArg(lean_object* v_m_421_, lean_object* v_a_422_){
_start:
{
lean_object* v_size_423_; lean_object* v_buckets_424_; lean_object* v___x_425_; uint64_t v___x_426_; uint64_t v___x_427_; uint64_t v___x_428_; uint64_t v_fold_429_; uint64_t v___x_430_; uint64_t v___x_431_; uint64_t v___x_432_; size_t v___x_433_; size_t v___x_434_; size_t v___x_435_; size_t v___x_436_; size_t v___x_437_; lean_object* v_bkt_438_; uint8_t v___x_439_; 
v_size_423_ = lean_ctor_get(v_m_421_, 0);
v_buckets_424_ = lean_ctor_get(v_m_421_, 1);
v___x_425_ = lean_array_get_size(v_buckets_424_);
v___x_426_ = l_Lean_Syntax_instHashableRange_hash(v_a_422_);
v___x_427_ = 32ULL;
v___x_428_ = lean_uint64_shift_right(v___x_426_, v___x_427_);
v_fold_429_ = lean_uint64_xor(v___x_426_, v___x_428_);
v___x_430_ = 16ULL;
v___x_431_ = lean_uint64_shift_right(v_fold_429_, v___x_430_);
v___x_432_ = lean_uint64_xor(v_fold_429_, v___x_431_);
v___x_433_ = lean_uint64_to_usize(v___x_432_);
v___x_434_ = lean_usize_of_nat(v___x_425_);
v___x_435_ = ((size_t)1ULL);
v___x_436_ = lean_usize_sub(v___x_434_, v___x_435_);
v___x_437_ = lean_usize_land(v___x_433_, v___x_436_);
v_bkt_438_ = lean_array_uget_borrowed(v_buckets_424_, v___x_437_);
v___x_439_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5___redArg(v_a_422_, v_bkt_438_);
if (v___x_439_ == 0)
{
return v_m_421_;
}
else
{
lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_452_; 
lean_inc(v_bkt_438_);
lean_inc_ref(v_buckets_424_);
lean_inc(v_size_423_);
v_isSharedCheck_452_ = !lean_is_exclusive(v_m_421_);
if (v_isSharedCheck_452_ == 0)
{
lean_object* v_unused_453_; lean_object* v_unused_454_; 
v_unused_453_ = lean_ctor_get(v_m_421_, 1);
lean_dec(v_unused_453_);
v_unused_454_ = lean_ctor_get(v_m_421_, 0);
lean_dec(v_unused_454_);
v___x_441_ = v_m_421_;
v_isShared_442_ = v_isSharedCheck_452_;
goto v_resetjp_440_;
}
else
{
lean_dec(v_m_421_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_452_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_443_; lean_object* v_buckets_x27_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_450_; 
v___x_443_ = lean_box(0);
v_buckets_x27_444_ = lean_array_uset(v_buckets_424_, v___x_437_, v___x_443_);
v___x_445_ = lean_unsigned_to_nat(1u);
v___x_446_ = lean_nat_sub(v_size_423_, v___x_445_);
lean_dec(v_size_423_);
v___x_447_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__6___redArg(v_a_422_, v_bkt_438_);
v___x_448_ = lean_array_uset(v_buckets_x27_444_, v___x_437_, v___x_447_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 1, v___x_448_);
lean_ctor_set(v___x_441_, 0, v___x_446_);
v___x_450_ = v___x_441_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v___x_446_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v___x_448_);
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
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2___redArg___boxed(lean_object* v_m_455_, lean_object* v_a_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2___redArg(v_m_455_, v_a_456_);
lean_dec_ref(v_a_456_);
return v_res_457_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics(lean_object* v_x_459_, lean_object* v_a_460_){
_start:
{
switch(lean_obj_tag(v_x_459_))
{
case 0:
{
lean_object* v_t_462_; 
v_t_462_ = lean_ctor_get(v_x_459_, 1);
lean_inc_ref(v_t_462_);
lean_dec_ref_known(v_x_459_, 2);
v_x_459_ = v_t_462_;
goto _start;
}
case 1:
{
lean_object* v_i_464_; 
v_i_464_ = lean_ctor_get(v_x_459_, 0);
if (lean_obj_tag(v_i_464_) == 0)
{
lean_object* v_i_465_; lean_object* v_toElabInfo_466_; lean_object* v_children_467_; lean_object* v_stx_468_; uint8_t v___x_469_; lean_object* v___x_470_; 
v_i_465_ = lean_ctor_get(v_i_464_, 0);
v_toElabInfo_466_ = lean_ctor_get(v_i_465_, 0);
lean_inc_ref(v_toElabInfo_466_);
v_children_467_ = lean_ctor_get(v_x_459_, 1);
lean_inc_ref(v_children_467_);
lean_dec_ref_known(v_x_459_, 2);
v_stx_468_ = lean_ctor_get(v_toElabInfo_466_, 1);
lean_inc(v_stx_468_);
lean_dec_ref(v_toElabInfo_466_);
v___x_469_ = 1;
v___x_470_ = l_Lean_Syntax_getRange_x3f(v_stx_468_, v___x_469_);
lean_dec(v_stx_468_);
if (lean_obj_tag(v___x_470_) == 1)
{
lean_object* v_val_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v_val_471_ = lean_ctor_get(v___x_470_, 0);
lean_inc(v_val_471_);
lean_dec_ref_known(v___x_470_, 1);
v___x_472_ = lean_st_ref_take(v_a_460_);
v___x_473_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2___redArg(v___x_472_, v_val_471_);
lean_dec(v_val_471_);
v___x_474_ = lean_st_ref_set(v_a_460_, v___x_473_);
v___x_475_ = l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList(v_children_467_, v_a_460_);
return v___x_475_;
}
else
{
lean_object* v___x_476_; 
lean_dec(v___x_470_);
v___x_476_ = l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList(v_children_467_, v_a_460_);
return v___x_476_;
}
}
else
{
lean_object* v_children_477_; lean_object* v___x_478_; 
v_children_477_ = lean_ctor_get(v_x_459_, 1);
lean_inc_ref(v_children_477_);
lean_dec_ref_known(v_x_459_, 2);
v___x_478_ = l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList(v_children_477_, v_a_460_);
return v___x_478_;
}
}
default: 
{
lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_486_; 
v_isSharedCheck_486_ = !lean_is_exclusive(v_x_459_);
if (v_isSharedCheck_486_ == 0)
{
lean_object* v_unused_487_; 
v_unused_487_ = lean_ctor_get(v_x_459_, 0);
lean_dec(v_unused_487_);
v___x_480_ = v_x_459_;
v_isShared_481_ = v_isSharedCheck_486_;
goto v_resetjp_479_;
}
else
{
lean_dec(v_x_459_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_486_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_482_; lean_object* v___x_484_; 
v___x_482_ = lean_box(0);
if (v_isShared_481_ == 0)
{
lean_ctor_set_tag(v___x_480_, 0);
lean_ctor_set(v___x_480_, 0, v___x_482_);
v___x_484_ = v___x_480_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v___x_482_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(lean_object* v_as_488_, size_t v_i_489_, size_t v_stop_490_, lean_object* v_b_491_, lean_object* v___y_492_){
_start:
{
uint8_t v___x_494_; 
v___x_494_ = lean_usize_dec_eq(v_i_489_, v_stop_490_);
if (v___x_494_ == 0)
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = lean_array_uget_borrowed(v_as_488_, v_i_489_);
lean_inc(v___x_495_);
v___x_496_ = l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics(v___x_495_, v___y_492_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v_a_497_; size_t v___x_498_; size_t v___x_499_; 
v_a_497_ = lean_ctor_get(v___x_496_, 0);
lean_inc(v_a_497_);
lean_dec_ref_known(v___x_496_, 1);
v___x_498_ = ((size_t)1ULL);
v___x_499_ = lean_usize_add(v_i_489_, v___x_498_);
v_i_489_ = v___x_499_;
v_b_491_ = v_a_497_;
goto _start;
}
else
{
return v___x_496_;
}
}
else
{
lean_object* v___x_501_; 
v___x_501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_501_, 0, v_b_491_);
return v___x_501_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__2(lean_object* v_x_502_, lean_object* v___y_503_){
_start:
{
if (lean_obj_tag(v_x_502_) == 0)
{
lean_object* v_cs_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_526_; 
v_cs_505_ = lean_ctor_get(v_x_502_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v_x_502_);
if (v_isSharedCheck_526_ == 0)
{
v___x_507_ = v_x_502_;
v_isShared_508_ = v_isSharedCheck_526_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_cs_505_);
lean_dec(v_x_502_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_526_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_509_ = lean_unsigned_to_nat(0u);
v___x_510_ = lean_array_get_size(v_cs_505_);
v___x_511_ = lean_box(0);
v___x_512_ = lean_nat_dec_lt(v___x_509_, v___x_510_);
if (v___x_512_ == 0)
{
lean_object* v___x_514_; 
lean_dec_ref(v_cs_505_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 0, v___x_511_);
v___x_514_ = v___x_507_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_511_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
else
{
uint8_t v___x_516_; 
v___x_516_ = lean_nat_dec_le(v___x_510_, v___x_510_);
if (v___x_516_ == 0)
{
if (v___x_512_ == 0)
{
lean_object* v___x_518_; 
lean_dec_ref(v_cs_505_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 0, v___x_511_);
v___x_518_ = v___x_507_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_511_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
else
{
size_t v___x_520_; size_t v___x_521_; lean_object* v___x_522_; 
lean_del_object(v___x_507_);
v___x_520_ = ((size_t)0ULL);
v___x_521_ = lean_usize_of_nat(v___x_510_);
v___x_522_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__3(v_cs_505_, v___x_520_, v___x_521_, v___x_511_, v___y_503_);
lean_dec_ref(v_cs_505_);
return v___x_522_;
}
}
else
{
size_t v___x_523_; size_t v___x_524_; lean_object* v___x_525_; 
lean_del_object(v___x_507_);
v___x_523_ = ((size_t)0ULL);
v___x_524_ = lean_usize_of_nat(v___x_510_);
v___x_525_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__3(v_cs_505_, v___x_523_, v___x_524_, v___x_511_, v___y_503_);
lean_dec_ref(v_cs_505_);
return v___x_525_;
}
}
}
}
else
{
lean_object* v_vs_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_548_; 
v_vs_527_ = lean_ctor_get(v_x_502_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v_x_502_);
if (v_isSharedCheck_548_ == 0)
{
v___x_529_ = v_x_502_;
v_isShared_530_ = v_isSharedCheck_548_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_vs_527_);
lean_dec(v_x_502_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_548_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; uint8_t v___x_534_; 
v___x_531_ = lean_unsigned_to_nat(0u);
v___x_532_ = lean_array_get_size(v_vs_527_);
v___x_533_ = lean_box(0);
v___x_534_ = lean_nat_dec_lt(v___x_531_, v___x_532_);
if (v___x_534_ == 0)
{
lean_object* v___x_536_; 
lean_dec_ref(v_vs_527_);
if (v_isShared_530_ == 0)
{
lean_ctor_set_tag(v___x_529_, 0);
lean_ctor_set(v___x_529_, 0, v___x_533_);
v___x_536_ = v___x_529_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_533_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
else
{
uint8_t v___x_538_; 
v___x_538_ = lean_nat_dec_le(v___x_532_, v___x_532_);
if (v___x_538_ == 0)
{
if (v___x_534_ == 0)
{
lean_object* v___x_540_; 
lean_dec_ref(v_vs_527_);
if (v_isShared_530_ == 0)
{
lean_ctor_set_tag(v___x_529_, 0);
lean_ctor_set(v___x_529_, 0, v___x_533_);
v___x_540_ = v___x_529_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v___x_533_);
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
lean_del_object(v___x_529_);
v___x_542_ = ((size_t)0ULL);
v___x_543_ = lean_usize_of_nat(v___x_532_);
v___x_544_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(v_vs_527_, v___x_542_, v___x_543_, v___x_533_, v___y_503_);
lean_dec_ref(v_vs_527_);
return v___x_544_;
}
}
else
{
size_t v___x_545_; size_t v___x_546_; lean_object* v___x_547_; 
lean_del_object(v___x_529_);
v___x_545_ = ((size_t)0ULL);
v___x_546_ = lean_usize_of_nat(v___x_532_);
v___x_547_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(v_vs_527_, v___x_545_, v___x_546_, v___x_533_, v___y_503_);
lean_dec_ref(v_vs_527_);
return v___x_547_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__3(lean_object* v_as_549_, size_t v_i_550_, size_t v_stop_551_, lean_object* v_b_552_, lean_object* v___y_553_){
_start:
{
uint8_t v___x_555_; 
v___x_555_ = lean_usize_dec_eq(v_i_550_, v_stop_551_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = lean_array_uget_borrowed(v_as_549_, v_i_550_);
lean_inc(v___x_556_);
v___x_557_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__2(v___x_556_, v___y_553_);
if (lean_obj_tag(v___x_557_) == 0)
{
lean_object* v_a_558_; size_t v___x_559_; size_t v___x_560_; 
v_a_558_ = lean_ctor_get(v___x_557_, 0);
lean_inc(v_a_558_);
lean_dec_ref_known(v___x_557_, 1);
v___x_559_ = ((size_t)1ULL);
v___x_560_ = lean_usize_add(v_i_550_, v___x_559_);
v_i_550_ = v___x_560_;
v_b_552_ = v_a_558_;
goto _start;
}
else
{
return v___x_557_;
}
}
else
{
lean_object* v___x_562_; 
v___x_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_562_, 0, v_b_552_);
return v___x_562_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0(lean_object* v_x_563_, size_t v_x_564_, size_t v_x_565_, lean_object* v___y_566_){
_start:
{
if (lean_obj_tag(v_x_563_) == 0)
{
lean_object* v_cs_568_; lean_object* v___x_569_; size_t v___x_570_; lean_object* v_j_571_; lean_object* v___x_572_; size_t v___x_573_; size_t v___x_574_; size_t v___x_575_; size_t v___x_576_; size_t v___x_577_; size_t v___x_578_; lean_object* v___x_579_; 
v_cs_568_ = lean_ctor_get(v_x_563_, 0);
lean_inc_ref(v_cs_568_);
lean_dec_ref_known(v_x_563_, 1);
v___x_569_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0___closed__0);
v___x_570_ = lean_usize_shift_right(v_x_564_, v_x_565_);
v_j_571_ = lean_usize_to_nat(v___x_570_);
v___x_572_ = lean_array_get_borrowed(v___x_569_, v_cs_568_, v_j_571_);
v___x_573_ = ((size_t)1ULL);
v___x_574_ = lean_usize_shift_left(v___x_573_, v_x_565_);
v___x_575_ = lean_usize_sub(v___x_574_, v___x_573_);
v___x_576_ = lean_usize_land(v_x_564_, v___x_575_);
v___x_577_ = ((size_t)5ULL);
v___x_578_ = lean_usize_sub(v_x_565_, v___x_577_);
lean_inc(v___x_572_);
v___x_579_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0(v___x_572_, v___x_576_, v___x_578_, v___y_566_);
if (lean_obj_tag(v___x_579_) == 0)
{
lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_601_; 
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_601_ == 0)
{
lean_object* v_unused_602_; 
v_unused_602_ = lean_ctor_get(v___x_579_, 0);
lean_dec(v_unused_602_);
v___x_581_ = v___x_579_;
v_isShared_582_ = v_isSharedCheck_601_;
goto v_resetjp_580_;
}
else
{
lean_dec(v___x_579_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_601_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; uint8_t v___x_587_; 
v___x_583_ = lean_unsigned_to_nat(1u);
v___x_584_ = lean_nat_add(v_j_571_, v___x_583_);
lean_dec(v_j_571_);
v___x_585_ = lean_array_get_size(v_cs_568_);
v___x_586_ = lean_box(0);
v___x_587_ = lean_nat_dec_lt(v___x_584_, v___x_585_);
if (v___x_587_ == 0)
{
lean_object* v___x_589_; 
lean_dec(v___x_584_);
lean_dec_ref(v_cs_568_);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 0, v___x_586_);
v___x_589_ = v___x_581_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_586_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
else
{
uint8_t v___x_591_; 
v___x_591_ = lean_nat_dec_le(v___x_585_, v___x_585_);
if (v___x_591_ == 0)
{
if (v___x_587_ == 0)
{
lean_object* v___x_593_; 
lean_dec(v___x_584_);
lean_dec_ref(v_cs_568_);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 0, v___x_586_);
v___x_593_ = v___x_581_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_586_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
else
{
size_t v___x_595_; size_t v___x_596_; lean_object* v___x_597_; 
lean_del_object(v___x_581_);
v___x_595_ = lean_usize_of_nat(v___x_584_);
lean_dec(v___x_584_);
v___x_596_ = lean_usize_of_nat(v___x_585_);
v___x_597_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__3(v_cs_568_, v___x_595_, v___x_596_, v___x_586_, v___y_566_);
lean_dec_ref(v_cs_568_);
return v___x_597_;
}
}
else
{
size_t v___x_598_; size_t v___x_599_; lean_object* v___x_600_; 
lean_del_object(v___x_581_);
v___x_598_ = lean_usize_of_nat(v___x_584_);
lean_dec(v___x_584_);
v___x_599_ = lean_usize_of_nat(v___x_585_);
v___x_600_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__3(v_cs_568_, v___x_598_, v___x_599_, v___x_586_, v___y_566_);
lean_dec_ref(v_cs_568_);
return v___x_600_;
}
}
}
}
else
{
lean_dec(v_j_571_);
lean_dec_ref(v_cs_568_);
return v___x_579_;
}
}
else
{
lean_object* v_vs_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_624_; 
v_vs_603_ = lean_ctor_get(v_x_563_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v_x_563_);
if (v_isSharedCheck_624_ == 0)
{
v___x_605_ = v_x_563_;
v_isShared_606_ = v_isSharedCheck_624_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_vs_603_);
lean_dec(v_x_563_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_624_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; uint8_t v___x_610_; 
v___x_607_ = lean_usize_to_nat(v_x_564_);
v___x_608_ = lean_array_get_size(v_vs_603_);
v___x_609_ = lean_box(0);
v___x_610_ = lean_nat_dec_lt(v___x_607_, v___x_608_);
if (v___x_610_ == 0)
{
lean_object* v___x_612_; 
lean_dec(v___x_607_);
lean_dec_ref(v_vs_603_);
if (v_isShared_606_ == 0)
{
lean_ctor_set_tag(v___x_605_, 0);
lean_ctor_set(v___x_605_, 0, v___x_609_);
v___x_612_ = v___x_605_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_609_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
else
{
uint8_t v___x_614_; 
v___x_614_ = lean_nat_dec_le(v___x_608_, v___x_608_);
if (v___x_614_ == 0)
{
if (v___x_610_ == 0)
{
lean_object* v___x_616_; 
lean_dec(v___x_607_);
lean_dec_ref(v_vs_603_);
if (v_isShared_606_ == 0)
{
lean_ctor_set_tag(v___x_605_, 0);
lean_ctor_set(v___x_605_, 0, v___x_609_);
v___x_616_ = v___x_605_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_609_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
else
{
size_t v___x_618_; size_t v___x_619_; lean_object* v___x_620_; 
lean_del_object(v___x_605_);
v___x_618_ = lean_usize_of_nat(v___x_607_);
lean_dec(v___x_607_);
v___x_619_ = lean_usize_of_nat(v___x_608_);
v___x_620_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(v_vs_603_, v___x_618_, v___x_619_, v___x_609_, v___y_566_);
lean_dec_ref(v_vs_603_);
return v___x_620_;
}
}
else
{
size_t v___x_621_; size_t v___x_622_; lean_object* v___x_623_; 
lean_del_object(v___x_605_);
v___x_621_ = lean_usize_of_nat(v___x_607_);
lean_dec(v___x_607_);
v___x_622_ = lean_usize_of_nat(v___x_608_);
v___x_623_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(v_vs_603_, v___x_621_, v___x_622_, v___x_609_, v___y_566_);
lean_dec_ref(v_vs_603_);
return v___x_623_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__2(lean_object* v_t_625_, lean_object* v___y_626_){
_start:
{
lean_object* v_root_628_; lean_object* v_tail_629_; lean_object* v___x_630_; 
v_root_628_ = lean_ctor_get(v_t_625_, 0);
lean_inc_ref(v_root_628_);
v_tail_629_ = lean_ctor_get(v_t_625_, 1);
lean_inc_ref(v_tail_629_);
lean_dec_ref(v_t_625_);
v___x_630_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__2(v_root_628_, v___y_626_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_651_; 
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_651_ == 0)
{
lean_object* v_unused_652_; 
v_unused_652_ = lean_ctor_get(v___x_630_, 0);
lean_dec(v_unused_652_);
v___x_632_ = v___x_630_;
v_isShared_633_ = v_isSharedCheck_651_;
goto v_resetjp_631_;
}
else
{
lean_dec(v___x_630_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_651_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; uint8_t v___x_637_; 
v___x_634_ = lean_unsigned_to_nat(0u);
v___x_635_ = lean_array_get_size(v_tail_629_);
v___x_636_ = lean_box(0);
v___x_637_ = lean_nat_dec_lt(v___x_634_, v___x_635_);
if (v___x_637_ == 0)
{
lean_object* v___x_639_; 
lean_dec_ref(v_tail_629_);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 0, v___x_636_);
v___x_639_ = v___x_632_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_636_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
else
{
uint8_t v___x_641_; 
v___x_641_ = lean_nat_dec_le(v___x_635_, v___x_635_);
if (v___x_641_ == 0)
{
if (v___x_637_ == 0)
{
lean_object* v___x_643_; 
lean_dec_ref(v_tail_629_);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 0, v___x_636_);
v___x_643_ = v___x_632_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_636_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
else
{
size_t v___x_645_; size_t v___x_646_; lean_object* v___x_647_; 
lean_del_object(v___x_632_);
v___x_645_ = ((size_t)0ULL);
v___x_646_ = lean_usize_of_nat(v___x_635_);
v___x_647_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(v_tail_629_, v___x_645_, v___x_646_, v___x_636_, v___y_626_);
lean_dec_ref(v_tail_629_);
return v___x_647_;
}
}
else
{
size_t v___x_648_; size_t v___x_649_; lean_object* v___x_650_; 
lean_del_object(v___x_632_);
v___x_648_ = ((size_t)0ULL);
v___x_649_ = lean_usize_of_nat(v___x_635_);
v___x_650_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(v_tail_629_, v___x_648_, v___x_649_, v___x_636_, v___y_626_);
lean_dec_ref(v_tail_629_);
return v___x_650_;
}
}
}
}
else
{
lean_dec_ref(v_tail_629_);
return v___x_630_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0(lean_object* v_t_653_, lean_object* v_start_654_, lean_object* v___y_655_){
_start:
{
lean_object* v___x_657_; uint8_t v___x_658_; 
v___x_657_ = lean_unsigned_to_nat(0u);
v___x_658_ = lean_nat_dec_eq(v_start_654_, v___x_657_);
if (v___x_658_ == 0)
{
lean_object* v_root_659_; lean_object* v_tail_660_; size_t v_shift_661_; lean_object* v_tailOff_662_; uint8_t v___x_663_; 
v_root_659_ = lean_ctor_get(v_t_653_, 0);
lean_inc_ref(v_root_659_);
v_tail_660_ = lean_ctor_get(v_t_653_, 1);
lean_inc_ref(v_tail_660_);
v_shift_661_ = lean_ctor_get_usize(v_t_653_, 4);
v_tailOff_662_ = lean_ctor_get(v_t_653_, 3);
lean_inc(v_tailOff_662_);
lean_dec_ref(v_t_653_);
v___x_663_ = lean_nat_dec_le(v_tailOff_662_, v_start_654_);
if (v___x_663_ == 0)
{
size_t v___x_664_; lean_object* v___x_665_; 
lean_dec(v_tailOff_662_);
v___x_664_ = lean_usize_of_nat(v_start_654_);
v___x_665_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0(v_root_659_, v___x_664_, v_shift_661_, v___y_655_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_685_; 
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_685_ == 0)
{
lean_object* v_unused_686_; 
v_unused_686_ = lean_ctor_get(v___x_665_, 0);
lean_dec(v_unused_686_);
v___x_667_ = v___x_665_;
v_isShared_668_ = v_isSharedCheck_685_;
goto v_resetjp_666_;
}
else
{
lean_dec(v___x_665_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_685_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_669_; lean_object* v___x_670_; uint8_t v___x_671_; 
v___x_669_ = lean_array_get_size(v_tail_660_);
v___x_670_ = lean_box(0);
v___x_671_ = lean_nat_dec_lt(v___x_657_, v___x_669_);
if (v___x_671_ == 0)
{
lean_object* v___x_673_; 
lean_dec_ref(v_tail_660_);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_670_);
v___x_673_ = v___x_667_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_670_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
else
{
uint8_t v___x_675_; 
v___x_675_ = lean_nat_dec_le(v___x_669_, v___x_669_);
if (v___x_675_ == 0)
{
if (v___x_671_ == 0)
{
lean_object* v___x_677_; 
lean_dec_ref(v_tail_660_);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_670_);
v___x_677_ = v___x_667_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_670_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
else
{
size_t v___x_679_; size_t v___x_680_; lean_object* v___x_681_; 
lean_del_object(v___x_667_);
v___x_679_ = ((size_t)0ULL);
v___x_680_ = lean_usize_of_nat(v___x_669_);
v___x_681_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(v_tail_660_, v___x_679_, v___x_680_, v___x_670_, v___y_655_);
lean_dec_ref(v_tail_660_);
return v___x_681_;
}
}
else
{
size_t v___x_682_; size_t v___x_683_; lean_object* v___x_684_; 
lean_del_object(v___x_667_);
v___x_682_ = ((size_t)0ULL);
v___x_683_ = lean_usize_of_nat(v___x_669_);
v___x_684_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(v_tail_660_, v___x_682_, v___x_683_, v___x_670_, v___y_655_);
lean_dec_ref(v_tail_660_);
return v___x_684_;
}
}
}
}
else
{
lean_dec_ref(v_tail_660_);
return v___x_665_;
}
}
else
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; uint8_t v___x_690_; 
lean_dec_ref(v_root_659_);
v___x_687_ = lean_nat_sub(v_start_654_, v_tailOff_662_);
lean_dec(v_tailOff_662_);
v___x_688_ = lean_array_get_size(v_tail_660_);
v___x_689_ = lean_box(0);
v___x_690_ = lean_nat_dec_lt(v___x_687_, v___x_688_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; 
lean_dec(v___x_687_);
lean_dec_ref(v_tail_660_);
v___x_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_691_, 0, v___x_689_);
return v___x_691_;
}
else
{
uint8_t v___x_692_; 
v___x_692_ = lean_nat_dec_le(v___x_688_, v___x_688_);
if (v___x_692_ == 0)
{
if (v___x_690_ == 0)
{
lean_object* v___x_693_; 
lean_dec(v___x_687_);
lean_dec_ref(v_tail_660_);
v___x_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_693_, 0, v___x_689_);
return v___x_693_;
}
else
{
size_t v___x_694_; size_t v___x_695_; lean_object* v___x_696_; 
v___x_694_ = lean_usize_of_nat(v___x_687_);
lean_dec(v___x_687_);
v___x_695_ = lean_usize_of_nat(v___x_688_);
v___x_696_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(v_tail_660_, v___x_694_, v___x_695_, v___x_689_, v___y_655_);
lean_dec_ref(v_tail_660_);
return v___x_696_;
}
}
else
{
size_t v___x_697_; size_t v___x_698_; lean_object* v___x_699_; 
v___x_697_ = lean_usize_of_nat(v___x_687_);
lean_dec(v___x_687_);
v___x_698_ = lean_usize_of_nat(v___x_688_);
v___x_699_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(v_tail_660_, v___x_697_, v___x_698_, v___x_689_, v___y_655_);
lean_dec_ref(v_tail_660_);
return v___x_699_;
}
}
}
}
else
{
lean_object* v___x_700_; 
v___x_700_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__2(v_t_653_, v___y_655_);
return v___x_700_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList(lean_object* v_trees_701_, lean_object* v_a_702_){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = lean_unsigned_to_nat(0u);
v___x_705_ = l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0(v_trees_701_, v___x_704_, v_a_702_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList___boxed(lean_object* v_trees_706_, lean_object* v_a_707_, lean_object* v_a_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList(v_trees_706_, v_a_707_);
lean_dec(v_a_707_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1___boxed(lean_object* v_as_710_, lean_object* v_i_711_, lean_object* v_stop_712_, lean_object* v_b_713_, lean_object* v___y_714_, lean_object* v___y_715_){
_start:
{
size_t v_i_boxed_716_; size_t v_stop_boxed_717_; lean_object* v_res_718_; 
v_i_boxed_716_ = lean_unbox_usize(v_i_711_);
lean_dec(v_i_711_);
v_stop_boxed_717_ = lean_unbox_usize(v_stop_712_);
lean_dec(v_stop_712_);
v_res_718_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(v_as_710_, v_i_boxed_716_, v_stop_boxed_717_, v_b_713_, v___y_714_);
lean_dec(v___y_714_);
lean_dec_ref(v_as_710_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__3___boxed(lean_object* v_as_719_, lean_object* v_i_720_, lean_object* v_stop_721_, lean_object* v_b_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
size_t v_i_boxed_725_; size_t v_stop_boxed_726_; lean_object* v_res_727_; 
v_i_boxed_725_ = lean_unbox_usize(v_i_720_);
lean_dec(v_i_720_);
v_stop_boxed_726_ = lean_unbox_usize(v_stop_721_);
lean_dec(v_stop_721_);
v_res_727_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__3(v_as_719_, v_i_boxed_725_, v_stop_boxed_726_, v_b_722_, v___y_723_);
lean_dec(v___y_723_);
lean_dec_ref(v_as_719_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__2___boxed(lean_object* v_t_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__2(v_t_728_, v___y_729_);
lean_dec(v___y_729_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics___boxed(lean_object* v_x_732_, lean_object* v_a_733_, lean_object* v_a_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics(v_x_732_, v_a_733_);
lean_dec(v_a_733_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__2___boxed(lean_object* v_x_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__2(v_x_736_, v___y_737_);
lean_dec(v___y_737_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0___boxed(lean_object* v_t_740_, lean_object* v_start_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0(v_t_740_, v_start_741_, v___y_742_);
lean_dec(v___y_742_);
lean_dec(v_start_741_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0___boxed(lean_object* v_x_745_, lean_object* v_x_746_, lean_object* v_x_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
size_t v_x_2929__boxed_750_; size_t v_x_2930__boxed_751_; lean_object* v_res_752_; 
v_x_2929__boxed_750_ = lean_unbox_usize(v_x_746_);
lean_dec(v_x_746_);
v_x_2930__boxed_751_ = lean_unbox_usize(v_x_747_);
lean_dec(v_x_747_);
v_res_752_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0(v_x_745_, v_x_2929__boxed_750_, v_x_2930__boxed_751_, v___y_748_);
lean_dec(v___y_748_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2(lean_object* v_00_u03b2_753_, lean_object* v_m_754_, lean_object* v_a_755_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2___redArg(v_m_754_, v_a_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2___boxed(lean_object* v_00_u03b2_757_, lean_object* v_m_758_, lean_object* v_a_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2(v_00_u03b2_757_, v_m_758_, v_a_759_);
lean_dec_ref(v_a_759_);
return v_res_760_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5(lean_object* v_00_u03b2_761_, lean_object* v_a_762_, lean_object* v_x_763_){
_start:
{
uint8_t v___x_764_; 
v___x_764_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5___redArg(v_a_762_, v_x_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5___boxed(lean_object* v_00_u03b2_765_, lean_object* v_a_766_, lean_object* v_x_767_){
_start:
{
uint8_t v_res_768_; lean_object* v_r_769_; 
v_res_768_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5(v_00_u03b2_765_, v_a_766_, v_x_767_);
lean_dec(v_x_767_);
lean_dec_ref(v_a_766_);
v_r_769_ = lean_box(v_res_768_);
return v_r_769_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__6(lean_object* v_00_u03b2_770_, lean_object* v_a_771_, lean_object* v_x_772_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__6___redArg(v_a_771_, v_x_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__6___boxed(lean_object* v_00_u03b2_774_, lean_object* v_a_775_, lean_object* v_x_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__6(v_00_u03b2_774_, v_a_775_, v_x_776_);
lean_dec_ref(v_a_775_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__0(lean_object* v_a_778_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = lean_nat_to_int(v_a_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4___redArg(lean_object* v___y_780_){
_start:
{
lean_object* v___x_782_; lean_object* v_infoState_783_; lean_object* v_trees_784_; lean_object* v___x_785_; 
v___x_782_ = lean_st_ref_get(v___y_780_);
v_infoState_783_ = lean_ctor_get(v___x_782_, 8);
lean_inc_ref(v_infoState_783_);
lean_dec(v___x_782_);
v_trees_784_ = lean_ctor_get(v_infoState_783_, 2);
lean_inc_ref(v_trees_784_);
lean_dec_ref(v_infoState_783_);
v___x_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_785_, 0, v_trees_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4___redArg___boxed(lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4___redArg(v___y_786_);
lean_dec(v___y_786_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4(lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4___redArg(v___y_790_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4___boxed(lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4(v___y_793_, v___y_794_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
return v_res_796_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__20(lean_object* v_opts_797_, lean_object* v_opt_798_){
_start:
{
lean_object* v_name_799_; lean_object* v_defValue_800_; lean_object* v_map_801_; lean_object* v___x_802_; 
v_name_799_ = lean_ctor_get(v_opt_798_, 0);
v_defValue_800_ = lean_ctor_get(v_opt_798_, 1);
v_map_801_ = lean_ctor_get(v_opts_797_, 0);
v___x_802_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_801_, v_name_799_);
if (lean_obj_tag(v___x_802_) == 0)
{
uint8_t v___x_803_; 
v___x_803_ = lean_unbox(v_defValue_800_);
return v___x_803_;
}
else
{
lean_object* v_val_804_; 
v_val_804_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_val_804_);
lean_dec_ref_known(v___x_802_, 1);
if (lean_obj_tag(v_val_804_) == 1)
{
uint8_t v_v_805_; 
v_v_805_ = lean_ctor_get_uint8(v_val_804_, 0);
lean_dec_ref_known(v_val_804_, 0);
return v_v_805_;
}
else
{
uint8_t v___x_806_; 
lean_dec(v_val_804_);
v___x_806_ = lean_unbox(v_defValue_800_);
return v___x_806_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__20___boxed(lean_object* v_opts_807_, lean_object* v_opt_808_){
_start:
{
uint8_t v_res_809_; lean_object* v_r_810_; 
v_res_809_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__20(v_opts_807_, v_opt_808_);
lean_dec_ref(v_opt_808_);
lean_dec_ref(v_opts_807_);
v_r_810_ = lean_box(v_res_809_);
return v_r_810_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__0(void){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_811_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__1(void){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_812_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__0);
v___x_813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
return v___x_813_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__2(void){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_814_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__1);
v___x_815_ = lean_unsigned_to_nat(0u);
v___x_816_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_816_, 0, v___x_815_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
lean_ctor_set(v___x_816_, 2, v___x_815_);
lean_ctor_set(v___x_816_, 3, v___x_815_);
lean_ctor_set(v___x_816_, 4, v___x_814_);
lean_ctor_set(v___x_816_, 5, v___x_814_);
lean_ctor_set(v___x_816_, 6, v___x_814_);
lean_ctor_set(v___x_816_, 7, v___x_814_);
lean_ctor_set(v___x_816_, 8, v___x_814_);
lean_ctor_set(v___x_816_, 9, v___x_814_);
return v___x_816_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__3(void){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_817_ = lean_unsigned_to_nat(32u);
v___x_818_ = lean_mk_empty_array_with_capacity(v___x_817_);
v___x_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
return v___x_819_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__4(void){
_start:
{
size_t v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_820_ = ((size_t)5ULL);
v___x_821_ = lean_unsigned_to_nat(0u);
v___x_822_ = lean_unsigned_to_nat(32u);
v___x_823_ = lean_mk_empty_array_with_capacity(v___x_822_);
v___x_824_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__3);
v___x_825_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_825_, 0, v___x_824_);
lean_ctor_set(v___x_825_, 1, v___x_823_);
lean_ctor_set(v___x_825_, 2, v___x_821_);
lean_ctor_set(v___x_825_, 3, v___x_821_);
lean_ctor_set_usize(v___x_825_, 4, v___x_820_);
return v___x_825_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__5(void){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_826_ = lean_box(1);
v___x_827_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__4);
v___x_828_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__1);
v___x_829_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
lean_ctor_set(v___x_829_, 1, v___x_827_);
lean_ctor_set(v___x_829_, 2, v___x_826_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg(lean_object* v_msgData_830_, lean_object* v___y_831_){
_start:
{
lean_object* v___x_833_; lean_object* v_env_834_; lean_object* v___x_835_; lean_object* v_scopes_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v_opts_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_833_ = lean_st_ref_get(v___y_831_);
v_env_834_ = lean_ctor_get(v___x_833_, 0);
lean_inc_ref(v_env_834_);
lean_dec(v___x_833_);
v___x_835_ = lean_st_ref_get(v___y_831_);
v_scopes_836_ = lean_ctor_get(v___x_835_, 2);
lean_inc(v_scopes_836_);
lean_dec(v___x_835_);
v___x_837_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_838_ = l_List_head_x21___redArg(v___x_837_, v_scopes_836_);
lean_dec(v_scopes_836_);
v_opts_839_ = lean_ctor_get(v___x_838_, 1);
lean_inc_ref(v_opts_839_);
lean_dec(v___x_838_);
v___x_840_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__2);
v___x_841_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__5);
v___x_842_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_842_, 0, v_env_834_);
lean_ctor_set(v___x_842_, 1, v___x_840_);
lean_ctor_set(v___x_842_, 2, v___x_841_);
lean_ctor_set(v___x_842_, 3, v_opts_839_);
v___x_843_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_843_, 0, v___x_842_);
lean_ctor_set(v___x_843_, 1, v_msgData_830_);
v___x_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_844_, 0, v___x_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___boxed(lean_object* v_msgData_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg(v_msgData_845_, v___y_846_);
lean_dec(v___y_846_);
return v_res_848_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13___lam__0(uint8_t v___y_850_, uint8_t v_suppressElabErrors_851_, lean_object* v_x_852_){
_start:
{
if (lean_obj_tag(v_x_852_) == 1)
{
lean_object* v_pre_853_; 
v_pre_853_ = lean_ctor_get(v_x_852_, 0);
if (lean_obj_tag(v_pre_853_) == 0)
{
lean_object* v_str_854_; lean_object* v___x_855_; uint8_t v___x_856_; 
v_str_854_ = lean_ctor_get(v_x_852_, 1);
v___x_855_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13___lam__0___closed__0));
v___x_856_ = lean_string_dec_eq(v_str_854_, v___x_855_);
if (v___x_856_ == 0)
{
return v___y_850_;
}
else
{
return v_suppressElabErrors_851_;
}
}
else
{
return v___y_850_;
}
}
else
{
return v___y_850_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13___lam__0___boxed(lean_object* v___y_857_, lean_object* v_suppressElabErrors_858_, lean_object* v_x_859_){
_start:
{
uint8_t v___y_12800__boxed_860_; uint8_t v_suppressElabErrors_boxed_861_; uint8_t v_res_862_; lean_object* v_r_863_; 
v___y_12800__boxed_860_ = lean_unbox(v___y_857_);
v_suppressElabErrors_boxed_861_ = lean_unbox(v_suppressElabErrors_858_);
v_res_862_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13___lam__0(v___y_12800__boxed_860_, v_suppressElabErrors_boxed_861_, v_x_859_);
lean_dec(v_x_859_);
v_r_863_ = lean_box(v_res_862_);
return v_r_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13(lean_object* v_ref_865_, lean_object* v_msgData_866_, uint8_t v_severity_867_, uint8_t v_isSilent_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
uint8_t v___y_873_; lean_object* v___y_874_; lean_object* v___y_875_; lean_object* v___y_876_; lean_object* v___y_877_; uint8_t v___y_878_; lean_object* v___y_879_; lean_object* v___y_880_; uint8_t v___y_936_; uint8_t v___y_937_; lean_object* v___y_938_; uint8_t v___y_939_; lean_object* v___y_940_; uint8_t v___y_964_; uint8_t v___y_965_; lean_object* v___y_966_; uint8_t v___y_967_; lean_object* v___y_968_; uint8_t v___y_972_; uint8_t v___y_973_; uint8_t v___y_974_; uint8_t v___x_989_; uint8_t v___y_991_; uint8_t v___y_992_; uint8_t v___y_993_; uint8_t v___y_995_; uint8_t v___x_1007_; 
v___x_989_ = 2;
v___x_1007_ = l_Lean_instBEqMessageSeverity_beq(v_severity_867_, v___x_989_);
if (v___x_1007_ == 0)
{
v___y_995_ = v___x_1007_;
goto v___jp_994_;
}
else
{
uint8_t v___x_1008_; 
lean_inc_ref(v_msgData_866_);
v___x_1008_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_866_);
v___y_995_ = v___x_1008_;
goto v___jp_994_;
}
v___jp_872_:
{
lean_object* v___x_881_; 
v___x_881_ = l_Lean_Elab_Command_getScope___redArg(v___y_880_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v_a_882_; lean_object* v___x_883_; 
v_a_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_a_882_);
lean_dec_ref_known(v___x_881_, 1);
v___x_883_ = l_Lean_Elab_Command_getScope___redArg(v___y_880_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_918_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_918_ == 0)
{
v___x_886_ = v___x_883_;
v_isShared_887_ = v_isSharedCheck_918_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_883_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_918_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_888_; lean_object* v_currNamespace_889_; lean_object* v_openDecls_890_; lean_object* v_env_891_; lean_object* v_messages_892_; lean_object* v_scopes_893_; lean_object* v_usedQuotCtxts_894_; lean_object* v_nextMacroScope_895_; lean_object* v_maxRecDepth_896_; lean_object* v_ngen_897_; lean_object* v_auxDeclNGen_898_; lean_object* v_infoState_899_; lean_object* v_traceState_900_; lean_object* v_snapshotTasks_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_917_; 
v___x_888_ = lean_st_ref_take(v___y_880_);
v_currNamespace_889_ = lean_ctor_get(v_a_882_, 2);
lean_inc(v_currNamespace_889_);
lean_dec(v_a_882_);
v_openDecls_890_ = lean_ctor_get(v_a_884_, 3);
lean_inc(v_openDecls_890_);
lean_dec(v_a_884_);
v_env_891_ = lean_ctor_get(v___x_888_, 0);
v_messages_892_ = lean_ctor_get(v___x_888_, 1);
v_scopes_893_ = lean_ctor_get(v___x_888_, 2);
v_usedQuotCtxts_894_ = lean_ctor_get(v___x_888_, 3);
v_nextMacroScope_895_ = lean_ctor_get(v___x_888_, 4);
v_maxRecDepth_896_ = lean_ctor_get(v___x_888_, 5);
v_ngen_897_ = lean_ctor_get(v___x_888_, 6);
v_auxDeclNGen_898_ = lean_ctor_get(v___x_888_, 7);
v_infoState_899_ = lean_ctor_get(v___x_888_, 8);
v_traceState_900_ = lean_ctor_get(v___x_888_, 9);
v_snapshotTasks_901_ = lean_ctor_get(v___x_888_, 10);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_917_ == 0)
{
v___x_903_ = v___x_888_;
v_isShared_904_ = v_isSharedCheck_917_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_snapshotTasks_901_);
lean_inc(v_traceState_900_);
lean_inc(v_infoState_899_);
lean_inc(v_auxDeclNGen_898_);
lean_inc(v_ngen_897_);
lean_inc(v_maxRecDepth_896_);
lean_inc(v_nextMacroScope_895_);
lean_inc(v_usedQuotCtxts_894_);
lean_inc(v_scopes_893_);
lean_inc(v_messages_892_);
lean_inc(v_env_891_);
lean_dec(v___x_888_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_917_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_910_; 
v___x_905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_905_, 0, v_currNamespace_889_);
lean_ctor_set(v___x_905_, 1, v_openDecls_890_);
v___x_906_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_905_);
lean_ctor_set(v___x_906_, 1, v___y_874_);
lean_inc_ref(v___y_876_);
lean_inc_ref(v___y_875_);
v___x_907_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_907_, 0, v___y_875_);
lean_ctor_set(v___x_907_, 1, v___y_879_);
lean_ctor_set(v___x_907_, 2, v___y_877_);
lean_ctor_set(v___x_907_, 3, v___y_876_);
lean_ctor_set(v___x_907_, 4, v___x_906_);
lean_ctor_set_uint8(v___x_907_, sizeof(void*)*5, v___y_878_);
lean_ctor_set_uint8(v___x_907_, sizeof(void*)*5 + 1, v___y_873_);
lean_ctor_set_uint8(v___x_907_, sizeof(void*)*5 + 2, v_isSilent_868_);
v___x_908_ = l_Lean_MessageLog_add(v___x_907_, v_messages_892_);
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 1, v___x_908_);
v___x_910_ = v___x_903_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_env_891_);
lean_ctor_set(v_reuseFailAlloc_916_, 1, v___x_908_);
lean_ctor_set(v_reuseFailAlloc_916_, 2, v_scopes_893_);
lean_ctor_set(v_reuseFailAlloc_916_, 3, v_usedQuotCtxts_894_);
lean_ctor_set(v_reuseFailAlloc_916_, 4, v_nextMacroScope_895_);
lean_ctor_set(v_reuseFailAlloc_916_, 5, v_maxRecDepth_896_);
lean_ctor_set(v_reuseFailAlloc_916_, 6, v_ngen_897_);
lean_ctor_set(v_reuseFailAlloc_916_, 7, v_auxDeclNGen_898_);
lean_ctor_set(v_reuseFailAlloc_916_, 8, v_infoState_899_);
lean_ctor_set(v_reuseFailAlloc_916_, 9, v_traceState_900_);
lean_ctor_set(v_reuseFailAlloc_916_, 10, v_snapshotTasks_901_);
v___x_910_ = v_reuseFailAlloc_916_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_914_; 
v___x_911_ = lean_st_ref_set(v___y_880_, v___x_910_);
v___x_912_ = lean_box(0);
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 0, v___x_912_);
v___x_914_ = v___x_886_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_912_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
}
else
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_926_; 
lean_dec(v_a_882_);
lean_dec_ref(v___y_879_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_874_);
v_a_919_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_926_ == 0)
{
v___x_921_ = v___x_883_;
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_883_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_924_; 
if (v_isShared_922_ == 0)
{
v___x_924_ = v___x_921_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_a_919_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
else
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_934_; 
lean_dec_ref(v___y_879_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_874_);
v_a_927_ = lean_ctor_get(v___x_881_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_934_ == 0)
{
v___x_929_ = v___x_881_;
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_881_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_932_; 
if (v_isShared_930_ == 0)
{
v___x_932_ = v___x_929_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_a_927_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
v___jp_935_:
{
lean_object* v_fileName_941_; lean_object* v_fileMap_942_; uint8_t v_suppressElabErrors_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_962_; 
v_fileName_941_ = lean_ctor_get(v___y_869_, 0);
v_fileMap_942_ = lean_ctor_get(v___y_869_, 1);
v_suppressElabErrors_943_ = lean_ctor_get_uint8(v___y_869_, sizeof(void*)*10);
v___x_944_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_866_);
v___x_945_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg(v___x_944_, v___y_870_);
v_a_946_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_962_ == 0)
{
v___x_948_ = v___x_945_;
v_isShared_949_ = v_isSharedCheck_962_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___x_945_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_962_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
lean_inc_ref_n(v_fileMap_942_, 2);
v___x_950_ = l_Lean_FileMap_toPosition(v_fileMap_942_, v___y_938_);
lean_dec(v___y_938_);
v___x_951_ = l_Lean_FileMap_toPosition(v_fileMap_942_, v___y_940_);
lean_dec(v___y_940_);
v___x_952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_952_, 0, v___x_951_);
v___x_953_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13___closed__0));
if (v_suppressElabErrors_943_ == 0)
{
lean_del_object(v___x_948_);
v___y_873_ = v___y_937_;
v___y_874_ = v_a_946_;
v___y_875_ = v_fileName_941_;
v___y_876_ = v___x_953_;
v___y_877_ = v___x_952_;
v___y_878_ = v___y_939_;
v___y_879_ = v___x_950_;
v___y_880_ = v___y_870_;
goto v___jp_872_;
}
else
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___f_956_; uint8_t v___x_957_; 
v___x_954_ = lean_box(v___y_936_);
v___x_955_ = lean_box(v_suppressElabErrors_943_);
v___f_956_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13___lam__0___boxed), 3, 2);
lean_closure_set(v___f_956_, 0, v___x_954_);
lean_closure_set(v___f_956_, 1, v___x_955_);
lean_inc(v_a_946_);
v___x_957_ = l_Lean_MessageData_hasTag(v___f_956_, v_a_946_);
if (v___x_957_ == 0)
{
lean_object* v___x_958_; lean_object* v___x_960_; 
lean_dec_ref_known(v___x_952_, 1);
lean_dec_ref(v___x_950_);
lean_dec(v_a_946_);
v___x_958_ = lean_box(0);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 0, v___x_958_);
v___x_960_ = v___x_948_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v___x_958_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
else
{
lean_del_object(v___x_948_);
v___y_873_ = v___y_937_;
v___y_874_ = v_a_946_;
v___y_875_ = v_fileName_941_;
v___y_876_ = v___x_953_;
v___y_877_ = v___x_952_;
v___y_878_ = v___y_939_;
v___y_879_ = v___x_950_;
v___y_880_ = v___y_870_;
goto v___jp_872_;
}
}
}
}
v___jp_963_:
{
lean_object* v___x_969_; 
v___x_969_ = l_Lean_Syntax_getTailPos_x3f(v___y_966_, v___y_967_);
lean_dec(v___y_966_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_inc(v___y_968_);
v___y_936_ = v___y_964_;
v___y_937_ = v___y_965_;
v___y_938_ = v___y_968_;
v___y_939_ = v___y_967_;
v___y_940_ = v___y_968_;
goto v___jp_935_;
}
else
{
lean_object* v_val_970_; 
v_val_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_val_970_);
lean_dec_ref_known(v___x_969_, 1);
v___y_936_ = v___y_964_;
v___y_937_ = v___y_965_;
v___y_938_ = v___y_968_;
v___y_939_ = v___y_967_;
v___y_940_ = v_val_970_;
goto v___jp_935_;
}
}
v___jp_971_:
{
lean_object* v___x_975_; 
v___x_975_ = l_Lean_Elab_Command_getRef___redArg(v___y_869_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; lean_object* v_ref_977_; lean_object* v___x_978_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_a_976_);
lean_dec_ref_known(v___x_975_, 1);
v_ref_977_ = l_Lean_replaceRef(v_ref_865_, v_a_976_);
lean_dec(v_a_976_);
v___x_978_ = l_Lean_Syntax_getPos_x3f(v_ref_977_, v___y_973_);
if (lean_obj_tag(v___x_978_) == 0)
{
lean_object* v___x_979_; 
v___x_979_ = lean_unsigned_to_nat(0u);
v___y_964_ = v___y_972_;
v___y_965_ = v___y_974_;
v___y_966_ = v_ref_977_;
v___y_967_ = v___y_973_;
v___y_968_ = v___x_979_;
goto v___jp_963_;
}
else
{
lean_object* v_val_980_; 
v_val_980_ = lean_ctor_get(v___x_978_, 0);
lean_inc(v_val_980_);
lean_dec_ref_known(v___x_978_, 1);
v___y_964_ = v___y_972_;
v___y_965_ = v___y_974_;
v___y_966_ = v_ref_977_;
v___y_967_ = v___y_973_;
v___y_968_ = v_val_980_;
goto v___jp_963_;
}
}
else
{
lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_988_; 
lean_dec_ref(v_msgData_866_);
v_a_981_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_988_ == 0)
{
v___x_983_ = v___x_975_;
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v___x_975_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_986_; 
if (v_isShared_984_ == 0)
{
v___x_986_ = v___x_983_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_a_981_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
v___jp_990_:
{
if (v___y_993_ == 0)
{
v___y_972_ = v___y_991_;
v___y_973_ = v___y_992_;
v___y_974_ = v_severity_867_;
goto v___jp_971_;
}
else
{
v___y_972_ = v___y_991_;
v___y_973_ = v___y_992_;
v___y_974_ = v___x_989_;
goto v___jp_971_;
}
}
v___jp_994_:
{
if (v___y_995_ == 0)
{
lean_object* v___x_996_; lean_object* v_scopes_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v_opts_1000_; uint8_t v___x_1001_; uint8_t v___x_1002_; 
v___x_996_ = lean_st_ref_get(v___y_870_);
v_scopes_997_ = lean_ctor_get(v___x_996_, 2);
lean_inc(v_scopes_997_);
lean_dec(v___x_996_);
v___x_998_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_999_ = l_List_head_x21___redArg(v___x_998_, v_scopes_997_);
lean_dec(v_scopes_997_);
v_opts_1000_ = lean_ctor_get(v___x_999_, 1);
lean_inc_ref(v_opts_1000_);
lean_dec(v___x_999_);
v___x_1001_ = 1;
v___x_1002_ = l_Lean_instBEqMessageSeverity_beq(v_severity_867_, v___x_1001_);
if (v___x_1002_ == 0)
{
lean_dec_ref(v_opts_1000_);
v___y_991_ = v___y_995_;
v___y_992_ = v___y_995_;
v___y_993_ = v___x_1002_;
goto v___jp_990_;
}
else
{
lean_object* v___x_1003_; uint8_t v___x_1004_; 
v___x_1003_ = l_Lean_warningAsError;
v___x_1004_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__20(v_opts_1000_, v___x_1003_);
lean_dec_ref(v_opts_1000_);
v___y_991_ = v___y_995_;
v___y_992_ = v___y_995_;
v___y_993_ = v___x_1004_;
goto v___jp_990_;
}
}
else
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
lean_dec_ref(v_msgData_866_);
v___x_1005_ = lean_box(0);
v___x_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
return v___x_1006_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13___boxed(lean_object* v_ref_1009_, lean_object* v_msgData_1010_, lean_object* v_severity_1011_, lean_object* v_isSilent_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
uint8_t v_severity_boxed_1016_; uint8_t v_isSilent_boxed_1017_; lean_object* v_res_1018_; 
v_severity_boxed_1016_ = lean_unbox(v_severity_1011_);
v_isSilent_boxed_1017_ = lean_unbox(v_isSilent_1012_);
v_res_1018_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13(v_ref_1009_, v_msgData_1010_, v_severity_boxed_1016_, v_isSilent_boxed_1017_, v___y_1013_, v___y_1014_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec(v_ref_1009_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5(lean_object* v_ref_1019_, lean_object* v_msgData_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
uint8_t v___x_1024_; uint8_t v___x_1025_; lean_object* v___x_1026_; 
v___x_1024_ = 1;
v___x_1025_ = 0;
v___x_1026_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13(v_ref_1019_, v_msgData_1020_, v___x_1024_, v___x_1025_, v___y_1021_, v___y_1022_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5___boxed(lean_object* v_ref_1027_, lean_object* v_msgData_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5(v_ref_1027_, v_msgData_1028_, v___y_1029_, v___y_1030_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v_ref_1027_);
return v_res_1032_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__0));
v___x_1035_ = l_Lean_stringToMessageData(v___x_1034_);
return v___x_1035_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__2));
v___x_1038_ = l_Lean_stringToMessageData(v___x_1037_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3(lean_object* v_linterOption_1039_, lean_object* v_stx_1040_, lean_object* v_msg_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v_name_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1063_; 
v_name_1045_ = lean_ctor_get(v_linterOption_1039_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v_linterOption_1039_);
if (v_isSharedCheck_1063_ == 0)
{
lean_object* v_unused_1064_; 
v_unused_1064_ = lean_ctor_get(v_linterOption_1039_, 1);
lean_dec(v_unused_1064_);
v___x_1047_ = v_linterOption_1039_;
v_isShared_1048_ = v_isSharedCheck_1063_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_name_1045_);
lean_dec(v_linterOption_1039_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1063_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1052_; 
v___x_1049_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__1);
lean_inc(v_name_1045_);
v___x_1050_ = l_Lean_MessageData_ofName(v_name_1045_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set_tag(v___x_1047_, 7);
lean_ctor_set(v___x_1047_, 1, v___x_1050_);
lean_ctor_set(v___x_1047_, 0, v___x_1049_);
v___x_1052_ = v___x_1047_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v___x_1049_);
lean_ctor_set(v_reuseFailAlloc_1062_, 1, v___x_1050_);
v___x_1052_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v_disable_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1053_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__3);
v___x_1054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1052_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
v_disable_1055_ = l_Lean_MessageData_note(v___x_1054_);
v___x_1056_ = l_Lean_Linter_linterMessageTag;
v___x_1057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1057_, 0, v_msg_1041_);
lean_ctor_set(v___x_1057_, 1, v_disable_1055_);
v___x_1058_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1056_);
lean_ctor_set(v___x_1058_, 1, v___x_1057_);
v___x_1059_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1059_, 0, v_name_1045_);
lean_ctor_set(v___x_1059_, 1, v___x_1058_);
lean_inc(v_stx_1040_);
v___x_1060_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_1060_, 0, v_stx_1040_);
lean_ctor_set(v___x_1060_, 1, v___x_1059_);
v___x_1061_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5(v_stx_1040_, v___x_1060_, v___y_1042_, v___y_1043_);
lean_dec(v_stx_1040_);
return v___x_1061_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___boxed(lean_object* v_linterOption_1065_, lean_object* v_stx_1066_, lean_object* v_msg_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3(v_linterOption_1065_, v_stx_1066_, v_msg_1067_, v___y_1068_, v___y_1069_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1___redArg(lean_object* v_o_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v___x_1075_; lean_object* v_env_1076_; lean_object* v___x_1077_; lean_object* v_toEnvExtension_1078_; lean_object* v_asyncMode_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v_merged_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1091_; 
v___x_1075_ = lean_st_ref_get(v___y_1073_);
v_env_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc_ref(v_env_1076_);
lean_dec(v___x_1075_);
v___x_1077_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_1078_ = lean_ctor_get(v___x_1077_, 0);
v_asyncMode_1079_ = lean_ctor_get(v_toEnvExtension_1078_, 2);
v___x_1080_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_1081_ = lean_box(0);
v___x_1082_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1080_, v___x_1077_, v_env_1076_, v_asyncMode_1079_, v___x_1081_);
v_merged_1083_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1091_ == 0)
{
lean_object* v_unused_1092_; 
v_unused_1092_ = lean_ctor_get(v___x_1082_, 1);
lean_dec(v_unused_1092_);
v___x_1085_ = v___x_1082_;
v_isShared_1086_ = v_isSharedCheck_1091_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_merged_1083_);
lean_dec(v___x_1082_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1091_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 1, v_merged_1083_);
lean_ctor_set(v___x_1085_, 0, v_o_1072_);
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_o_1072_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v_merged_1083_);
v___x_1088_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
lean_object* v___x_1089_; 
v___x_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1088_);
return v___x_1089_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1___redArg___boxed(lean_object* v_o_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1___redArg(v_o_1093_, v___y_1094_);
lean_dec(v___y_1094_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1(lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v___x_1100_; lean_object* v_scopes_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v_opts_1104_; lean_object* v___x_1105_; 
v___x_1100_ = lean_st_ref_get(v___y_1098_);
v_scopes_1101_ = lean_ctor_get(v___x_1100_, 2);
lean_inc(v_scopes_1101_);
lean_dec(v___x_1100_);
v___x_1102_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1103_ = l_List_head_x21___redArg(v___x_1102_, v_scopes_1101_);
lean_dec(v_scopes_1101_);
v_opts_1104_ = lean_ctor_get(v___x_1103_, 1);
lean_inc_ref(v_opts_1104_);
lean_dec(v___x_1103_);
v___x_1105_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1___redArg(v_opts_1104_, v___y_1098_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1___boxed(lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1(v___y_1106_, v___y_1107_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2(lean_object* v_linterOption_1110_, lean_object* v_stx_1111_, lean_object* v_msg_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v___x_1116_; lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1127_; 
v___x_1116_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1(v___y_1113_, v___y_1114_);
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1119_ = v___x_1116_;
v_isShared_1120_ = v_isSharedCheck_1127_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v___x_1116_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1127_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
uint8_t v___x_1121_; 
v___x_1121_ = l_Lean_Linter_getLinterValue(v_linterOption_1110_, v_a_1117_);
lean_dec(v_a_1117_);
if (v___x_1121_ == 0)
{
lean_object* v___x_1122_; lean_object* v___x_1124_; 
lean_dec_ref(v_msg_1112_);
lean_dec(v_stx_1111_);
lean_dec_ref(v_linterOption_1110_);
v___x_1122_ = lean_box(0);
if (v_isShared_1120_ == 0)
{
lean_ctor_set(v___x_1119_, 0, v___x_1122_);
v___x_1124_ = v___x_1119_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v___x_1122_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
else
{
lean_object* v___x_1126_; 
lean_del_object(v___x_1119_);
v___x_1126_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3(v_linterOption_1110_, v_stx_1111_, v_msg_1112_, v___y_1113_, v___y_1114_);
return v___x_1126_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2___boxed(lean_object* v_linterOption_1128_, lean_object* v_stx_1129_, lean_object* v_msg_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2(v_linterOption_1128_, v_stx_1129_, v_msg_1130_, v___y_1131_, v___y_1132_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
return v_res_1134_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___closed__2(void){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1138_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___closed__1));
v___x_1139_ = l_Lean_MessageData_ofFormat(v___x_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5(lean_object* v_as_1140_, size_t v_sz_1141_, size_t v_i_1142_, lean_object* v_b_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_){
_start:
{
lean_object* v_a_1148_; uint8_t v___x_1152_; 
v___x_1152_ = lean_usize_dec_lt(v_i_1142_, v_sz_1141_);
if (v___x_1152_ == 0)
{
lean_object* v___x_1153_; 
v___x_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1153_, 0, v_b_1143_);
return v___x_1153_;
}
else
{
lean_object* v_a_1154_; lean_object* v_fst_1155_; lean_object* v_snd_1156_; lean_object* v_start_1157_; lean_object* v_stop_1158_; lean_object* v_start_1159_; lean_object* v_stop_1160_; lean_object* v___x_1161_; uint8_t v___y_1163_; uint8_t v___x_1174_; 
v_a_1154_ = lean_array_uget_borrowed(v_as_1140_, v_i_1142_);
v_fst_1155_ = lean_ctor_get(v_a_1154_, 0);
v_snd_1156_ = lean_ctor_get(v_a_1154_, 1);
v_start_1157_ = lean_ctor_get(v_b_1143_, 0);
v_stop_1158_ = lean_ctor_get(v_b_1143_, 1);
v_start_1159_ = lean_ctor_get(v_fst_1155_, 0);
v_stop_1160_ = lean_ctor_get(v_fst_1155_, 1);
v___x_1161_ = l_Lean_Linter_Extra_linter_extra_unreachableTactic;
v___x_1174_ = lean_nat_dec_le(v_start_1157_, v_start_1159_);
if (v___x_1174_ == 0)
{
v___y_1163_ = v___x_1174_;
goto v___jp_1162_;
}
else
{
uint8_t v___x_1175_; 
v___x_1175_ = lean_nat_dec_le(v_stop_1160_, v_stop_1158_);
v___y_1163_ = v___x_1175_;
goto v___jp_1162_;
}
v___jp_1162_:
{
if (v___y_1163_ == 0)
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
lean_dec_ref(v_b_1143_);
v___x_1164_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___closed__2);
lean_inc(v_snd_1156_);
v___x_1165_ = l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2(v___x_1161_, v_snd_1156_, v___x_1164_, v___y_1144_, v___y_1145_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_dec_ref_known(v___x_1165_, 1);
lean_inc(v_fst_1155_);
v_a_1148_ = v_fst_1155_;
goto v___jp_1147_;
}
else
{
lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1173_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1168_ = v___x_1165_;
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___x_1165_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1171_; 
if (v_isShared_1169_ == 0)
{
v___x_1171_ = v___x_1168_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_a_1166_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
}
else
{
v_a_1148_ = v_b_1143_;
goto v___jp_1147_;
}
}
}
v___jp_1147_:
{
size_t v___x_1149_; size_t v___x_1150_; 
v___x_1149_ = ((size_t)1ULL);
v___x_1150_ = lean_usize_add(v_i_1142_, v___x_1149_);
v_i_1142_ = v___x_1150_;
v_b_1143_ = v_a_1148_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___boxed(lean_object* v_as_1176_, lean_object* v_sz_1177_, lean_object* v_i_1178_, lean_object* v_b_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
size_t v_sz_boxed_1183_; size_t v_i_boxed_1184_; lean_object* v_res_1185_; 
v_sz_boxed_1183_ = lean_unbox_usize(v_sz_1177_);
lean_dec(v_sz_1177_);
v_i_boxed_1184_ = lean_unbox_usize(v_i_1178_);
lean_dec(v_i_1178_);
v_res_1185_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5(v_as_1176_, v_sz_boxed_1183_, v_i_boxed_1184_, v_b_1179_, v___y_1180_, v___y_1181_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
lean_dec_ref(v_as_1176_);
return v_res_1185_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13_spec__16___redArg(lean_object* v_keys_1186_, lean_object* v_i_1187_, lean_object* v_k_1188_){
_start:
{
lean_object* v___x_1189_; uint8_t v___x_1190_; 
v___x_1189_ = lean_array_get_size(v_keys_1186_);
v___x_1190_ = lean_nat_dec_lt(v_i_1187_, v___x_1189_);
if (v___x_1190_ == 0)
{
lean_dec(v_i_1187_);
return v___x_1190_;
}
else
{
lean_object* v_k_x27_1191_; uint8_t v___x_1192_; 
v_k_x27_1191_ = lean_array_fget_borrowed(v_keys_1186_, v_i_1187_);
v___x_1192_ = lean_name_eq(v_k_1188_, v_k_x27_1191_);
if (v___x_1192_ == 0)
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = lean_unsigned_to_nat(1u);
v___x_1194_ = lean_nat_add(v_i_1187_, v___x_1193_);
lean_dec(v_i_1187_);
v_i_1187_ = v___x_1194_;
goto _start;
}
else
{
lean_dec(v_i_1187_);
return v___x_1192_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13_spec__16___redArg___boxed(lean_object* v_keys_1196_, lean_object* v_i_1197_, lean_object* v_k_1198_){
_start:
{
uint8_t v_res_1199_; lean_object* v_r_1200_; 
v_res_1199_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13_spec__16___redArg(v_keys_1196_, v_i_1197_, v_k_1198_);
lean_dec(v_k_1198_);
lean_dec_ref(v_keys_1196_);
v_r_1200_ = lean_box(v_res_1199_);
return v_r_1200_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg___closed__0(void){
_start:
{
size_t v___x_1201_; size_t v___x_1202_; size_t v___x_1203_; 
v___x_1201_ = ((size_t)5ULL);
v___x_1202_ = ((size_t)1ULL);
v___x_1203_ = lean_usize_shift_left(v___x_1202_, v___x_1201_);
return v___x_1203_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg___closed__1(void){
_start:
{
size_t v___x_1204_; size_t v___x_1205_; size_t v___x_1206_; 
v___x_1204_ = ((size_t)1ULL);
v___x_1205_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg___closed__0);
v___x_1206_ = lean_usize_sub(v___x_1205_, v___x_1204_);
return v___x_1206_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg(lean_object* v_x_1207_, size_t v_x_1208_, lean_object* v_x_1209_){
_start:
{
if (lean_obj_tag(v_x_1207_) == 0)
{
lean_object* v_es_1210_; lean_object* v___x_1211_; size_t v___x_1212_; size_t v___x_1213_; size_t v___x_1214_; lean_object* v_j_1215_; lean_object* v___x_1216_; 
v_es_1210_ = lean_ctor_get(v_x_1207_, 0);
v___x_1211_ = lean_box(2);
v___x_1212_ = ((size_t)5ULL);
v___x_1213_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg___closed__1);
v___x_1214_ = lean_usize_land(v_x_1208_, v___x_1213_);
v_j_1215_ = lean_usize_to_nat(v___x_1214_);
v___x_1216_ = lean_array_get_borrowed(v___x_1211_, v_es_1210_, v_j_1215_);
lean_dec(v_j_1215_);
switch(lean_obj_tag(v___x_1216_))
{
case 0:
{
lean_object* v_key_1217_; uint8_t v___x_1218_; 
v_key_1217_ = lean_ctor_get(v___x_1216_, 0);
v___x_1218_ = lean_name_eq(v_x_1209_, v_key_1217_);
return v___x_1218_;
}
case 1:
{
lean_object* v_node_1219_; size_t v___x_1220_; 
v_node_1219_ = lean_ctor_get(v___x_1216_, 0);
v___x_1220_ = lean_usize_shift_right(v_x_1208_, v___x_1212_);
v_x_1207_ = v_node_1219_;
v_x_1208_ = v___x_1220_;
goto _start;
}
default: 
{
uint8_t v___x_1222_; 
v___x_1222_ = 0;
return v___x_1222_;
}
}
}
else
{
lean_object* v_ks_1223_; lean_object* v___x_1224_; uint8_t v___x_1225_; 
v_ks_1223_ = lean_ctor_get(v_x_1207_, 0);
v___x_1224_ = lean_unsigned_to_nat(0u);
v___x_1225_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13_spec__16___redArg(v_ks_1223_, v___x_1224_, v_x_1209_);
return v___x_1225_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg___boxed(lean_object* v_x_1226_, lean_object* v_x_1227_, lean_object* v_x_1228_){
_start:
{
size_t v_x_13329__boxed_1229_; uint8_t v_res_1230_; lean_object* v_r_1231_; 
v_x_13329__boxed_1229_ = lean_unbox_usize(v_x_1227_);
lean_dec(v_x_1227_);
v_res_1230_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg(v_x_1226_, v_x_13329__boxed_1229_, v_x_1228_);
lean_dec(v_x_1228_);
lean_dec_ref(v_x_1226_);
v_r_1231_ = lean_box(v_res_1230_);
return v_r_1231_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9___redArg(lean_object* v_x_1232_, lean_object* v_x_1233_){
_start:
{
uint64_t v___y_1235_; 
if (lean_obj_tag(v_x_1233_) == 0)
{
uint64_t v___x_1238_; 
v___x_1238_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
v___y_1235_ = v___x_1238_;
goto v___jp_1234_;
}
else
{
uint64_t v_hash_1239_; 
v_hash_1239_ = lean_ctor_get_uint64(v_x_1233_, sizeof(void*)*2);
v___y_1235_ = v_hash_1239_;
goto v___jp_1234_;
}
v___jp_1234_:
{
size_t v___x_1236_; uint8_t v___x_1237_; 
v___x_1236_ = lean_uint64_to_usize(v___y_1235_);
v___x_1237_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg(v_x_1232_, v___x_1236_, v_x_1233_);
return v___x_1237_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9___redArg___boxed(lean_object* v_x_1240_, lean_object* v_x_1241_){
_start:
{
uint8_t v_res_1242_; lean_object* v_r_1243_; 
v_res_1242_ = l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9___redArg(v_x_1240_, v_x_1241_);
lean_dec(v_x_1241_);
lean_dec_ref(v_x_1240_);
v_r_1243_ = lean_box(v_res_1242_);
return v_r_1243_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19_spec__21_spec__25___redArg(lean_object* v_x_1244_, lean_object* v_x_1245_){
_start:
{
if (lean_obj_tag(v_x_1245_) == 0)
{
return v_x_1244_;
}
else
{
lean_object* v_key_1246_; lean_object* v_value_1247_; lean_object* v_tail_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1271_; 
v_key_1246_ = lean_ctor_get(v_x_1245_, 0);
v_value_1247_ = lean_ctor_get(v_x_1245_, 1);
v_tail_1248_ = lean_ctor_get(v_x_1245_, 2);
v_isSharedCheck_1271_ = !lean_is_exclusive(v_x_1245_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1250_ = v_x_1245_;
v_isShared_1251_ = v_isSharedCheck_1271_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_tail_1248_);
lean_inc(v_value_1247_);
lean_inc(v_key_1246_);
lean_dec(v_x_1245_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1271_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1252_; uint64_t v___x_1253_; uint64_t v___x_1254_; uint64_t v___x_1255_; uint64_t v_fold_1256_; uint64_t v___x_1257_; uint64_t v___x_1258_; uint64_t v___x_1259_; size_t v___x_1260_; size_t v___x_1261_; size_t v___x_1262_; size_t v___x_1263_; size_t v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1267_; 
v___x_1252_ = lean_array_get_size(v_x_1244_);
v___x_1253_ = l_Lean_Syntax_instHashableRange_hash(v_key_1246_);
v___x_1254_ = 32ULL;
v___x_1255_ = lean_uint64_shift_right(v___x_1253_, v___x_1254_);
v_fold_1256_ = lean_uint64_xor(v___x_1253_, v___x_1255_);
v___x_1257_ = 16ULL;
v___x_1258_ = lean_uint64_shift_right(v_fold_1256_, v___x_1257_);
v___x_1259_ = lean_uint64_xor(v_fold_1256_, v___x_1258_);
v___x_1260_ = lean_uint64_to_usize(v___x_1259_);
v___x_1261_ = lean_usize_of_nat(v___x_1252_);
v___x_1262_ = ((size_t)1ULL);
v___x_1263_ = lean_usize_sub(v___x_1261_, v___x_1262_);
v___x_1264_ = lean_usize_land(v___x_1260_, v___x_1263_);
v___x_1265_ = lean_array_uget_borrowed(v_x_1244_, v___x_1264_);
lean_inc(v___x_1265_);
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 2, v___x_1265_);
v___x_1267_ = v___x_1250_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_key_1246_);
lean_ctor_set(v_reuseFailAlloc_1270_, 1, v_value_1247_);
lean_ctor_set(v_reuseFailAlloc_1270_, 2, v___x_1265_);
v___x_1267_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
lean_object* v___x_1268_; 
v___x_1268_ = lean_array_uset(v_x_1244_, v___x_1264_, v___x_1267_);
v_x_1244_ = v___x_1268_;
v_x_1245_ = v_tail_1248_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19_spec__21___redArg(lean_object* v_i_1272_, lean_object* v_source_1273_, lean_object* v_target_1274_){
_start:
{
lean_object* v___x_1275_; uint8_t v___x_1276_; 
v___x_1275_ = lean_array_get_size(v_source_1273_);
v___x_1276_ = lean_nat_dec_lt(v_i_1272_, v___x_1275_);
if (v___x_1276_ == 0)
{
lean_dec_ref(v_source_1273_);
lean_dec(v_i_1272_);
return v_target_1274_;
}
else
{
lean_object* v_es_1277_; lean_object* v___x_1278_; lean_object* v_source_1279_; lean_object* v_target_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v_es_1277_ = lean_array_fget(v_source_1273_, v_i_1272_);
v___x_1278_ = lean_box(0);
v_source_1279_ = lean_array_fset(v_source_1273_, v_i_1272_, v___x_1278_);
v_target_1280_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19_spec__21_spec__25___redArg(v_target_1274_, v_es_1277_);
v___x_1281_ = lean_unsigned_to_nat(1u);
v___x_1282_ = lean_nat_add(v_i_1272_, v___x_1281_);
lean_dec(v_i_1272_);
v_i_1272_ = v___x_1282_;
v_source_1273_ = v_source_1279_;
v_target_1274_ = v_target_1280_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19___redArg(lean_object* v_data_1284_){
_start:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v_nbuckets_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1285_ = lean_array_get_size(v_data_1284_);
v___x_1286_ = lean_unsigned_to_nat(2u);
v_nbuckets_1287_ = lean_nat_mul(v___x_1285_, v___x_1286_);
v___x_1288_ = lean_unsigned_to_nat(0u);
v___x_1289_ = lean_box(0);
v___x_1290_ = lean_mk_array(v_nbuckets_1287_, v___x_1289_);
v___x_1291_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19_spec__21___redArg(v___x_1288_, v_data_1284_, v___x_1290_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__20___redArg(lean_object* v_a_1292_, lean_object* v_b_1293_, lean_object* v_x_1294_){
_start:
{
if (lean_obj_tag(v_x_1294_) == 0)
{
lean_dec(v_b_1293_);
lean_dec_ref(v_a_1292_);
return v_x_1294_;
}
else
{
lean_object* v_key_1295_; lean_object* v_value_1296_; lean_object* v_tail_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1309_; 
v_key_1295_ = lean_ctor_get(v_x_1294_, 0);
v_value_1296_ = lean_ctor_get(v_x_1294_, 1);
v_tail_1297_ = lean_ctor_get(v_x_1294_, 2);
v_isSharedCheck_1309_ = !lean_is_exclusive(v_x_1294_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1299_ = v_x_1294_;
v_isShared_1300_ = v_isSharedCheck_1309_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_tail_1297_);
lean_inc(v_value_1296_);
lean_inc(v_key_1295_);
lean_dec(v_x_1294_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1309_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
uint8_t v___x_1301_; 
v___x_1301_ = l_Lean_Syntax_instBEqRange_beq(v_key_1295_, v_a_1292_);
if (v___x_1301_ == 0)
{
lean_object* v___x_1302_; lean_object* v___x_1304_; 
v___x_1302_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__20___redArg(v_a_1292_, v_b_1293_, v_tail_1297_);
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 2, v___x_1302_);
v___x_1304_ = v___x_1299_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_key_1295_);
lean_ctor_set(v_reuseFailAlloc_1305_, 1, v_value_1296_);
lean_ctor_set(v_reuseFailAlloc_1305_, 2, v___x_1302_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
else
{
lean_object* v___x_1307_; 
lean_dec(v_value_1296_);
lean_dec(v_key_1295_);
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 1, v_b_1293_);
lean_ctor_set(v___x_1299_, 0, v_a_1292_);
v___x_1307_ = v___x_1299_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_a_1292_);
lean_ctor_set(v_reuseFailAlloc_1308_, 1, v_b_1293_);
lean_ctor_set(v_reuseFailAlloc_1308_, 2, v_tail_1297_);
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
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15___redArg(lean_object* v_m_1310_, lean_object* v_a_1311_, lean_object* v_b_1312_){
_start:
{
lean_object* v_size_1313_; lean_object* v_buckets_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1357_; 
v_size_1313_ = lean_ctor_get(v_m_1310_, 0);
v_buckets_1314_ = lean_ctor_get(v_m_1310_, 1);
v_isSharedCheck_1357_ = !lean_is_exclusive(v_m_1310_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1316_ = v_m_1310_;
v_isShared_1317_ = v_isSharedCheck_1357_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_buckets_1314_);
lean_inc(v_size_1313_);
lean_dec(v_m_1310_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1357_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1318_; uint64_t v___x_1319_; uint64_t v___x_1320_; uint64_t v___x_1321_; uint64_t v_fold_1322_; uint64_t v___x_1323_; uint64_t v___x_1324_; uint64_t v___x_1325_; size_t v___x_1326_; size_t v___x_1327_; size_t v___x_1328_; size_t v___x_1329_; size_t v___x_1330_; lean_object* v_bkt_1331_; uint8_t v___x_1332_; 
v___x_1318_ = lean_array_get_size(v_buckets_1314_);
v___x_1319_ = l_Lean_Syntax_instHashableRange_hash(v_a_1311_);
v___x_1320_ = 32ULL;
v___x_1321_ = lean_uint64_shift_right(v___x_1319_, v___x_1320_);
v_fold_1322_ = lean_uint64_xor(v___x_1319_, v___x_1321_);
v___x_1323_ = 16ULL;
v___x_1324_ = lean_uint64_shift_right(v_fold_1322_, v___x_1323_);
v___x_1325_ = lean_uint64_xor(v_fold_1322_, v___x_1324_);
v___x_1326_ = lean_uint64_to_usize(v___x_1325_);
v___x_1327_ = lean_usize_of_nat(v___x_1318_);
v___x_1328_ = ((size_t)1ULL);
v___x_1329_ = lean_usize_sub(v___x_1327_, v___x_1328_);
v___x_1330_ = lean_usize_land(v___x_1326_, v___x_1329_);
v_bkt_1331_ = lean_array_uget_borrowed(v_buckets_1314_, v___x_1330_);
v___x_1332_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5___redArg(v_a_1311_, v_bkt_1331_);
if (v___x_1332_ == 0)
{
lean_object* v___x_1333_; lean_object* v_size_x27_1334_; lean_object* v___x_1335_; lean_object* v_buckets_x27_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; uint8_t v___x_1342_; 
v___x_1333_ = lean_unsigned_to_nat(1u);
v_size_x27_1334_ = lean_nat_add(v_size_1313_, v___x_1333_);
lean_dec(v_size_1313_);
lean_inc(v_bkt_1331_);
v___x_1335_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1335_, 0, v_a_1311_);
lean_ctor_set(v___x_1335_, 1, v_b_1312_);
lean_ctor_set(v___x_1335_, 2, v_bkt_1331_);
v_buckets_x27_1336_ = lean_array_uset(v_buckets_1314_, v___x_1330_, v___x_1335_);
v___x_1337_ = lean_unsigned_to_nat(4u);
v___x_1338_ = lean_nat_mul(v_size_x27_1334_, v___x_1337_);
v___x_1339_ = lean_unsigned_to_nat(3u);
v___x_1340_ = lean_nat_div(v___x_1338_, v___x_1339_);
lean_dec(v___x_1338_);
v___x_1341_ = lean_array_get_size(v_buckets_x27_1336_);
v___x_1342_ = lean_nat_dec_le(v___x_1340_, v___x_1341_);
lean_dec(v___x_1340_);
if (v___x_1342_ == 0)
{
lean_object* v_val_1343_; lean_object* v___x_1345_; 
v_val_1343_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19___redArg(v_buckets_x27_1336_);
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 1, v_val_1343_);
lean_ctor_set(v___x_1316_, 0, v_size_x27_1334_);
v___x_1345_ = v___x_1316_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_size_x27_1334_);
lean_ctor_set(v_reuseFailAlloc_1346_, 1, v_val_1343_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
else
{
lean_object* v___x_1348_; 
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 1, v_buckets_x27_1336_);
lean_ctor_set(v___x_1316_, 0, v_size_x27_1334_);
v___x_1348_ = v___x_1316_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_size_x27_1334_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v_buckets_x27_1336_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
else
{
lean_object* v___x_1350_; lean_object* v_buckets_x27_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1355_; 
lean_inc(v_bkt_1331_);
v___x_1350_ = lean_box(0);
v_buckets_x27_1351_ = lean_array_uset(v_buckets_1314_, v___x_1330_, v___x_1350_);
v___x_1352_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__20___redArg(v_a_1311_, v_b_1312_, v_bkt_1331_);
v___x_1353_ = lean_array_uset(v_buckets_x27_1351_, v___x_1330_, v___x_1352_);
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 1, v___x_1353_);
v___x_1355_ = v___x_1316_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_size_1313_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v___x_1353_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10(lean_object* v___x_1358_, lean_object* v___x_1359_, uint8_t v___y_1360_, lean_object* v_ignoreTacticKinds_1361_, lean_object* v_stx_1362_, lean_object* v_a_1363_){
_start:
{
lean_object* v___y_1366_; uint8_t v___y_1367_; 
if (lean_obj_tag(v_stx_1362_) == 1)
{
lean_object* v_kind_1385_; lean_object* v_args_1386_; lean_object* v___y_1388_; lean_object* v___y_1392_; uint8_t v___x_1393_; 
v_kind_1385_ = lean_ctor_get(v_stx_1362_, 1);
v_args_1386_ = lean_ctor_get(v_stx_1362_, 2);
v___x_1393_ = l_Lean_Linter_Extra_UnreachableTactic_isIgnoreTacticKind(v_ignoreTacticKinds_1361_, v_kind_1385_);
if (v___x_1393_ == 0)
{
lean_object* v___x_1394_; lean_object* v___x_1395_; uint8_t v___x_1396_; 
v___x_1394_ = lean_unsigned_to_nat(0u);
v___x_1395_ = lean_array_get_size(v_args_1386_);
v___x_1396_ = lean_nat_dec_lt(v___x_1394_, v___x_1395_);
if (v___x_1396_ == 0)
{
v___y_1388_ = v_a_1363_;
goto v___jp_1387_;
}
else
{
lean_object* v___x_1397_; uint8_t v___x_1398_; 
v___x_1397_ = lean_box(0);
v___x_1398_ = lean_nat_dec_le(v___x_1395_, v___x_1395_);
if (v___x_1398_ == 0)
{
if (v___x_1396_ == 0)
{
v___y_1388_ = v_a_1363_;
goto v___jp_1387_;
}
else
{
size_t v___x_1399_; size_t v___x_1400_; lean_object* v___x_1401_; 
v___x_1399_ = ((size_t)0ULL);
v___x_1400_ = lean_usize_of_nat(v___x_1395_);
v___x_1401_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__16(v___x_1358_, v___x_1359_, v___y_1360_, v_ignoreTacticKinds_1361_, v_args_1386_, v___x_1399_, v___x_1400_, v___x_1397_, v_a_1363_);
v___y_1392_ = v___x_1401_;
goto v___jp_1391_;
}
}
else
{
size_t v___x_1402_; size_t v___x_1403_; lean_object* v___x_1404_; 
v___x_1402_ = ((size_t)0ULL);
v___x_1403_ = lean_usize_of_nat(v___x_1395_);
v___x_1404_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__16(v___x_1358_, v___x_1359_, v___y_1360_, v_ignoreTacticKinds_1361_, v_args_1386_, v___x_1402_, v___x_1403_, v___x_1397_, v_a_1363_);
v___y_1392_ = v___x_1404_;
goto v___jp_1391_;
}
}
}
else
{
v___y_1388_ = v_a_1363_;
goto v___jp_1387_;
}
v___jp_1387_:
{
uint8_t v___x_1389_; 
v___x_1389_ = l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9___redArg(v___x_1358_, v_kind_1385_);
if (v___x_1389_ == 0)
{
uint8_t v___x_1390_; 
v___x_1390_ = l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9___redArg(v___x_1359_, v_kind_1385_);
v___y_1366_ = v___y_1388_;
v___y_1367_ = v___x_1390_;
goto v___jp_1365_;
}
else
{
v___y_1366_ = v___y_1388_;
v___y_1367_ = v___y_1360_;
goto v___jp_1365_;
}
}
v___jp_1391_:
{
if (lean_obj_tag(v___y_1392_) == 0)
{
lean_dec_ref_known(v___y_1392_, 1);
v___y_1388_ = v_a_1363_;
goto v___jp_1387_;
}
else
{
lean_dec_ref_known(v_stx_1362_, 3);
return v___y_1392_;
}
}
}
else
{
lean_object* v___x_1405_; lean_object* v___x_1406_; 
lean_dec(v_stx_1362_);
v___x_1405_ = lean_box(0);
v___x_1406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1405_);
return v___x_1406_;
}
v___jp_1365_:
{
if (v___y_1367_ == 0)
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
lean_dec(v_stx_1362_);
v___x_1368_ = lean_box(0);
v___x_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1368_);
return v___x_1369_;
}
else
{
lean_object* v___x_1370_; 
v___x_1370_ = l_Lean_Syntax_getRange_x3f(v_stx_1362_, v___y_1367_);
if (lean_obj_tag(v___x_1370_) == 1)
{
lean_object* v_val_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1382_; 
v_val_1371_ = lean_ctor_get(v___x_1370_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1373_ = v___x_1370_;
v_isShared_1374_ = v_isSharedCheck_1382_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_val_1371_);
lean_dec(v___x_1370_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1382_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1380_; 
v___x_1375_ = lean_st_ref_take(v___y_1366_);
v___x_1376_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15___redArg(v___x_1375_, v_val_1371_, v_stx_1362_);
v___x_1377_ = lean_st_ref_set(v___y_1366_, v___x_1376_);
v___x_1378_ = lean_box(0);
if (v_isShared_1374_ == 0)
{
lean_ctor_set_tag(v___x_1373_, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1378_);
v___x_1380_ = v___x_1373_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v___x_1378_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
}
else
{
lean_object* v___x_1383_; lean_object* v___x_1384_; 
lean_dec(v___x_1370_);
lean_dec(v_stx_1362_);
v___x_1383_ = lean_box(0);
v___x_1384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1383_);
return v___x_1384_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__16(lean_object* v___x_1407_, lean_object* v___x_1408_, uint8_t v___y_1409_, lean_object* v_ignoreTacticKinds_1410_, lean_object* v_as_1411_, size_t v_i_1412_, size_t v_stop_1413_, lean_object* v_b_1414_, lean_object* v___y_1415_){
_start:
{
uint8_t v___x_1417_; 
v___x_1417_ = lean_usize_dec_eq(v_i_1412_, v_stop_1413_);
if (v___x_1417_ == 0)
{
lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1418_ = lean_array_uget_borrowed(v_as_1411_, v_i_1412_);
lean_inc(v___x_1418_);
v___x_1419_ = l_Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10(v___x_1407_, v___x_1408_, v___y_1409_, v_ignoreTacticKinds_1410_, v___x_1418_, v___y_1415_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v_a_1420_; size_t v___x_1421_; size_t v___x_1422_; 
v_a_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc(v_a_1420_);
lean_dec_ref_known(v___x_1419_, 1);
v___x_1421_ = ((size_t)1ULL);
v___x_1422_ = lean_usize_add(v_i_1412_, v___x_1421_);
v_i_1412_ = v___x_1422_;
v_b_1414_ = v_a_1420_;
goto _start;
}
else
{
return v___x_1419_;
}
}
else
{
lean_object* v___x_1424_; 
v___x_1424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1424_, 0, v_b_1414_);
return v___x_1424_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__16___boxed(lean_object* v___x_1425_, lean_object* v___x_1426_, lean_object* v___y_1427_, lean_object* v_ignoreTacticKinds_1428_, lean_object* v_as_1429_, lean_object* v_i_1430_, lean_object* v_stop_1431_, lean_object* v_b_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
uint8_t v___y_13586__boxed_1435_; size_t v_i_boxed_1436_; size_t v_stop_boxed_1437_; lean_object* v_res_1438_; 
v___y_13586__boxed_1435_ = lean_unbox(v___y_1427_);
v_i_boxed_1436_ = lean_unbox_usize(v_i_1430_);
lean_dec(v_i_1430_);
v_stop_boxed_1437_ = lean_unbox_usize(v_stop_1431_);
lean_dec(v_stop_1431_);
v_res_1438_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__16(v___x_1425_, v___x_1426_, v___y_13586__boxed_1435_, v_ignoreTacticKinds_1428_, v_as_1429_, v_i_boxed_1436_, v_stop_boxed_1437_, v_b_1432_, v___y_1433_);
lean_dec(v___y_1433_);
lean_dec_ref(v_as_1429_);
lean_dec_ref(v_ignoreTacticKinds_1428_);
lean_dec_ref(v___x_1426_);
lean_dec_ref(v___x_1425_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10___boxed(lean_object* v___x_1439_, lean_object* v___x_1440_, lean_object* v___y_1441_, lean_object* v_ignoreTacticKinds_1442_, lean_object* v_stx_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_){
_start:
{
uint8_t v___y_13600__boxed_1446_; lean_object* v_res_1447_; 
v___y_13600__boxed_1446_ = lean_unbox(v___y_1441_);
v_res_1447_ = l_Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10(v___x_1439_, v___x_1440_, v___y_13600__boxed_1446_, v_ignoreTacticKinds_1442_, v_stx_1443_, v_a_1444_);
lean_dec(v_a_1444_);
lean_dec_ref(v_ignoreTacticKinds_1442_);
lean_dec_ref(v___x_1440_);
lean_dec_ref(v___x_1439_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8___redArg(lean_object* v_keys_1448_, lean_object* v_vals_1449_, lean_object* v_i_1450_, lean_object* v_k_1451_){
_start:
{
lean_object* v___x_1452_; uint8_t v___x_1453_; 
v___x_1452_ = lean_array_get_size(v_keys_1448_);
v___x_1453_ = lean_nat_dec_lt(v_i_1450_, v___x_1452_);
if (v___x_1453_ == 0)
{
lean_object* v___x_1454_; 
lean_dec(v_i_1450_);
v___x_1454_ = lean_box(0);
return v___x_1454_;
}
else
{
lean_object* v_k_x27_1455_; uint8_t v___x_1456_; 
v_k_x27_1455_ = lean_array_fget_borrowed(v_keys_1448_, v_i_1450_);
v___x_1456_ = lean_name_eq(v_k_1451_, v_k_x27_1455_);
if (v___x_1456_ == 0)
{
lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1457_ = lean_unsigned_to_nat(1u);
v___x_1458_ = lean_nat_add(v_i_1450_, v___x_1457_);
lean_dec(v_i_1450_);
v_i_1450_ = v___x_1458_;
goto _start;
}
else
{
lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1460_ = lean_array_fget_borrowed(v_vals_1449_, v_i_1450_);
lean_dec(v_i_1450_);
lean_inc(v___x_1460_);
v___x_1461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1460_);
return v___x_1461_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_keys_1462_, lean_object* v_vals_1463_, lean_object* v_i_1464_, lean_object* v_k_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8___redArg(v_keys_1462_, v_vals_1463_, v_i_1464_, v_k_1465_);
lean_dec(v_k_1465_);
lean_dec_ref(v_vals_1463_);
lean_dec_ref(v_keys_1462_);
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5___redArg(lean_object* v_x_1467_, size_t v_x_1468_, lean_object* v_x_1469_){
_start:
{
if (lean_obj_tag(v_x_1467_) == 0)
{
lean_object* v_es_1470_; lean_object* v___x_1471_; size_t v___x_1472_; size_t v___x_1473_; size_t v___x_1474_; lean_object* v_j_1475_; lean_object* v___x_1476_; 
v_es_1470_ = lean_ctor_get(v_x_1467_, 0);
v___x_1471_ = lean_box(2);
v___x_1472_ = ((size_t)5ULL);
v___x_1473_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg___closed__1);
v___x_1474_ = lean_usize_land(v_x_1468_, v___x_1473_);
v_j_1475_ = lean_usize_to_nat(v___x_1474_);
v___x_1476_ = lean_array_get_borrowed(v___x_1471_, v_es_1470_, v_j_1475_);
lean_dec(v_j_1475_);
switch(lean_obj_tag(v___x_1476_))
{
case 0:
{
lean_object* v_key_1477_; lean_object* v_val_1478_; uint8_t v___x_1479_; 
v_key_1477_ = lean_ctor_get(v___x_1476_, 0);
v_val_1478_ = lean_ctor_get(v___x_1476_, 1);
v___x_1479_ = lean_name_eq(v_x_1469_, v_key_1477_);
if (v___x_1479_ == 0)
{
lean_object* v___x_1480_; 
v___x_1480_ = lean_box(0);
return v___x_1480_;
}
else
{
lean_object* v___x_1481_; 
lean_inc(v_val_1478_);
v___x_1481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1481_, 0, v_val_1478_);
return v___x_1481_;
}
}
case 1:
{
lean_object* v_node_1482_; size_t v___x_1483_; 
v_node_1482_ = lean_ctor_get(v___x_1476_, 0);
v___x_1483_ = lean_usize_shift_right(v_x_1468_, v___x_1472_);
v_x_1467_ = v_node_1482_;
v_x_1468_ = v___x_1483_;
goto _start;
}
default: 
{
lean_object* v___x_1485_; 
v___x_1485_ = lean_box(0);
return v___x_1485_;
}
}
}
else
{
lean_object* v_ks_1486_; lean_object* v_vs_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v_ks_1486_ = lean_ctor_get(v_x_1467_, 0);
v_vs_1487_ = lean_ctor_get(v_x_1467_, 1);
v___x_1488_ = lean_unsigned_to_nat(0u);
v___x_1489_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8___redArg(v_ks_1486_, v_vs_1487_, v___x_1488_, v_x_1469_);
return v___x_1489_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5___redArg___boxed(lean_object* v_x_1490_, lean_object* v_x_1491_, lean_object* v_x_1492_){
_start:
{
size_t v_x_13740__boxed_1493_; lean_object* v_res_1494_; 
v_x_13740__boxed_1493_ = lean_unbox_usize(v_x_1491_);
lean_dec(v_x_1491_);
v_res_1494_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5___redArg(v_x_1490_, v_x_13740__boxed_1493_, v_x_1492_);
lean_dec(v_x_1492_);
lean_dec_ref(v_x_1490_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3___redArg(lean_object* v_x_1495_, lean_object* v_x_1496_){
_start:
{
uint64_t v___y_1498_; 
if (lean_obj_tag(v_x_1496_) == 0)
{
uint64_t v___x_1501_; 
v___x_1501_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
v___y_1498_ = v___x_1501_;
goto v___jp_1497_;
}
else
{
uint64_t v_hash_1502_; 
v_hash_1502_ = lean_ctor_get_uint64(v_x_1496_, sizeof(void*)*2);
v___y_1498_ = v_hash_1502_;
goto v___jp_1497_;
}
v___jp_1497_:
{
size_t v___x_1499_; lean_object* v___x_1500_; 
v___x_1499_ = lean_uint64_to_usize(v___y_1498_);
v___x_1500_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5___redArg(v_x_1495_, v___x_1499_, v_x_1496_);
return v___x_1500_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3___redArg___boxed(lean_object* v_x_1503_, lean_object* v_x_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3___redArg(v_x_1503_, v_x_1504_);
lean_dec(v_x_1504_);
lean_dec_ref(v_x_1503_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7(lean_object* v_x_1506_, lean_object* v_x_1507_){
_start:
{
if (lean_obj_tag(v_x_1507_) == 0)
{
return v_x_1506_;
}
else
{
lean_object* v_key_1508_; lean_object* v_value_1509_; lean_object* v_tail_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
v_key_1508_ = lean_ctor_get(v_x_1507_, 0);
v_value_1509_ = lean_ctor_get(v_x_1507_, 1);
v_tail_1510_ = lean_ctor_get(v_x_1507_, 2);
lean_inc(v_value_1509_);
lean_inc(v_key_1508_);
v___x_1511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1511_, 0, v_key_1508_);
lean_ctor_set(v___x_1511_, 1, v_value_1509_);
v___x_1512_ = lean_array_push(v_x_1506_, v___x_1511_);
v_x_1506_ = v___x_1512_;
v_x_1507_ = v_tail_1510_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___boxed(lean_object* v_x_1514_, lean_object* v_x_1515_){
_start:
{
lean_object* v_res_1516_; 
v_res_1516_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7(v_x_1514_, v_x_1515_);
lean_dec(v_x_1515_);
return v_res_1516_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8(lean_object* v_as_1517_, size_t v_i_1518_, size_t v_stop_1519_, lean_object* v_b_1520_){
_start:
{
uint8_t v___x_1521_; 
v___x_1521_ = lean_usize_dec_eq(v_i_1518_, v_stop_1519_);
if (v___x_1521_ == 0)
{
lean_object* v___x_1522_; lean_object* v___x_1523_; size_t v___x_1524_; size_t v___x_1525_; 
v___x_1522_ = lean_array_uget_borrowed(v_as_1517_, v_i_1518_);
v___x_1523_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7(v_b_1520_, v___x_1522_);
v___x_1524_ = ((size_t)1ULL);
v___x_1525_ = lean_usize_add(v_i_1518_, v___x_1524_);
v_i_1518_ = v___x_1525_;
v_b_1520_ = v___x_1523_;
goto _start;
}
else
{
return v_b_1520_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8___boxed(lean_object* v_as_1527_, lean_object* v_i_1528_, lean_object* v_stop_1529_, lean_object* v_b_1530_){
_start:
{
size_t v_i_boxed_1531_; size_t v_stop_boxed_1532_; lean_object* v_res_1533_; 
v_i_boxed_1531_ = lean_unbox_usize(v_i_1528_);
lean_dec(v_i_1528_);
v_stop_boxed_1532_ = lean_unbox_usize(v_stop_1529_);
lean_dec(v_stop_1529_);
v_res_1533_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8(v_as_1527_, v_i_boxed_1531_, v_stop_boxed_1532_, v_b_1530_);
lean_dec_ref(v_as_1527_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___lam__0(lean_object* v_r_1534_){
_start:
{
lean_object* v_start_1535_; lean_object* v_stop_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1545_; 
v_start_1535_ = lean_ctor_get(v_r_1534_, 0);
v_stop_1536_ = lean_ctor_get(v_r_1534_, 1);
v_isSharedCheck_1545_ = !lean_is_exclusive(v_r_1534_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1538_ = v_r_1534_;
v_isShared_1539_ = v_isSharedCheck_1545_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_stop_1536_);
lean_inc(v_start_1535_);
lean_dec(v_r_1534_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1545_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1543_; 
v___x_1540_ = lean_nat_to_int(v_stop_1536_);
v___x_1541_ = lean_int_neg(v___x_1540_);
lean_dec(v___x_1540_);
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 1, v___x_1541_);
v___x_1543_ = v___x_1538_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_start_1535_);
lean_ctor_set(v_reuseFailAlloc_1544_, 1, v___x_1541_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9___redArg(lean_object* v_hi_1548_, lean_object* v_pivot_1549_, lean_object* v_as_1550_, lean_object* v_i_1551_, lean_object* v_k_1552_){
_start:
{
uint8_t v___x_1557_; 
v___x_1557_ = lean_nat_dec_lt(v_k_1552_, v_hi_1548_);
if (v___x_1557_ == 0)
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
lean_dec(v_k_1552_);
lean_dec_ref(v_pivot_1549_);
v___x_1558_ = lean_array_fswap(v_as_1550_, v_i_1551_, v_hi_1548_);
v___x_1559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1559_, 0, v_i_1551_);
lean_ctor_set(v___x_1559_, 1, v___x_1558_);
return v___x_1559_;
}
else
{
lean_object* v___x_1560_; lean_object* v_fst_1561_; lean_object* v_fst_1562_; lean_object* v___f_1563_; lean_object* v___f_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_12390__overap_1567_; lean_object* v___x_1568_; uint8_t v___x_1569_; 
v___x_1560_ = lean_array_fget_borrowed(v_as_1550_, v_k_1552_);
v_fst_1561_ = lean_ctor_get(v___x_1560_, 0);
v_fst_1562_ = lean_ctor_get(v_pivot_1549_, 0);
v___f_1563_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9___redArg___closed__0));
v___f_1564_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9___redArg___closed__1));
lean_inc(v_fst_1561_);
v___x_1565_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___lam__0(v_fst_1561_);
lean_inc(v_fst_1562_);
v___x_1566_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___lam__0(v_fst_1562_);
v___x_12390__overap_1567_ = l_lexOrd___redArg(v___f_1563_, v___f_1564_);
v___x_1568_ = lean_apply_2(v___x_12390__overap_1567_, v___x_1565_, v___x_1566_);
v___x_1569_ = lean_unbox(v___x_1568_);
if (v___x_1569_ == 0)
{
if (v___x_1557_ == 0)
{
goto v___jp_1553_;
}
else
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1570_ = lean_array_fswap(v_as_1550_, v_i_1551_, v_k_1552_);
v___x_1571_ = lean_unsigned_to_nat(1u);
v___x_1572_ = lean_nat_add(v_i_1551_, v___x_1571_);
lean_dec(v_i_1551_);
v___x_1573_ = lean_nat_add(v_k_1552_, v___x_1571_);
lean_dec(v_k_1552_);
v_as_1550_ = v___x_1570_;
v_i_1551_ = v___x_1572_;
v_k_1552_ = v___x_1573_;
goto _start;
}
}
else
{
goto v___jp_1553_;
}
}
v___jp_1553_:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1554_ = lean_unsigned_to_nat(1u);
v___x_1555_ = lean_nat_add(v_k_1552_, v___x_1554_);
lean_dec(v_k_1552_);
v_k_1552_ = v___x_1555_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9___redArg___boxed(lean_object* v_hi_1575_, lean_object* v_pivot_1576_, lean_object* v_as_1577_, lean_object* v_i_1578_, lean_object* v_k_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9___redArg(v_hi_1575_, v_pivot_1576_, v_as_1577_, v_i_1578_, v_k_1579_);
lean_dec(v_hi_1575_);
return v_res_1580_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___lam__1(lean_object* v___f_1581_, uint8_t v___x_1582_, lean_object* v_x1_1583_, lean_object* v_x2_1584_){
_start:
{
lean_object* v_fst_1585_; lean_object* v_fst_1586_; lean_object* v___f_1587_; lean_object* v___f_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_12653__overap_1591_; lean_object* v___x_1592_; uint8_t v___x_1593_; 
v_fst_1585_ = lean_ctor_get(v_x1_1583_, 0);
lean_inc(v_fst_1585_);
lean_dec_ref(v_x1_1583_);
v_fst_1586_ = lean_ctor_get(v_x2_1584_, 0);
lean_inc(v_fst_1586_);
lean_dec_ref(v_x2_1584_);
v___f_1587_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9___redArg___closed__0));
v___f_1588_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9___redArg___closed__1));
lean_inc_ref(v___f_1581_);
v___x_1589_ = lean_apply_1(v___f_1581_, v_fst_1585_);
v___x_1590_ = lean_apply_1(v___f_1581_, v_fst_1586_);
v___x_12653__overap_1591_ = l_lexOrd___redArg(v___f_1587_, v___f_1588_);
v___x_1592_ = lean_apply_2(v___x_12653__overap_1591_, v___x_1589_, v___x_1590_);
v___x_1593_ = lean_unbox(v___x_1592_);
if (v___x_1593_ == 0)
{
return v___x_1582_;
}
else
{
uint8_t v___x_1594_; 
v___x_1594_ = 0;
return v___x_1594_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___lam__1___boxed(lean_object* v___f_1595_, lean_object* v___x_1596_, lean_object* v_x1_1597_, lean_object* v_x2_1598_){
_start:
{
uint8_t v___x_13902__boxed_1599_; uint8_t v_res_1600_; lean_object* v_r_1601_; 
v___x_13902__boxed_1599_ = lean_unbox(v___x_1596_);
v_res_1600_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___lam__1(v___f_1595_, v___x_13902__boxed_1599_, v_x1_1597_, v_x2_1598_);
v_r_1601_ = lean_box(v_res_1600_);
return v_r_1601_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg(lean_object* v_n_1603_, lean_object* v_as_1604_, lean_object* v_lo_1605_, lean_object* v_hi_1606_){
_start:
{
lean_object* v___y_1608_; uint8_t v___x_1618_; 
v___x_1618_ = lean_nat_dec_lt(v_lo_1605_, v_hi_1606_);
if (v___x_1618_ == 0)
{
lean_dec(v_lo_1605_);
return v_as_1604_;
}
else
{
lean_object* v___f_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v_mid_1622_; lean_object* v___y_1624_; lean_object* v___y_1630_; lean_object* v___x_1635_; lean_object* v___x_1636_; uint8_t v___x_1637_; 
v___f_1619_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___closed__0));
v___x_1620_ = lean_nat_add(v_lo_1605_, v_hi_1606_);
v___x_1621_ = lean_unsigned_to_nat(1u);
v_mid_1622_ = lean_nat_shiftr(v___x_1620_, v___x_1621_);
lean_dec(v___x_1620_);
v___x_1635_ = lean_array_fget_borrowed(v_as_1604_, v_mid_1622_);
v___x_1636_ = lean_array_fget_borrowed(v_as_1604_, v_lo_1605_);
lean_inc(v___x_1636_);
lean_inc(v___x_1635_);
v___x_1637_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___lam__1(v___f_1619_, v___x_1618_, v___x_1635_, v___x_1636_);
if (v___x_1637_ == 0)
{
v___y_1630_ = v_as_1604_;
goto v___jp_1629_;
}
else
{
lean_object* v___x_1638_; 
v___x_1638_ = lean_array_fswap(v_as_1604_, v_lo_1605_, v_mid_1622_);
v___y_1630_ = v___x_1638_;
goto v___jp_1629_;
}
v___jp_1623_:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; uint8_t v___x_1627_; 
v___x_1625_ = lean_array_fget_borrowed(v___y_1624_, v_mid_1622_);
v___x_1626_ = lean_array_fget_borrowed(v___y_1624_, v_hi_1606_);
lean_inc(v___x_1626_);
lean_inc(v___x_1625_);
v___x_1627_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___lam__1(v___f_1619_, v___x_1618_, v___x_1625_, v___x_1626_);
if (v___x_1627_ == 0)
{
lean_dec(v_mid_1622_);
v___y_1608_ = v___y_1624_;
goto v___jp_1607_;
}
else
{
lean_object* v___x_1628_; 
v___x_1628_ = lean_array_fswap(v___y_1624_, v_mid_1622_, v_hi_1606_);
lean_dec(v_mid_1622_);
v___y_1608_ = v___x_1628_;
goto v___jp_1607_;
}
}
v___jp_1629_:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; uint8_t v___x_1633_; 
v___x_1631_ = lean_array_fget_borrowed(v___y_1630_, v_hi_1606_);
v___x_1632_ = lean_array_fget_borrowed(v___y_1630_, v_lo_1605_);
lean_inc(v___x_1632_);
lean_inc(v___x_1631_);
v___x_1633_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___lam__1(v___f_1619_, v___x_1618_, v___x_1631_, v___x_1632_);
if (v___x_1633_ == 0)
{
v___y_1624_ = v___y_1630_;
goto v___jp_1623_;
}
else
{
lean_object* v___x_1634_; 
v___x_1634_ = lean_array_fswap(v___y_1630_, v_lo_1605_, v_hi_1606_);
v___y_1624_ = v___x_1634_;
goto v___jp_1623_;
}
}
}
v___jp_1607_:
{
lean_object* v_pivot_1609_; lean_object* v___x_1610_; lean_object* v_fst_1611_; lean_object* v_snd_1612_; uint8_t v___x_1613_; 
v_pivot_1609_ = lean_array_fget(v___y_1608_, v_hi_1606_);
lean_inc_n(v_lo_1605_, 2);
v___x_1610_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9___redArg(v_hi_1606_, v_pivot_1609_, v___y_1608_, v_lo_1605_, v_lo_1605_);
v_fst_1611_ = lean_ctor_get(v___x_1610_, 0);
lean_inc(v_fst_1611_);
v_snd_1612_ = lean_ctor_get(v___x_1610_, 1);
lean_inc(v_snd_1612_);
lean_dec_ref(v___x_1610_);
v___x_1613_ = lean_nat_dec_le(v_hi_1606_, v_fst_1611_);
if (v___x_1613_ == 0)
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___x_1614_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg(v_n_1603_, v_snd_1612_, v_lo_1605_, v_fst_1611_);
v___x_1615_ = lean_unsigned_to_nat(1u);
v___x_1616_ = lean_nat_add(v_fst_1611_, v___x_1615_);
lean_dec(v_fst_1611_);
v_as_1604_ = v___x_1614_;
v_lo_1605_ = v___x_1616_;
goto _start;
}
else
{
lean_dec(v_fst_1611_);
lean_dec(v_lo_1605_);
return v_snd_1612_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___boxed(lean_object* v_n_1639_, lean_object* v_as_1640_, lean_object* v_lo_1641_, lean_object* v_hi_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg(v_n_1639_, v_as_1640_, v_lo_1641_, v_hi_1642_);
lean_dec(v_hi_1642_);
lean_dec(v_n_1639_);
return v_res_1643_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1650_ = lean_box(0);
v___x_1651_ = lean_unsigned_to_nat(16u);
v___x_1652_ = lean_mk_array(v___x_1651_, v___x_1650_);
return v___x_1652_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1653_ = lean_obj_once(&l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__4, &l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__4_once, _init_l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__4);
v___x_1654_ = lean_unsigned_to_nat(0u);
v___x_1655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1654_);
lean_ctor_set(v___x_1655_, 1, v___x_1653_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0(lean_object* v_stx_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_){
_start:
{
lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v___y_1691_; lean_object* v___y_1692_; lean_object* v___y_1693_; lean_object* v___y_1694_; lean_object* v___y_1695_; lean_object* v___y_1698_; lean_object* v___y_1699_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___x_1736_; lean_object* v_a_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1793_; 
v___x_1736_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1(v___y_1657_, v___y_1658_);
v_a_1737_ = lean_ctor_get(v___x_1736_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1736_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1739_ = v___x_1736_;
v_isShared_1740_ = v_isSharedCheck_1793_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_a_1737_);
lean_dec(v___x_1736_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1793_;
goto v_resetjp_1738_;
}
v___jp_1660_:
{
size_t v_sz_1663_; size_t v___x_1664_; lean_object* v___x_1665_; 
v_sz_1663_ = lean_array_size(v___y_1662_);
v___x_1664_ = ((size_t)0ULL);
v___x_1665_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5(v___y_1662_, v_sz_1663_, v___x_1664_, v___y_1661_, v___y_1657_, v___y_1658_);
lean_dec_ref(v___y_1662_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1673_; 
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1673_ == 0)
{
lean_object* v_unused_1674_; 
v_unused_1674_ = lean_ctor_get(v___x_1665_, 0);
lean_dec(v_unused_1674_);
v___x_1667_ = v___x_1665_;
v_isShared_1668_ = v_isSharedCheck_1673_;
goto v_resetjp_1666_;
}
else
{
lean_dec(v___x_1665_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1673_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1669_; lean_object* v___x_1671_; 
v___x_1669_ = lean_box(0);
if (v_isShared_1668_ == 0)
{
lean_ctor_set(v___x_1667_, 0, v___x_1669_);
v___x_1671_ = v___x_1667_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v___x_1669_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
else
{
lean_object* v_a_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1682_; 
v_a_1675_ = lean_ctor_get(v___x_1665_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1677_ = v___x_1665_;
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_a_1675_);
lean_dec(v___x_1665_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1680_; 
if (v_isShared_1678_ == 0)
{
v___x_1680_ = v___x_1677_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_a_1675_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
}
}
v___jp_1683_:
{
lean_object* v___x_1689_; 
v___x_1689_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg(v___y_1684_, v___y_1686_, v___y_1685_, v___y_1688_);
lean_dec(v___y_1688_);
lean_dec(v___y_1684_);
v___y_1661_ = v___y_1687_;
v___y_1662_ = v___x_1689_;
goto v___jp_1660_;
}
v___jp_1690_:
{
uint8_t v___x_1696_; 
v___x_1696_ = lean_nat_dec_le(v___y_1695_, v___y_1691_);
if (v___x_1696_ == 0)
{
lean_dec(v___y_1691_);
lean_inc(v___y_1695_);
v___y_1684_ = v___y_1692_;
v___y_1685_ = v___y_1695_;
v___y_1686_ = v___y_1693_;
v___y_1687_ = v___y_1694_;
v___y_1688_ = v___y_1695_;
goto v___jp_1683_;
}
else
{
v___y_1684_ = v___y_1692_;
v___y_1685_ = v___y_1695_;
v___y_1686_ = v___y_1693_;
v___y_1687_ = v___y_1694_;
v___y_1688_ = v___y_1691_;
goto v___jp_1683_;
}
}
v___jp_1697_:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; uint8_t v___x_1702_; 
lean_inc_n(v___y_1698_, 2);
v___x_1700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1700_, 0, v___y_1698_);
lean_ctor_set(v___x_1700_, 1, v___y_1698_);
v___x_1701_ = lean_array_get_size(v___y_1699_);
v___x_1702_ = lean_nat_dec_eq(v___x_1701_, v___y_1698_);
if (v___x_1702_ == 0)
{
lean_object* v___x_1703_; lean_object* v___x_1704_; uint8_t v___x_1705_; 
v___x_1703_ = lean_unsigned_to_nat(1u);
v___x_1704_ = lean_nat_sub(v___x_1701_, v___x_1703_);
v___x_1705_ = lean_nat_dec_le(v___y_1698_, v___x_1704_);
if (v___x_1705_ == 0)
{
lean_dec(v___y_1698_);
lean_inc(v___x_1704_);
v___y_1691_ = v___x_1704_;
v___y_1692_ = v___x_1701_;
v___y_1693_ = v___y_1699_;
v___y_1694_ = v___x_1700_;
v___y_1695_ = v___x_1704_;
goto v___jp_1690_;
}
else
{
v___y_1691_ = v___x_1704_;
v___y_1692_ = v___x_1701_;
v___y_1693_ = v___y_1699_;
v___y_1694_ = v___x_1700_;
v___y_1695_ = v___y_1698_;
goto v___jp_1690_;
}
}
else
{
lean_dec(v___y_1698_);
v___y_1661_ = v___x_1700_;
v___y_1662_ = v___y_1699_;
goto v___jp_1660_;
}
}
v___jp_1706_:
{
if (lean_obj_tag(v___y_1709_) == 0)
{
lean_object* v___x_1710_; lean_object* v_size_1711_; lean_object* v_buckets_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; uint8_t v___x_1715_; 
lean_dec_ref_known(v___y_1709_, 1);
v___x_1710_ = lean_st_ref_get(v___y_1708_);
lean_dec(v___y_1708_);
v_size_1711_ = lean_ctor_get(v___x_1710_, 0);
lean_inc(v_size_1711_);
v_buckets_1712_ = lean_ctor_get(v___x_1710_, 1);
lean_inc_ref(v_buckets_1712_);
lean_dec(v___x_1710_);
v___x_1713_ = lean_mk_empty_array_with_capacity(v_size_1711_);
lean_dec(v_size_1711_);
v___x_1714_ = lean_array_get_size(v_buckets_1712_);
v___x_1715_ = lean_nat_dec_lt(v___y_1707_, v___x_1714_);
if (v___x_1715_ == 0)
{
lean_dec_ref(v_buckets_1712_);
v___y_1698_ = v___y_1707_;
v___y_1699_ = v___x_1713_;
goto v___jp_1697_;
}
else
{
uint8_t v___x_1716_; 
v___x_1716_ = lean_nat_dec_le(v___x_1714_, v___x_1714_);
if (v___x_1716_ == 0)
{
if (v___x_1715_ == 0)
{
lean_dec_ref(v_buckets_1712_);
v___y_1698_ = v___y_1707_;
v___y_1699_ = v___x_1713_;
goto v___jp_1697_;
}
else
{
size_t v___x_1717_; size_t v___x_1718_; lean_object* v___x_1719_; 
v___x_1717_ = ((size_t)0ULL);
v___x_1718_ = lean_usize_of_nat(v___x_1714_);
v___x_1719_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8(v_buckets_1712_, v___x_1717_, v___x_1718_, v___x_1713_);
lean_dec_ref(v_buckets_1712_);
v___y_1698_ = v___y_1707_;
v___y_1699_ = v___x_1719_;
goto v___jp_1697_;
}
}
else
{
size_t v___x_1720_; size_t v___x_1721_; lean_object* v___x_1722_; 
v___x_1720_ = ((size_t)0ULL);
v___x_1721_ = lean_usize_of_nat(v___x_1714_);
v___x_1722_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8(v_buckets_1712_, v___x_1720_, v___x_1721_, v___x_1713_);
lean_dec_ref(v_buckets_1712_);
v___y_1698_ = v___y_1707_;
v___y_1699_ = v___x_1722_;
goto v___jp_1697_;
}
}
}
else
{
lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1735_; 
lean_dec(v___y_1708_);
lean_dec(v___y_1707_);
v_a_1723_ = lean_ctor_get(v___y_1709_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___y_1709_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1725_ = v___y_1709_;
v_isShared_1726_ = v_isSharedCheck_1735_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_dec(v___y_1709_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1735_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v_ref_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1733_; 
v_ref_1727_ = lean_ctor_get(v___y_1657_, 7);
v___x_1728_ = lean_io_error_to_string(v_a_1723_);
v___x_1729_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1728_);
v___x_1730_ = l_Lean_MessageData_ofFormat(v___x_1729_);
lean_inc(v_ref_1727_);
v___x_1731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1731_, 0, v_ref_1727_);
lean_ctor_set(v___x_1731_, 1, v___x_1730_);
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 0, v___x_1731_);
v___x_1733_ = v___x_1725_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v___x_1731_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
}
}
v_resetjp_1738_:
{
lean_object* v___x_1741_; uint8_t v___y_1743_; lean_object* v___x_1789_; uint8_t v___x_1790_; 
v___x_1741_ = lean_st_ref_get(v___y_1658_);
v___x_1789_ = l_Lean_Linter_Extra_linter_extra_unreachableTactic;
v___x_1790_ = l_Lean_Linter_getLinterValue(v___x_1789_, v_a_1737_);
lean_dec(v_a_1737_);
if (v___x_1790_ == 0)
{
lean_dec(v___x_1741_);
v___y_1743_ = v___x_1790_;
goto v___jp_1742_;
}
else
{
lean_object* v_infoState_1791_; uint8_t v_enabled_1792_; 
v_infoState_1791_ = lean_ctor_get(v___x_1741_, 8);
lean_inc_ref(v_infoState_1791_);
lean_dec(v___x_1741_);
v_enabled_1792_ = lean_ctor_get_uint8(v_infoState_1791_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1791_);
v___y_1743_ = v_enabled_1792_;
goto v___jp_1742_;
}
v___jp_1742_:
{
if (v___y_1743_ == 0)
{
lean_object* v___x_1744_; lean_object* v___x_1746_; 
lean_dec(v_stx_1656_);
v___x_1744_ = lean_box(0);
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 0, v___x_1744_);
v___x_1746_ = v___x_1739_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v___x_1744_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
else
{
lean_object* v___x_1748_; lean_object* v_messages_1749_; uint8_t v___x_1750_; 
v___x_1748_ = lean_st_ref_get(v___y_1658_);
v_messages_1749_ = lean_ctor_get(v___x_1748_, 1);
lean_inc_ref(v_messages_1749_);
lean_dec(v___x_1748_);
v___x_1750_ = l_Lean_MessageLog_hasErrors(v_messages_1749_);
lean_dec_ref(v_messages_1749_);
if (v___x_1750_ == 0)
{
lean_object* v___x_1751_; lean_object* v_env_1752_; lean_object* v___x_1753_; lean_object* v_ext_1754_; lean_object* v_toEnvExtension_1755_; lean_object* v_asyncMode_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v_categories_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1751_ = lean_st_ref_get(v___y_1658_);
v_env_1752_ = lean_ctor_get(v___x_1751_, 0);
lean_inc_ref(v_env_1752_);
lean_dec(v___x_1751_);
v___x_1753_ = l_Lean_Parser_parserExtension;
v_ext_1754_ = lean_ctor_get(v___x_1753_, 1);
v_toEnvExtension_1755_ = lean_ctor_get(v_ext_1754_, 0);
v_asyncMode_1756_ = lean_ctor_get(v_toEnvExtension_1755_, 2);
v___x_1757_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_1758_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1757_, v___x_1753_, v_env_1752_, v_asyncMode_1756_);
v_categories_1759_ = lean_ctor_get(v___x_1758_, 2);
lean_inc_ref(v_categories_1759_);
lean_dec(v___x_1758_);
v___x_1760_ = ((lean_object*)(l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__1));
v___x_1761_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3___redArg(v_categories_1759_, v___x_1760_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v___x_1762_; lean_object* v___x_1764_; 
lean_dec_ref(v_categories_1759_);
lean_dec(v_stx_1656_);
v___x_1762_ = lean_box(0);
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 0, v___x_1762_);
v___x_1764_ = v___x_1739_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v___x_1762_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
else
{
lean_object* v_val_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
v_val_1766_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_val_1766_);
lean_dec_ref_known(v___x_1761_, 1);
v___x_1767_ = ((lean_object*)(l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__3));
v___x_1768_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3___redArg(v_categories_1759_, v___x_1767_);
lean_dec_ref(v_categories_1759_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v___x_1769_; lean_object* v___x_1771_; 
lean_dec(v_val_1766_);
lean_dec(v_stx_1656_);
v___x_1769_ = lean_box(0);
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 0, v___x_1769_);
v___x_1771_ = v___x_1739_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1769_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
return v___x_1771_;
}
}
else
{
lean_object* v_val_1773_; lean_object* v___x_1774_; lean_object* v_a_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v_kinds_1781_; lean_object* v_kinds_1782_; lean_object* v___x_1783_; 
lean_del_object(v___x_1739_);
v_val_1773_ = lean_ctor_get(v___x_1768_, 0);
lean_inc(v_val_1773_);
lean_dec_ref_known(v___x_1768_, 1);
v___x_1774_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4___redArg(v___y_1658_);
v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
lean_inc(v_a_1775_);
lean_dec_ref(v___x_1774_);
v___x_1776_ = lean_unsigned_to_nat(0u);
v___x_1777_ = lean_obj_once(&l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__5, &l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__5_once, _init_l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__5);
v___x_1778_ = lean_st_mk_ref(v___x_1777_);
v___x_1779_ = l_Lean_Linter_Extra_UnreachableTactic_ignoreTacticKindsRef;
v___x_1780_ = lean_st_ref_get(v___x_1779_);
v_kinds_1781_ = lean_ctor_get(v_val_1766_, 1);
lean_inc_ref(v_kinds_1781_);
lean_dec(v_val_1766_);
v_kinds_1782_ = lean_ctor_get(v_val_1773_, 1);
lean_inc_ref(v_kinds_1782_);
lean_dec(v_val_1773_);
v___x_1783_ = l_Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10(v_kinds_1781_, v_kinds_1782_, v___y_1743_, v___x_1780_, v_stx_1656_, v___x_1778_);
lean_dec(v___x_1780_);
lean_dec_ref(v_kinds_1782_);
lean_dec_ref(v_kinds_1781_);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_object* v___x_1784_; 
lean_dec_ref_known(v___x_1783_, 1);
v___x_1784_ = l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList(v_a_1775_, v___x_1778_);
v___y_1707_ = v___x_1776_;
v___y_1708_ = v___x_1778_;
v___y_1709_ = v___x_1784_;
goto v___jp_1706_;
}
else
{
lean_dec(v_a_1775_);
v___y_1707_ = v___x_1776_;
v___y_1708_ = v___x_1778_;
v___y_1709_ = v___x_1783_;
goto v___jp_1706_;
}
}
}
}
else
{
lean_object* v___x_1785_; lean_object* v___x_1787_; 
lean_dec(v_stx_1656_);
v___x_1785_ = lean_box(0);
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 0, v___x_1785_);
v___x_1787_ = v___x_1739_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v___x_1785_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___boxed(lean_object* v_stx_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0(v_stx_1794_, v___y_1795_, v___y_1796_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1(lean_object* v_o_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1___redArg(v_o_1814_, v___y_1816_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1___boxed(lean_object* v_o_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1(v_o_1819_, v___y_1820_, v___y_1821_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3(lean_object* v_00_u03b2_1824_, lean_object* v_x_1825_, lean_object* v_x_1826_){
_start:
{
lean_object* v___x_1827_; 
v___x_1827_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3___redArg(v_x_1825_, v_x_1826_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3___boxed(lean_object* v_00_u03b2_1828_, lean_object* v_x_1829_, lean_object* v_x_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3(v_00_u03b2_1828_, v_x_1829_, v_x_1830_);
lean_dec(v_x_1830_);
lean_dec_ref(v_x_1829_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6(lean_object* v_n_1832_, lean_object* v_as_1833_, lean_object* v_lo_1834_, lean_object* v_hi_1835_, lean_object* v_w_1836_, lean_object* v_hlo_1837_, lean_object* v_hhi_1838_){
_start:
{
lean_object* v___x_1839_; 
v___x_1839_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg(v_n_1832_, v_as_1833_, v_lo_1834_, v_hi_1835_);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___boxed(lean_object* v_n_1840_, lean_object* v_as_1841_, lean_object* v_lo_1842_, lean_object* v_hi_1843_, lean_object* v_w_1844_, lean_object* v_hlo_1845_, lean_object* v_hhi_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6(v_n_1840_, v_as_1841_, v_lo_1842_, v_hi_1843_, v_w_1844_, v_hlo_1845_, v_hhi_1846_);
lean_dec(v_hi_1843_);
lean_dec(v_n_1840_);
return v_res_1847_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9(lean_object* v_00_u03b2_1848_, lean_object* v_x_1849_, lean_object* v_x_1850_){
_start:
{
uint8_t v___x_1851_; 
v___x_1851_ = l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9___redArg(v_x_1849_, v_x_1850_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9___boxed(lean_object* v_00_u03b2_1852_, lean_object* v_x_1853_, lean_object* v_x_1854_){
_start:
{
uint8_t v_res_1855_; lean_object* v_r_1856_; 
v_res_1855_ = l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9(v_00_u03b2_1852_, v_x_1853_, v_x_1854_);
lean_dec(v_x_1854_);
lean_dec_ref(v_x_1853_);
v_r_1856_ = lean_box(v_res_1855_);
return v_r_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5(lean_object* v_00_u03b2_1857_, lean_object* v_x_1858_, size_t v_x_1859_, lean_object* v_x_1860_){
_start:
{
lean_object* v___x_1861_; 
v___x_1861_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5___redArg(v_x_1858_, v_x_1859_, v_x_1860_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5___boxed(lean_object* v_00_u03b2_1862_, lean_object* v_x_1863_, lean_object* v_x_1864_, lean_object* v_x_1865_){
_start:
{
size_t v_x_14358__boxed_1866_; lean_object* v_res_1867_; 
v_x_14358__boxed_1866_ = lean_unbox_usize(v_x_1864_);
lean_dec(v_x_1864_);
v_res_1867_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5(v_00_u03b2_1862_, v_x_1863_, v_x_14358__boxed_1866_, v_x_1865_);
lean_dec(v_x_1865_);
lean_dec_ref(v_x_1863_);
return v_res_1867_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9(lean_object* v_n_1868_, lean_object* v_lo_1869_, lean_object* v_hi_1870_, lean_object* v_hhi_1871_, lean_object* v_pivot_1872_, lean_object* v_as_1873_, lean_object* v_i_1874_, lean_object* v_k_1875_, lean_object* v_ilo_1876_, lean_object* v_ik_1877_, lean_object* v_w_1878_){
_start:
{
lean_object* v___x_1879_; 
v___x_1879_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9___redArg(v_hi_1870_, v_pivot_1872_, v_as_1873_, v_i_1874_, v_k_1875_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9___boxed(lean_object* v_n_1880_, lean_object* v_lo_1881_, lean_object* v_hi_1882_, lean_object* v_hhi_1883_, lean_object* v_pivot_1884_, lean_object* v_as_1885_, lean_object* v_i_1886_, lean_object* v_k_1887_, lean_object* v_ilo_1888_, lean_object* v_ik_1889_, lean_object* v_w_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9(v_n_1880_, v_lo_1881_, v_hi_1882_, v_hhi_1883_, v_pivot_1884_, v_as_1885_, v_i_1886_, v_k_1887_, v_ilo_1888_, v_ik_1889_, v_w_1890_);
lean_dec(v_hi_1882_);
lean_dec(v_lo_1881_);
lean_dec(v_n_1880_);
return v_res_1891_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13(lean_object* v_00_u03b2_1892_, lean_object* v_x_1893_, size_t v_x_1894_, lean_object* v_x_1895_){
_start:
{
uint8_t v___x_1896_; 
v___x_1896_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg(v_x_1893_, v_x_1894_, v_x_1895_);
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___boxed(lean_object* v_00_u03b2_1897_, lean_object* v_x_1898_, lean_object* v_x_1899_, lean_object* v_x_1900_){
_start:
{
size_t v_x_14371__boxed_1901_; uint8_t v_res_1902_; lean_object* v_r_1903_; 
v_x_14371__boxed_1901_ = lean_unbox_usize(v_x_1899_);
lean_dec(v_x_1899_);
v_res_1902_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13(v_00_u03b2_1897_, v_x_1898_, v_x_14371__boxed_1901_, v_x_1900_);
lean_dec(v_x_1900_);
lean_dec_ref(v_x_1898_);
v_r_1903_ = lean_box(v_res_1902_);
return v_r_1903_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15(lean_object* v_00_u03b2_1904_, lean_object* v_m_1905_, lean_object* v_a_1906_, lean_object* v_b_1907_){
_start:
{
lean_object* v___x_1908_; 
v___x_1908_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15___redArg(v_m_1905_, v_a_1906_, v_b_1907_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8(lean_object* v_00_u03b2_1909_, lean_object* v_keys_1910_, lean_object* v_vals_1911_, lean_object* v_heq_1912_, lean_object* v_i_1913_, lean_object* v_k_1914_){
_start:
{
lean_object* v___x_1915_; 
v___x_1915_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8___redArg(v_keys_1910_, v_vals_1911_, v_i_1913_, v_k_1914_);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1916_, lean_object* v_keys_1917_, lean_object* v_vals_1918_, lean_object* v_heq_1919_, lean_object* v_i_1920_, lean_object* v_k_1921_){
_start:
{
lean_object* v_res_1922_; 
v_res_1922_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8(v_00_u03b2_1916_, v_keys_1917_, v_vals_1918_, v_heq_1919_, v_i_1920_, v_k_1921_);
lean_dec(v_k_1921_);
lean_dec_ref(v_vals_1918_);
lean_dec_ref(v_keys_1917_);
return v_res_1922_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13_spec__16(lean_object* v_00_u03b2_1923_, lean_object* v_keys_1924_, lean_object* v_vals_1925_, lean_object* v_heq_1926_, lean_object* v_i_1927_, lean_object* v_k_1928_){
_start:
{
uint8_t v___x_1929_; 
v___x_1929_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13_spec__16___redArg(v_keys_1924_, v_i_1927_, v_k_1928_);
return v___x_1929_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13_spec__16___boxed(lean_object* v_00_u03b2_1930_, lean_object* v_keys_1931_, lean_object* v_vals_1932_, lean_object* v_heq_1933_, lean_object* v_i_1934_, lean_object* v_k_1935_){
_start:
{
uint8_t v_res_1936_; lean_object* v_r_1937_; 
v_res_1936_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13_spec__16(v_00_u03b2_1930_, v_keys_1931_, v_vals_1932_, v_heq_1933_, v_i_1934_, v_k_1935_);
lean_dec(v_k_1935_);
lean_dec_ref(v_vals_1932_);
lean_dec_ref(v_keys_1931_);
v_r_1937_ = lean_box(v_res_1936_);
return v_r_1937_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19(lean_object* v_00_u03b2_1938_, lean_object* v_data_1939_){
_start:
{
lean_object* v___x_1940_; 
v___x_1940_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19___redArg(v_data_1939_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__20(lean_object* v_00_u03b2_1941_, lean_object* v_a_1942_, lean_object* v_b_1943_, lean_object* v_x_1944_){
_start:
{
lean_object* v___x_1945_; 
v___x_1945_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__20___redArg(v_a_1942_, v_b_1943_, v_x_1944_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19(lean_object* v_msgData_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
lean_object* v___x_1950_; 
v___x_1950_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg(v_msgData_1946_, v___y_1948_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___boxed(lean_object* v_msgData_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19(v_msgData_1951_, v___y_1952_, v___y_1953_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19_spec__21(lean_object* v_00_u03b2_1956_, lean_object* v_i_1957_, lean_object* v_source_1958_, lean_object* v_target_1959_){
_start:
{
lean_object* v___x_1960_; 
v___x_1960_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19_spec__21___redArg(v_i_1957_, v_source_1958_, v_target_1959_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19_spec__21_spec__25(lean_object* v_00_u03b2_1961_, lean_object* v_x_1962_, lean_object* v_x_1963_){
_start:
{
lean_object* v___x_1964_; 
v___x_1964_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19_spec__21_spec__25___redArg(v_x_1962_, v_x_1963_);
return v___x_1964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_1366347041____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1966_; lean_object* v___x_1967_; 
v___x_1966_ = ((lean_object*)(l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter));
v___x_1967_ = l_Lean_Elab_Command_addLinter(v___x_1966_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_1366347041____hygCtx___hyg_2____boxed(lean_object* v_a_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_1366347041____hygCtx___hyg_2_();
return v_res_1969_;
}
}
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Init_Try(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_Extra_UnreachableTactic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
