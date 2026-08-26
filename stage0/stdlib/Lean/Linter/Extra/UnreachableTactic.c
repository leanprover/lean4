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
extern lean_object* l_Lean_Parser_ParserExtension_instInhabitedState_default;
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
extern lean_object* l_Lean_Parser_parserExtension;
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameHashSet_insert(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_75_, lean_object* v_x_76_){
_start:
{
if (lean_obj_tag(v_x_76_) == 0)
{
return v_x_75_;
}
else
{
lean_object* v_key_77_; lean_object* v_value_78_; lean_object* v_tail_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_105_; 
v_key_77_ = lean_ctor_get(v_x_76_, 0);
v_value_78_ = lean_ctor_get(v_x_76_, 1);
v_tail_79_ = lean_ctor_get(v_x_76_, 2);
v_isSharedCheck_105_ = !lean_is_exclusive(v_x_76_);
if (v_isSharedCheck_105_ == 0)
{
v___x_81_ = v_x_76_;
v_isShared_82_ = v_isSharedCheck_105_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_tail_79_);
lean_inc(v_value_78_);
lean_inc(v_key_77_);
lean_dec(v_x_76_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_105_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_83_; uint64_t v___y_85_; 
v___x_83_ = lean_array_get_size(v_x_75_);
if (lean_obj_tag(v_key_77_) == 0)
{
uint64_t v___x_103_; 
v___x_103_ = 1723ULL;
v___y_85_ = v___x_103_;
goto v___jp_84_;
}
else
{
uint64_t v_hash_104_; 
v_hash_104_ = lean_ctor_get_uint64(v_key_77_, sizeof(void*)*2);
v___y_85_ = v_hash_104_;
goto v___jp_84_;
}
v___jp_84_:
{
uint64_t v___x_86_; uint64_t v___x_87_; uint64_t v_fold_88_; uint64_t v___x_89_; uint64_t v___x_90_; uint64_t v___x_91_; size_t v___x_92_; size_t v___x_93_; size_t v___x_94_; size_t v___x_95_; size_t v___x_96_; lean_object* v___x_97_; lean_object* v___x_99_; 
v___x_86_ = 32ULL;
v___x_87_ = lean_uint64_shift_right(v___y_85_, v___x_86_);
v_fold_88_ = lean_uint64_xor(v___y_85_, v___x_87_);
v___x_89_ = 16ULL;
v___x_90_ = lean_uint64_shift_right(v_fold_88_, v___x_89_);
v___x_91_ = lean_uint64_xor(v_fold_88_, v___x_90_);
v___x_92_ = lean_uint64_to_usize(v___x_91_);
v___x_93_ = lean_usize_of_nat(v___x_83_);
v___x_94_ = ((size_t)1ULL);
v___x_95_ = lean_usize_sub(v___x_93_, v___x_94_);
v___x_96_ = lean_usize_land(v___x_92_, v___x_95_);
v___x_97_ = lean_array_uget_borrowed(v_x_75_, v___x_96_);
lean_inc(v___x_97_);
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 2, v___x_97_);
v___x_99_ = v___x_81_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_key_77_);
lean_ctor_set(v_reuseFailAlloc_102_, 1, v_value_78_);
lean_ctor_set(v_reuseFailAlloc_102_, 2, v___x_97_);
v___x_99_ = v_reuseFailAlloc_102_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
lean_object* v___x_100_; 
v___x_100_ = lean_array_uset(v_x_75_, v___x_96_, v___x_99_);
v_x_75_ = v___x_100_;
v_x_76_ = v_tail_79_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(lean_object* v_i_106_, lean_object* v_source_107_, lean_object* v_target_108_){
_start:
{
lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_109_ = lean_array_get_size(v_source_107_);
v___x_110_ = lean_nat_dec_lt(v_i_106_, v___x_109_);
if (v___x_110_ == 0)
{
lean_dec_ref(v_source_107_);
lean_dec(v_i_106_);
return v_target_108_;
}
else
{
lean_object* v_es_111_; lean_object* v___x_112_; lean_object* v_source_113_; lean_object* v_target_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v_es_111_ = lean_array_fget(v_source_107_, v_i_106_);
v___x_112_ = lean_box(0);
v_source_113_ = lean_array_fset(v_source_107_, v_i_106_, v___x_112_);
v_target_114_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg(v_target_108_, v_es_111_);
v___x_115_ = lean_unsigned_to_nat(1u);
v___x_116_ = lean_nat_add(v_i_106_, v___x_115_);
lean_dec(v_i_106_);
v_i_106_ = v___x_116_;
v_source_107_ = v_source_113_;
v_target_108_ = v_target_114_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_data_118_){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v_nbuckets_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_119_ = lean_array_get_size(v_data_118_);
v___x_120_ = lean_unsigned_to_nat(2u);
v_nbuckets_121_ = lean_nat_mul(v___x_119_, v___x_120_);
v___x_122_ = lean_unsigned_to_nat(0u);
v___x_123_ = lean_box(0);
v___x_124_ = lean_mk_array(v_nbuckets_121_, v___x_123_);
v___x_125_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v___x_122_, v_data_118_, v___x_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(lean_object* v_m_126_, lean_object* v_a_127_, lean_object* v_b_128_){
_start:
{
lean_object* v_size_129_; lean_object* v_buckets_130_; lean_object* v___x_131_; uint64_t v___y_133_; 
v_size_129_ = lean_ctor_get(v_m_126_, 0);
v_buckets_130_ = lean_ctor_get(v_m_126_, 1);
v___x_131_ = lean_array_get_size(v_buckets_130_);
if (lean_obj_tag(v_a_127_) == 0)
{
uint64_t v___x_170_; 
v___x_170_ = 1723ULL;
v___y_133_ = v___x_170_;
goto v___jp_132_;
}
else
{
uint64_t v_hash_171_; 
v_hash_171_ = lean_ctor_get_uint64(v_a_127_, sizeof(void*)*2);
v___y_133_ = v_hash_171_;
goto v___jp_132_;
}
v___jp_132_:
{
uint64_t v___x_134_; uint64_t v___x_135_; uint64_t v_fold_136_; uint64_t v___x_137_; uint64_t v___x_138_; uint64_t v___x_139_; size_t v___x_140_; size_t v___x_141_; size_t v___x_142_; size_t v___x_143_; size_t v___x_144_; lean_object* v_bkt_145_; uint8_t v___x_146_; 
v___x_134_ = 32ULL;
v___x_135_ = lean_uint64_shift_right(v___y_133_, v___x_134_);
v_fold_136_ = lean_uint64_xor(v___y_133_, v___x_135_);
v___x_137_ = 16ULL;
v___x_138_ = lean_uint64_shift_right(v_fold_136_, v___x_137_);
v___x_139_ = lean_uint64_xor(v_fold_136_, v___x_138_);
v___x_140_ = lean_uint64_to_usize(v___x_139_);
v___x_141_ = lean_usize_of_nat(v___x_131_);
v___x_142_ = ((size_t)1ULL);
v___x_143_ = lean_usize_sub(v___x_141_, v___x_142_);
v___x_144_ = lean_usize_land(v___x_140_, v___x_143_);
v_bkt_145_ = lean_array_uget_borrowed(v_buckets_130_, v___x_144_);
v___x_146_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_127_, v_bkt_145_);
if (v___x_146_ == 0)
{
lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_167_; 
lean_inc_ref(v_buckets_130_);
lean_inc(v_size_129_);
v_isSharedCheck_167_ = !lean_is_exclusive(v_m_126_);
if (v_isSharedCheck_167_ == 0)
{
lean_object* v_unused_168_; lean_object* v_unused_169_; 
v_unused_168_ = lean_ctor_get(v_m_126_, 1);
lean_dec(v_unused_168_);
v_unused_169_ = lean_ctor_get(v_m_126_, 0);
lean_dec(v_unused_169_);
v___x_148_ = v_m_126_;
v_isShared_149_ = v_isSharedCheck_167_;
goto v_resetjp_147_;
}
else
{
lean_dec(v_m_126_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_167_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_150_; lean_object* v_size_x27_151_; lean_object* v___x_152_; lean_object* v_buckets_x27_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; 
v___x_150_ = lean_unsigned_to_nat(1u);
v_size_x27_151_ = lean_nat_add(v_size_129_, v___x_150_);
lean_dec(v_size_129_);
lean_inc(v_bkt_145_);
v___x_152_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_152_, 0, v_a_127_);
lean_ctor_set(v___x_152_, 1, v_b_128_);
lean_ctor_set(v___x_152_, 2, v_bkt_145_);
v_buckets_x27_153_ = lean_array_uset(v_buckets_130_, v___x_144_, v___x_152_);
v___x_154_ = lean_unsigned_to_nat(4u);
v___x_155_ = lean_nat_mul(v_size_x27_151_, v___x_154_);
v___x_156_ = lean_unsigned_to_nat(3u);
v___x_157_ = lean_nat_div(v___x_155_, v___x_156_);
lean_dec(v___x_155_);
v___x_158_ = lean_array_get_size(v_buckets_x27_153_);
v___x_159_ = lean_nat_dec_le(v___x_157_, v___x_158_);
lean_dec(v___x_157_);
if (v___x_159_ == 0)
{
lean_object* v_val_160_; lean_object* v___x_162_; 
v_val_160_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1___redArg(v_buckets_x27_153_);
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 1, v_val_160_);
lean_ctor_set(v___x_148_, 0, v_size_x27_151_);
v___x_162_ = v___x_148_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_size_x27_151_);
lean_ctor_set(v_reuseFailAlloc_163_, 1, v_val_160_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
else
{
lean_object* v___x_165_; 
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 1, v_buckets_x27_153_);
lean_ctor_set(v___x_148_, 0, v_size_x27_151_);
v___x_165_ = v___x_148_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_size_x27_151_);
lean_ctor_set(v_reuseFailAlloc_166_, 1, v_buckets_x27_153_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
}
else
{
lean_dec(v_b_128_);
lean_dec(v_a_127_);
return v_m_126_;
}
}
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__0_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_172_ = lean_box(0);
v___x_173_ = lean_unsigned_to_nat(16u);
v___x_174_ = lean_mk_array(v___x_173_, v___x_172_);
return v___x_174_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__1_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_175_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__0_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__0_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__0_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
v___x_176_ = lean_unsigned_to_nat(0u);
v___x_177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
lean_ctor_set(v___x_177_, 1, v___x_175_);
return v___x_177_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_186_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__5_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_));
v___x_187_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__1_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__1_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__1_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
v___x_188_ = l_Lean_NameHashSet_insert(v___x_187_, v___x_186_);
return v___x_188_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_195_ = lean_box(0);
v___x_196_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__8_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_));
v___x_197_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
v___x_198_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___x_197_, v___x_196_, v___x_195_);
return v___x_198_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__13_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_206_ = lean_box(0);
v___x_207_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__12_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_));
v___x_208_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
v___x_209_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___x_208_, v___x_207_, v___x_206_);
return v___x_209_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__16_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_216_ = lean_box(0);
v___x_217_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__15_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_));
v___x_218_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__13_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__13_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__13_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
v___x_219_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___x_218_, v___x_217_, v___x_216_);
return v___x_219_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__20_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_227_ = lean_box(0);
v___x_228_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__19_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_));
v___x_229_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__16_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__16_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__16_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
v___x_230_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___x_229_, v___x_228_, v___x_227_);
return v___x_230_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__23_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_237_ = lean_box(0);
v___x_238_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__22_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_));
v___x_239_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__20_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__20_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__20_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
v___x_240_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___x_239_, v___x_238_, v___x_237_);
return v___x_240_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__26_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_247_ = lean_box(0);
v___x_248_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__25_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_));
v___x_249_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__23_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__23_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__23_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
v___x_250_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___x_249_, v___x_248_, v___x_247_);
return v___x_250_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__29_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_257_ = lean_box(0);
v___x_258_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__28_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_));
v___x_259_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__26_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__26_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__26_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
v___x_260_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___x_259_, v___x_258_, v___x_257_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_262_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__29_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__29_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__29_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
v___x_263_ = lean_st_mk_ref(v___x_262_);
v___x_264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2____boxed(lean_object* v_a_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_();
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_267_, lean_object* v_m_268_, lean_object* v_a_269_, lean_object* v_b_270_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v_m_268_, v_a_269_, v_b_270_);
return v___x_271_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_272_, lean_object* v_a_273_, lean_object* v_x_274_){
_start:
{
uint8_t v___x_275_; 
v___x_275_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_273_, v_x_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_276_, lean_object* v_a_277_, lean_object* v_x_278_){
_start:
{
uint8_t v_res_279_; lean_object* v_r_280_; 
v_res_279_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_276_, v_a_277_, v_x_278_);
lean_dec(v_x_278_);
lean_dec(v_a_277_);
v_r_280_ = lean_box(v_res_279_);
return v_r_280_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_00_u03b2_281_, lean_object* v_data_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1___redArg(v_data_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2(lean_object* v_00_u03b2_284_, lean_object* v_i_285_, lean_object* v_source_286_, lean_object* v_target_287_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v_i_285_, v_source_286_, v_target_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_289_, lean_object* v_x_290_, lean_object* v_x_291_){
_start:
{
lean_object* v___x_292_; 
v___x_292_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg(v_x_290_, v_x_291_);
return v___x_292_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_Extra_UnreachableTactic_isIgnoreTacticKind(lean_object* v_ignoreTacticKinds_294_, lean_object* v_k_295_){
_start:
{
if (lean_obj_tag(v_k_295_) == 1)
{
lean_object* v_str_296_; lean_object* v___x_297_; uint8_t v___x_298_; 
v_str_296_ = lean_ctor_get(v_k_295_, 1);
v___x_297_ = ((lean_object*)(l_Lean_Linter_Extra_UnreachableTactic_isIgnoreTacticKind___closed__0));
v___x_298_ = lean_string_dec_eq(v_str_296_, v___x_297_);
if (v___x_298_ == 0)
{
uint8_t v___x_299_; 
v___x_299_ = l_Lean_NameHashSet_contains(v_ignoreTacticKinds_294_, v_k_295_);
return v___x_299_;
}
else
{
return v___x_298_;
}
}
else
{
uint8_t v___x_300_; 
v___x_300_ = l_Lean_NameHashSet_contains(v_ignoreTacticKinds_294_, v_k_295_);
return v___x_300_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_isIgnoreTacticKind___boxed(lean_object* v_ignoreTacticKinds_301_, lean_object* v_k_302_){
_start:
{
uint8_t v_res_303_; lean_object* v_r_304_; 
v_res_303_ = l_Lean_Linter_Extra_UnreachableTactic_isIgnoreTacticKind(v_ignoreTacticKinds_301_, v_k_302_);
lean_dec(v_k_302_);
lean_dec_ref(v_ignoreTacticKinds_301_);
v_r_304_ = lean_box(v_res_303_);
return v_r_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_addIgnoreTacticKind(lean_object* v_kind_305_){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_307_ = l_Lean_Linter_Extra_UnreachableTactic_ignoreTacticKindsRef;
v___x_308_ = lean_st_ref_take(v___x_307_);
v___x_309_ = l_Lean_NameHashSet_insert(v___x_308_, v_kind_305_);
v___x_310_ = lean_st_ref_put(v___x_307_, v___x_309_);
v___x_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_addIgnoreTacticKind___boxed(lean_object* v_kind_312_, lean_object* v_a_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Lean_Linter_Extra_UnreachableTactic_addIgnoreTacticKind(v_kind_312_);
return v_res_314_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__0(void){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_instMonadEIO(lean_box(0));
return v___x_315_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__1(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = lean_obj_once(&l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__0, &l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__0_once, _init_l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__0);
v___x_317_ = l_StateRefT_x27_instMonad___redArg(v___x_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_getTactics___lam__0___boxed(lean_object* v_ignoreTacticKinds_320_, lean_object* v_isTacKind_321_, lean_object* v_x_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Lean_Linter_Extra_UnreachableTactic_getTactics___lam__0(v_ignoreTacticKinds_320_, v_isTacKind_321_, v_x_322_, v___y_323_, v___y_324_);
lean_dec(v___y_324_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_getTactics(lean_object* v_ignoreTacticKinds_327_, lean_object* v_isTacKind_328_, lean_object* v_stx_329_, lean_object* v_a_330_){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = lean_obj_once(&l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__1, &l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__1_once, _init_l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__1);
if (lean_obj_tag(v_stx_329_) == 1)
{
lean_object* v_kind_333_; lean_object* v_args_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___y_338_; lean_object* v___y_360_; uint8_t v___x_361_; 
v_kind_333_ = lean_ctor_get(v_stx_329_, 1);
v_args_334_ = lean_ctor_get(v_stx_329_, 2);
v___x_335_ = ((lean_object*)(l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__2));
v___x_336_ = ((lean_object*)(l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__3));
v___x_361_ = l_Lean_Linter_Extra_UnreachableTactic_isIgnoreTacticKind(v_ignoreTacticKinds_327_, v_kind_333_);
if (v___x_361_ == 0)
{
lean_object* v___x_362_; lean_object* v___x_363_; uint8_t v___x_364_; 
v___x_362_ = lean_unsigned_to_nat(0u);
v___x_363_ = lean_array_get_size(v_args_334_);
v___x_364_ = lean_nat_dec_lt(v___x_362_, v___x_363_);
if (v___x_364_ == 0)
{
lean_dec_ref(v_ignoreTacticKinds_327_);
v___y_338_ = v_a_330_;
goto v___jp_337_;
}
else
{
lean_object* v___f_365_; lean_object* v___x_366_; uint8_t v___x_367_; 
lean_inc_ref(v_isTacKind_328_);
v___f_365_ = lean_alloc_closure((void*)(l_Lean_Linter_Extra_UnreachableTactic_getTactics___lam__0___boxed), 6, 2);
lean_closure_set(v___f_365_, 0, v_ignoreTacticKinds_327_);
lean_closure_set(v___f_365_, 1, v_isTacKind_328_);
v___x_366_ = lean_box(0);
v___x_367_ = lean_nat_dec_le(v___x_363_, v___x_363_);
if (v___x_367_ == 0)
{
if (v___x_364_ == 0)
{
lean_dec_ref(v___f_365_);
v___y_338_ = v_a_330_;
goto v___jp_337_;
}
else
{
size_t v___x_368_; size_t v___x_369_; lean_object* v___x_968__overap_370_; lean_object* v___x_371_; 
v___x_368_ = ((size_t)0ULL);
v___x_369_ = lean_usize_of_nat(v___x_363_);
lean_inc_ref(v_args_334_);
v___x_968__overap_370_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_332_, v___f_365_, v_args_334_, v___x_368_, v___x_369_, v___x_366_);
lean_inc(v_a_330_);
v___x_371_ = lean_apply_2(v___x_968__overap_370_, v_a_330_, lean_box(0));
v___y_360_ = v___x_371_;
goto v___jp_359_;
}
}
else
{
size_t v___x_372_; size_t v___x_373_; lean_object* v___x_971__overap_374_; lean_object* v___x_375_; 
v___x_372_ = ((size_t)0ULL);
v___x_373_ = lean_usize_of_nat(v___x_363_);
lean_inc_ref(v_args_334_);
v___x_971__overap_374_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_332_, v___f_365_, v_args_334_, v___x_372_, v___x_373_, v___x_366_);
lean_inc(v_a_330_);
v___x_375_ = lean_apply_2(v___x_971__overap_374_, v_a_330_, lean_box(0));
v___y_360_ = v___x_375_;
goto v___jp_359_;
}
}
}
else
{
lean_dec_ref(v_ignoreTacticKinds_327_);
v___y_338_ = v_a_330_;
goto v___jp_337_;
}
v___jp_337_:
{
lean_object* v___x_339_; uint8_t v___x_340_; 
lean_inc(v_kind_333_);
v___x_339_ = lean_apply_1(v_isTacKind_328_, v_kind_333_);
v___x_340_ = lean_unbox(v___x_339_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; lean_object* v___x_342_; 
lean_dec_ref_known(v_stx_329_, 3);
v___x_341_ = lean_box(0);
v___x_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
return v___x_342_;
}
else
{
uint8_t v___x_343_; lean_object* v___x_344_; 
v___x_343_ = lean_unbox(v___x_339_);
v___x_344_ = l_Lean_Syntax_getRange_x3f(v_stx_329_, v___x_343_);
if (lean_obj_tag(v___x_344_) == 1)
{
lean_object* v_val_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_356_; 
v_val_345_ = lean_ctor_get(v___x_344_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_356_ == 0)
{
v___x_347_ = v___x_344_;
v_isShared_348_ = v_isSharedCheck_356_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_val_345_);
lean_dec(v___x_344_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_356_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_349_ = lean_st_ref_take(v___y_338_);
v___x_350_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_335_, v___x_336_, v___x_349_, v_val_345_, v_stx_329_);
v___x_351_ = lean_st_ref_put(v___y_338_, v___x_350_);
v___x_352_ = lean_box(0);
if (v_isShared_348_ == 0)
{
lean_ctor_set_tag(v___x_347_, 0);
lean_ctor_set(v___x_347_, 0, v___x_352_);
v___x_354_ = v___x_347_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v___x_352_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
else
{
lean_object* v___x_357_; lean_object* v___x_358_; 
lean_dec(v___x_344_);
lean_dec_ref_known(v_stx_329_, 3);
v___x_357_ = lean_box(0);
v___x_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
return v___x_358_;
}
}
}
v___jp_359_:
{
if (lean_obj_tag(v___y_360_) == 0)
{
lean_dec_ref_known(v___y_360_, 1);
v___y_338_ = v_a_330_;
goto v___jp_337_;
}
else
{
lean_dec_ref_known(v_stx_329_, 3);
lean_dec_ref(v_isTacKind_328_);
return v___y_360_;
}
}
}
else
{
lean_object* v___x_376_; lean_object* v___x_377_; 
lean_dec(v_stx_329_);
lean_dec_ref(v_isTacKind_328_);
lean_dec_ref(v_ignoreTacticKinds_327_);
v___x_376_ = lean_box(0);
v___x_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
return v___x_377_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_getTactics___lam__0(lean_object* v_ignoreTacticKinds_378_, lean_object* v_isTacKind_379_, lean_object* v_x_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l_Lean_Linter_Extra_UnreachableTactic_getTactics(v_ignoreTacticKinds_378_, v_isTacKind_379_, v___y_381_, v___y_382_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_getTactics___boxed(lean_object* v_ignoreTacticKinds_385_, lean_object* v_isTacKind_386_, lean_object* v_stx_387_, lean_object* v_a_388_, lean_object* v_a_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_Linter_Extra_UnreachableTactic_getTactics(v_ignoreTacticKinds_385_, v_isTacKind_386_, v_stx_387_, v_a_388_);
lean_dec(v_a_388_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__6___redArg(lean_object* v_a_391_, lean_object* v_x_392_){
_start:
{
if (lean_obj_tag(v_x_392_) == 0)
{
return v_x_392_;
}
else
{
lean_object* v_key_393_; lean_object* v_value_394_; lean_object* v_tail_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_404_; 
v_key_393_ = lean_ctor_get(v_x_392_, 0);
v_value_394_ = lean_ctor_get(v_x_392_, 1);
v_tail_395_ = lean_ctor_get(v_x_392_, 2);
v_isSharedCheck_404_ = !lean_is_exclusive(v_x_392_);
if (v_isSharedCheck_404_ == 0)
{
v___x_397_ = v_x_392_;
v_isShared_398_ = v_isSharedCheck_404_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_tail_395_);
lean_inc(v_value_394_);
lean_inc(v_key_393_);
lean_dec(v_x_392_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_404_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
uint8_t v___x_399_; 
v___x_399_ = l_Lean_Syntax_instBEqRange_beq(v_key_393_, v_a_391_);
if (v___x_399_ == 0)
{
lean_object* v___x_400_; lean_object* v___x_402_; 
v___x_400_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__6___redArg(v_a_391_, v_tail_395_);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 2, v___x_400_);
v___x_402_ = v___x_397_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_key_393_);
lean_ctor_set(v_reuseFailAlloc_403_, 1, v_value_394_);
lean_ctor_set(v_reuseFailAlloc_403_, 2, v___x_400_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
else
{
lean_del_object(v___x_397_);
lean_dec(v_value_394_);
lean_dec(v_key_393_);
return v_tail_395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__6___redArg___boxed(lean_object* v_a_405_, lean_object* v_x_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__6___redArg(v_a_405_, v_x_406_);
lean_dec_ref(v_a_405_);
return v_res_407_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5___redArg(lean_object* v_a_408_, lean_object* v_x_409_){
_start:
{
if (lean_obj_tag(v_x_409_) == 0)
{
uint8_t v___x_410_; 
v___x_410_ = 0;
return v___x_410_;
}
else
{
lean_object* v_key_411_; lean_object* v_tail_412_; uint8_t v___x_413_; 
v_key_411_ = lean_ctor_get(v_x_409_, 0);
v_tail_412_ = lean_ctor_get(v_x_409_, 2);
v___x_413_ = l_Lean_Syntax_instBEqRange_beq(v_key_411_, v_a_408_);
if (v___x_413_ == 0)
{
v_x_409_ = v_tail_412_;
goto _start;
}
else
{
return v___x_413_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5___redArg___boxed(lean_object* v_a_415_, lean_object* v_x_416_){
_start:
{
uint8_t v_res_417_; lean_object* v_r_418_; 
v_res_417_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5___redArg(v_a_415_, v_x_416_);
lean_dec(v_x_416_);
lean_dec_ref(v_a_415_);
v_r_418_ = lean_box(v_res_417_);
return v_r_418_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2___redArg(lean_object* v_m_419_, lean_object* v_a_420_){
_start:
{
lean_object* v_size_421_; lean_object* v_buckets_422_; lean_object* v___x_423_; uint64_t v___x_424_; uint64_t v___x_425_; uint64_t v___x_426_; uint64_t v_fold_427_; uint64_t v___x_428_; uint64_t v___x_429_; uint64_t v___x_430_; size_t v___x_431_; size_t v___x_432_; size_t v___x_433_; size_t v___x_434_; size_t v___x_435_; lean_object* v_bkt_436_; uint8_t v___x_437_; 
v_size_421_ = lean_ctor_get(v_m_419_, 0);
v_buckets_422_ = lean_ctor_get(v_m_419_, 1);
v___x_423_ = lean_array_get_size(v_buckets_422_);
v___x_424_ = l_Lean_Syntax_instHashableRange_hash(v_a_420_);
v___x_425_ = 32ULL;
v___x_426_ = lean_uint64_shift_right(v___x_424_, v___x_425_);
v_fold_427_ = lean_uint64_xor(v___x_424_, v___x_426_);
v___x_428_ = 16ULL;
v___x_429_ = lean_uint64_shift_right(v_fold_427_, v___x_428_);
v___x_430_ = lean_uint64_xor(v_fold_427_, v___x_429_);
v___x_431_ = lean_uint64_to_usize(v___x_430_);
v___x_432_ = lean_usize_of_nat(v___x_423_);
v___x_433_ = ((size_t)1ULL);
v___x_434_ = lean_usize_sub(v___x_432_, v___x_433_);
v___x_435_ = lean_usize_land(v___x_431_, v___x_434_);
v_bkt_436_ = lean_array_uget_borrowed(v_buckets_422_, v___x_435_);
v___x_437_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5___redArg(v_a_420_, v_bkt_436_);
if (v___x_437_ == 0)
{
return v_m_419_;
}
else
{
lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_450_; 
lean_inc(v_bkt_436_);
lean_inc_ref(v_buckets_422_);
lean_inc(v_size_421_);
v_isSharedCheck_450_ = !lean_is_exclusive(v_m_419_);
if (v_isSharedCheck_450_ == 0)
{
lean_object* v_unused_451_; lean_object* v_unused_452_; 
v_unused_451_ = lean_ctor_get(v_m_419_, 1);
lean_dec(v_unused_451_);
v_unused_452_ = lean_ctor_get(v_m_419_, 0);
lean_dec(v_unused_452_);
v___x_439_ = v_m_419_;
v_isShared_440_ = v_isSharedCheck_450_;
goto v_resetjp_438_;
}
else
{
lean_dec(v_m_419_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_450_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_441_; lean_object* v_buckets_x27_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_448_; 
v___x_441_ = lean_box(0);
v_buckets_x27_442_ = lean_array_uset(v_buckets_422_, v___x_435_, v___x_441_);
v___x_443_ = lean_unsigned_to_nat(1u);
v___x_444_ = lean_nat_sub(v_size_421_, v___x_443_);
lean_dec(v_size_421_);
v___x_445_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__6___redArg(v_a_420_, v_bkt_436_);
v___x_446_ = lean_array_uset(v_buckets_x27_442_, v___x_435_, v___x_445_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 1, v___x_446_);
lean_ctor_set(v___x_439_, 0, v___x_444_);
v___x_448_ = v___x_439_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_444_);
lean_ctor_set(v_reuseFailAlloc_449_, 1, v___x_446_);
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
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2___redArg___boxed(lean_object* v_m_453_, lean_object* v_a_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2___redArg(v_m_453_, v_a_454_);
lean_dec_ref(v_a_454_);
return v_res_455_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics(lean_object* v_x_457_, lean_object* v_a_458_){
_start:
{
switch(lean_obj_tag(v_x_457_))
{
case 0:
{
lean_object* v_t_460_; 
v_t_460_ = lean_ctor_get(v_x_457_, 1);
lean_inc_ref(v_t_460_);
lean_dec_ref_known(v_x_457_, 2);
v_x_457_ = v_t_460_;
goto _start;
}
case 1:
{
lean_object* v_i_462_; 
v_i_462_ = lean_ctor_get(v_x_457_, 0);
if (lean_obj_tag(v_i_462_) == 0)
{
lean_object* v_i_463_; lean_object* v_toElabInfo_464_; lean_object* v_children_465_; lean_object* v_stx_466_; uint8_t v___x_467_; lean_object* v___x_468_; 
v_i_463_ = lean_ctor_get(v_i_462_, 0);
v_toElabInfo_464_ = lean_ctor_get(v_i_463_, 0);
lean_inc_ref(v_toElabInfo_464_);
v_children_465_ = lean_ctor_get(v_x_457_, 1);
lean_inc_ref(v_children_465_);
lean_dec_ref_known(v_x_457_, 2);
v_stx_466_ = lean_ctor_get(v_toElabInfo_464_, 1);
lean_inc(v_stx_466_);
lean_dec_ref(v_toElabInfo_464_);
v___x_467_ = 1;
v___x_468_ = l_Lean_Syntax_getRange_x3f(v_stx_466_, v___x_467_);
lean_dec(v_stx_466_);
if (lean_obj_tag(v___x_468_) == 1)
{
lean_object* v_val_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v_val_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc(v_val_469_);
lean_dec_ref_known(v___x_468_, 1);
v___x_470_ = lean_st_ref_take(v_a_458_);
v___x_471_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2___redArg(v___x_470_, v_val_469_);
lean_dec(v_val_469_);
v___x_472_ = lean_st_ref_put(v_a_458_, v___x_471_);
v___x_473_ = l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList(v_children_465_, v_a_458_);
return v___x_473_;
}
else
{
lean_object* v___x_474_; 
lean_dec(v___x_468_);
v___x_474_ = l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList(v_children_465_, v_a_458_);
return v___x_474_;
}
}
else
{
lean_object* v_children_475_; lean_object* v___x_476_; 
v_children_475_ = lean_ctor_get(v_x_457_, 1);
lean_inc_ref(v_children_475_);
lean_dec_ref_known(v_x_457_, 2);
v___x_476_ = l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList(v_children_475_, v_a_458_);
return v___x_476_;
}
}
default: 
{
lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_484_; 
v_isSharedCheck_484_ = !lean_is_exclusive(v_x_457_);
if (v_isSharedCheck_484_ == 0)
{
lean_object* v_unused_485_; 
v_unused_485_ = lean_ctor_get(v_x_457_, 0);
lean_dec(v_unused_485_);
v___x_478_ = v_x_457_;
v_isShared_479_ = v_isSharedCheck_484_;
goto v_resetjp_477_;
}
else
{
lean_dec(v_x_457_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_484_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_480_; lean_object* v___x_482_; 
v___x_480_ = lean_box(0);
if (v_isShared_479_ == 0)
{
lean_ctor_set_tag(v___x_478_, 0);
lean_ctor_set(v___x_478_, 0, v___x_480_);
v___x_482_ = v___x_478_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v___x_480_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(lean_object* v_as_486_, size_t v_i_487_, size_t v_stop_488_, lean_object* v_b_489_, lean_object* v___y_490_){
_start:
{
uint8_t v___x_492_; 
v___x_492_ = lean_usize_dec_eq(v_i_487_, v_stop_488_);
if (v___x_492_ == 0)
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = lean_array_uget_borrowed(v_as_486_, v_i_487_);
lean_inc(v___x_493_);
v___x_494_ = l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics(v___x_493_, v___y_490_);
if (lean_obj_tag(v___x_494_) == 0)
{
lean_object* v_a_495_; size_t v___x_496_; size_t v___x_497_; 
v_a_495_ = lean_ctor_get(v___x_494_, 0);
lean_inc(v_a_495_);
lean_dec_ref_known(v___x_494_, 1);
v___x_496_ = ((size_t)1ULL);
v___x_497_ = lean_usize_add(v_i_487_, v___x_496_);
v_i_487_ = v___x_497_;
v_b_489_ = v_a_495_;
goto _start;
}
else
{
return v___x_494_;
}
}
else
{
lean_object* v___x_499_; 
v___x_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_499_, 0, v_b_489_);
return v___x_499_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__2(lean_object* v_x_500_, lean_object* v___y_501_){
_start:
{
if (lean_obj_tag(v_x_500_) == 0)
{
lean_object* v_cs_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_517_; 
v_cs_503_ = lean_ctor_get(v_x_500_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v_x_500_);
if (v_isSharedCheck_517_ == 0)
{
v___x_505_ = v_x_500_;
v_isShared_506_ = v_isSharedCheck_517_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_cs_503_);
lean_dec(v_x_500_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_517_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; uint8_t v___x_510_; 
v___x_507_ = lean_unsigned_to_nat(0u);
v___x_508_ = lean_array_get_size(v_cs_503_);
v___x_509_ = lean_box(0);
v___x_510_ = lean_nat_dec_lt(v___x_507_, v___x_508_);
if (v___x_510_ == 0)
{
lean_object* v___x_512_; 
lean_dec_ref(v_cs_503_);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 0, v___x_509_);
v___x_512_ = v___x_505_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v___x_509_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
else
{
size_t v___x_514_; size_t v___x_515_; lean_object* v___x_516_; 
lean_del_object(v___x_505_);
v___x_514_ = ((size_t)0ULL);
v___x_515_ = lean_usize_of_nat(v___x_508_);
v___x_516_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__3(v_cs_503_, v___x_514_, v___x_515_, v___x_509_, v___y_501_);
lean_dec_ref(v_cs_503_);
return v___x_516_;
}
}
}
else
{
lean_object* v_vs_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_532_; 
v_vs_518_ = lean_ctor_get(v_x_500_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v_x_500_);
if (v_isSharedCheck_532_ == 0)
{
v___x_520_ = v_x_500_;
v_isShared_521_ = v_isSharedCheck_532_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_vs_518_);
lean_dec(v_x_500_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_532_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; uint8_t v___x_525_; 
v___x_522_ = lean_unsigned_to_nat(0u);
v___x_523_ = lean_array_get_size(v_vs_518_);
v___x_524_ = lean_box(0);
v___x_525_ = lean_nat_dec_lt(v___x_522_, v___x_523_);
if (v___x_525_ == 0)
{
lean_object* v___x_527_; 
lean_dec_ref(v_vs_518_);
if (v_isShared_521_ == 0)
{
lean_ctor_set_tag(v___x_520_, 0);
lean_ctor_set(v___x_520_, 0, v___x_524_);
v___x_527_ = v___x_520_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_524_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
else
{
size_t v___x_529_; size_t v___x_530_; lean_object* v___x_531_; 
lean_del_object(v___x_520_);
v___x_529_ = ((size_t)0ULL);
v___x_530_ = lean_usize_of_nat(v___x_523_);
v___x_531_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(v_vs_518_, v___x_529_, v___x_530_, v___x_524_, v___y_501_);
lean_dec_ref(v_vs_518_);
return v___x_531_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__3(lean_object* v_as_533_, size_t v_i_534_, size_t v_stop_535_, lean_object* v_b_536_, lean_object* v___y_537_){
_start:
{
uint8_t v___x_539_; 
v___x_539_ = lean_usize_dec_eq(v_i_534_, v_stop_535_);
if (v___x_539_ == 0)
{
lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_540_ = lean_array_uget_borrowed(v_as_533_, v_i_534_);
lean_inc(v___x_540_);
v___x_541_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__2(v___x_540_, v___y_537_);
if (lean_obj_tag(v___x_541_) == 0)
{
lean_object* v_a_542_; size_t v___x_543_; size_t v___x_544_; 
v_a_542_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_a_542_);
lean_dec_ref_known(v___x_541_, 1);
v___x_543_ = ((size_t)1ULL);
v___x_544_ = lean_usize_add(v_i_534_, v___x_543_);
v_i_534_ = v___x_544_;
v_b_536_ = v_a_542_;
goto _start;
}
else
{
return v___x_541_;
}
}
else
{
lean_object* v___x_546_; 
v___x_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_546_, 0, v_b_536_);
return v___x_546_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0(lean_object* v_x_547_, size_t v_x_548_, size_t v_x_549_, lean_object* v___y_550_){
_start:
{
if (lean_obj_tag(v_x_547_) == 0)
{
lean_object* v_cs_552_; lean_object* v___x_553_; size_t v___x_554_; lean_object* v_j_555_; lean_object* v___x_556_; size_t v___x_557_; size_t v___x_558_; size_t v___x_559_; size_t v___x_560_; size_t v___x_561_; size_t v___x_562_; lean_object* v___x_563_; 
v_cs_552_ = lean_ctor_get(v_x_547_, 0);
lean_inc_ref(v_cs_552_);
lean_dec_ref_known(v_x_547_, 1);
v___x_553_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0___closed__0);
v___x_554_ = lean_usize_shift_right(v_x_548_, v_x_549_);
v_j_555_ = lean_usize_to_nat(v___x_554_);
v___x_556_ = lean_array_get_borrowed(v___x_553_, v_cs_552_, v_j_555_);
v___x_557_ = ((size_t)1ULL);
v___x_558_ = lean_usize_shift_left(v___x_557_, v_x_549_);
v___x_559_ = lean_usize_sub(v___x_558_, v___x_557_);
v___x_560_ = lean_usize_land(v_x_548_, v___x_559_);
v___x_561_ = ((size_t)5ULL);
v___x_562_ = lean_usize_sub(v_x_549_, v___x_561_);
lean_inc(v___x_556_);
v___x_563_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0(v___x_556_, v___x_560_, v___x_562_, v___y_550_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_578_; 
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_578_ == 0)
{
lean_object* v_unused_579_; 
v_unused_579_ = lean_ctor_get(v___x_563_, 0);
lean_dec(v_unused_579_);
v___x_565_ = v___x_563_;
v_isShared_566_ = v_isSharedCheck_578_;
goto v_resetjp_564_;
}
else
{
lean_dec(v___x_563_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_578_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; uint8_t v___x_571_; 
v___x_567_ = lean_unsigned_to_nat(1u);
v___x_568_ = lean_nat_add(v_j_555_, v___x_567_);
lean_dec(v_j_555_);
v___x_569_ = lean_array_get_size(v_cs_552_);
v___x_570_ = lean_box(0);
v___x_571_ = lean_nat_dec_lt(v___x_568_, v___x_569_);
if (v___x_571_ == 0)
{
lean_object* v___x_573_; 
lean_dec(v___x_568_);
lean_dec_ref(v_cs_552_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 0, v___x_570_);
v___x_573_ = v___x_565_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_570_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
else
{
size_t v___x_575_; size_t v___x_576_; lean_object* v___x_577_; 
lean_del_object(v___x_565_);
v___x_575_ = lean_usize_of_nat(v___x_568_);
lean_dec(v___x_568_);
v___x_576_ = lean_usize_of_nat(v___x_569_);
v___x_577_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__3(v_cs_552_, v___x_575_, v___x_576_, v___x_570_, v___y_550_);
lean_dec_ref(v_cs_552_);
return v___x_577_;
}
}
}
else
{
lean_dec(v_j_555_);
lean_dec_ref(v_cs_552_);
return v___x_563_;
}
}
else
{
lean_object* v_vs_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_594_; 
v_vs_580_ = lean_ctor_get(v_x_547_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v_x_547_);
if (v_isSharedCheck_594_ == 0)
{
v___x_582_ = v_x_547_;
v_isShared_583_ = v_isSharedCheck_594_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_vs_580_);
lean_dec(v_x_547_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_594_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; uint8_t v___x_587_; 
v___x_584_ = lean_usize_to_nat(v_x_548_);
v___x_585_ = lean_array_get_size(v_vs_580_);
v___x_586_ = lean_box(0);
v___x_587_ = lean_nat_dec_lt(v___x_584_, v___x_585_);
if (v___x_587_ == 0)
{
lean_object* v___x_589_; 
lean_dec(v___x_584_);
lean_dec_ref(v_vs_580_);
if (v_isShared_583_ == 0)
{
lean_ctor_set_tag(v___x_582_, 0);
lean_ctor_set(v___x_582_, 0, v___x_586_);
v___x_589_ = v___x_582_;
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
size_t v___x_591_; size_t v___x_592_; lean_object* v___x_593_; 
lean_del_object(v___x_582_);
v___x_591_ = lean_usize_of_nat(v___x_584_);
lean_dec(v___x_584_);
v___x_592_ = lean_usize_of_nat(v___x_585_);
v___x_593_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(v_vs_580_, v___x_591_, v___x_592_, v___x_586_, v___y_550_);
lean_dec_ref(v_vs_580_);
return v___x_593_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__2(lean_object* v_t_595_, lean_object* v___y_596_){
_start:
{
lean_object* v_root_598_; lean_object* v_tail_599_; lean_object* v___x_600_; 
v_root_598_ = lean_ctor_get(v_t_595_, 0);
lean_inc_ref(v_root_598_);
v_tail_599_ = lean_ctor_get(v_t_595_, 1);
lean_inc_ref(v_tail_599_);
lean_dec_ref(v_t_595_);
v___x_600_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__2(v_root_598_, v___y_596_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_614_; 
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_614_ == 0)
{
lean_object* v_unused_615_; 
v_unused_615_ = lean_ctor_get(v___x_600_, 0);
lean_dec(v_unused_615_);
v___x_602_ = v___x_600_;
v_isShared_603_ = v_isSharedCheck_614_;
goto v_resetjp_601_;
}
else
{
lean_dec(v___x_600_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_614_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; uint8_t v___x_607_; 
v___x_604_ = lean_unsigned_to_nat(0u);
v___x_605_ = lean_array_get_size(v_tail_599_);
v___x_606_ = lean_box(0);
v___x_607_ = lean_nat_dec_lt(v___x_604_, v___x_605_);
if (v___x_607_ == 0)
{
lean_object* v___x_609_; 
lean_dec_ref(v_tail_599_);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 0, v___x_606_);
v___x_609_ = v___x_602_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_606_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
else
{
size_t v___x_611_; size_t v___x_612_; lean_object* v___x_613_; 
lean_del_object(v___x_602_);
v___x_611_ = ((size_t)0ULL);
v___x_612_ = lean_usize_of_nat(v___x_605_);
v___x_613_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(v_tail_599_, v___x_611_, v___x_612_, v___x_606_, v___y_596_);
lean_dec_ref(v_tail_599_);
return v___x_613_;
}
}
}
else
{
lean_dec_ref(v_tail_599_);
return v___x_600_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0(lean_object* v_t_616_, lean_object* v_start_617_, lean_object* v___y_618_){
_start:
{
lean_object* v___x_620_; uint8_t v___x_621_; 
v___x_620_ = lean_unsigned_to_nat(0u);
v___x_621_ = lean_nat_dec_eq(v_start_617_, v___x_620_);
if (v___x_621_ == 0)
{
lean_object* v_root_622_; lean_object* v_tail_623_; size_t v_shift_624_; lean_object* v_tailOff_625_; uint8_t v___x_626_; 
v_root_622_ = lean_ctor_get(v_t_616_, 0);
lean_inc_ref(v_root_622_);
v_tail_623_ = lean_ctor_get(v_t_616_, 1);
lean_inc_ref(v_tail_623_);
v_shift_624_ = lean_ctor_get_usize(v_t_616_, 4);
v_tailOff_625_ = lean_ctor_get(v_t_616_, 3);
lean_inc(v_tailOff_625_);
lean_dec_ref(v_t_616_);
v___x_626_ = lean_nat_dec_le(v_tailOff_625_, v_start_617_);
if (v___x_626_ == 0)
{
size_t v___x_627_; lean_object* v___x_628_; 
lean_dec(v_tailOff_625_);
v___x_627_ = lean_usize_of_nat(v_start_617_);
v___x_628_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0(v_root_622_, v___x_627_, v_shift_624_, v___y_618_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_641_; 
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_641_ == 0)
{
lean_object* v_unused_642_; 
v_unused_642_ = lean_ctor_get(v___x_628_, 0);
lean_dec(v_unused_642_);
v___x_630_ = v___x_628_;
v_isShared_631_ = v_isSharedCheck_641_;
goto v_resetjp_629_;
}
else
{
lean_dec(v___x_628_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_641_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_632_; lean_object* v___x_633_; uint8_t v___x_634_; 
v___x_632_ = lean_array_get_size(v_tail_623_);
v___x_633_ = lean_box(0);
v___x_634_ = lean_nat_dec_lt(v___x_620_, v___x_632_);
if (v___x_634_ == 0)
{
lean_object* v___x_636_; 
lean_dec_ref(v_tail_623_);
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 0, v___x_633_);
v___x_636_ = v___x_630_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_633_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
else
{
size_t v___x_638_; size_t v___x_639_; lean_object* v___x_640_; 
lean_del_object(v___x_630_);
v___x_638_ = ((size_t)0ULL);
v___x_639_ = lean_usize_of_nat(v___x_632_);
v___x_640_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(v_tail_623_, v___x_638_, v___x_639_, v___x_633_, v___y_618_);
lean_dec_ref(v_tail_623_);
return v___x_640_;
}
}
}
else
{
lean_dec_ref(v_tail_623_);
return v___x_628_;
}
}
else
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; uint8_t v___x_646_; 
lean_dec_ref(v_root_622_);
v___x_643_ = lean_nat_sub(v_start_617_, v_tailOff_625_);
lean_dec(v_tailOff_625_);
v___x_644_ = lean_array_get_size(v_tail_623_);
v___x_645_ = lean_box(0);
v___x_646_ = lean_nat_dec_lt(v___x_643_, v___x_644_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; 
lean_dec(v___x_643_);
lean_dec_ref(v_tail_623_);
v___x_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_647_, 0, v___x_645_);
return v___x_647_;
}
else
{
size_t v___x_648_; size_t v___x_649_; lean_object* v___x_650_; 
v___x_648_ = lean_usize_of_nat(v___x_643_);
lean_dec(v___x_643_);
v___x_649_ = lean_usize_of_nat(v___x_644_);
v___x_650_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(v_tail_623_, v___x_648_, v___x_649_, v___x_645_, v___y_618_);
lean_dec_ref(v_tail_623_);
return v___x_650_;
}
}
}
else
{
lean_object* v___x_651_; 
v___x_651_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__2(v_t_616_, v___y_618_);
return v___x_651_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList(lean_object* v_trees_652_, lean_object* v_a_653_){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_655_ = lean_unsigned_to_nat(0u);
v___x_656_ = l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0(v_trees_652_, v___x_655_, v_a_653_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList___boxed(lean_object* v_trees_657_, lean_object* v_a_658_, lean_object* v_a_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList(v_trees_657_, v_a_658_);
lean_dec(v_a_658_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1___boxed(lean_object* v_as_661_, lean_object* v_i_662_, lean_object* v_stop_663_, lean_object* v_b_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
size_t v_i_boxed_667_; size_t v_stop_boxed_668_; lean_object* v_res_669_; 
v_i_boxed_667_ = lean_unbox_usize(v_i_662_);
lean_dec(v_i_662_);
v_stop_boxed_668_ = lean_unbox_usize(v_stop_663_);
lean_dec(v_stop_663_);
v_res_669_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(v_as_661_, v_i_boxed_667_, v_stop_boxed_668_, v_b_664_, v___y_665_);
lean_dec(v___y_665_);
lean_dec_ref(v_as_661_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__3___boxed(lean_object* v_as_670_, lean_object* v_i_671_, lean_object* v_stop_672_, lean_object* v_b_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
size_t v_i_boxed_676_; size_t v_stop_boxed_677_; lean_object* v_res_678_; 
v_i_boxed_676_ = lean_unbox_usize(v_i_671_);
lean_dec(v_i_671_);
v_stop_boxed_677_ = lean_unbox_usize(v_stop_672_);
lean_dec(v_stop_672_);
v_res_678_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__3(v_as_670_, v_i_boxed_676_, v_stop_boxed_677_, v_b_673_, v___y_674_);
lean_dec(v___y_674_);
lean_dec_ref(v_as_670_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__2___boxed(lean_object* v_t_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__2(v_t_679_, v___y_680_);
lean_dec(v___y_680_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__2___boxed(lean_object* v_x_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__2(v_x_683_, v___y_684_);
lean_dec(v___y_684_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics___boxed(lean_object* v_x_687_, lean_object* v_a_688_, lean_object* v_a_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics(v_x_687_, v_a_688_);
lean_dec(v_a_688_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0___boxed(lean_object* v_t_691_, lean_object* v_start_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0(v_t_691_, v_start_692_, v___y_693_);
lean_dec(v___y_693_);
lean_dec(v_start_692_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0___boxed(lean_object* v_x_696_, lean_object* v_x_697_, lean_object* v_x_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
size_t v_x_2447__boxed_701_; size_t v_x_2448__boxed_702_; lean_object* v_res_703_; 
v_x_2447__boxed_701_ = lean_unbox_usize(v_x_697_);
lean_dec(v_x_697_);
v_x_2448__boxed_702_ = lean_unbox_usize(v_x_698_);
lean_dec(v_x_698_);
v_res_703_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0(v_x_696_, v_x_2447__boxed_701_, v_x_2448__boxed_702_, v___y_699_);
lean_dec(v___y_699_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2(lean_object* v_00_u03b2_704_, lean_object* v_m_705_, lean_object* v_a_706_){
_start:
{
lean_object* v___x_707_; 
v___x_707_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2___redArg(v_m_705_, v_a_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2___boxed(lean_object* v_00_u03b2_708_, lean_object* v_m_709_, lean_object* v_a_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2(v_00_u03b2_708_, v_m_709_, v_a_710_);
lean_dec_ref(v_a_710_);
return v_res_711_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5(lean_object* v_00_u03b2_712_, lean_object* v_a_713_, lean_object* v_x_714_){
_start:
{
uint8_t v___x_715_; 
v___x_715_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5___redArg(v_a_713_, v_x_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5___boxed(lean_object* v_00_u03b2_716_, lean_object* v_a_717_, lean_object* v_x_718_){
_start:
{
uint8_t v_res_719_; lean_object* v_r_720_; 
v_res_719_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5(v_00_u03b2_716_, v_a_717_, v_x_718_);
lean_dec(v_x_718_);
lean_dec_ref(v_a_717_);
v_r_720_ = lean_box(v_res_719_);
return v_r_720_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__6(lean_object* v_00_u03b2_721_, lean_object* v_a_722_, lean_object* v_x_723_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__6___redArg(v_a_722_, v_x_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__6___boxed(lean_object* v_00_u03b2_725_, lean_object* v_a_726_, lean_object* v_x_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__6(v_00_u03b2_725_, v_a_726_, v_x_727_);
lean_dec_ref(v_a_726_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__0(lean_object* v_a_729_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = lean_nat_to_int(v_a_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4___redArg(lean_object* v___y_731_){
_start:
{
lean_object* v___x_733_; lean_object* v_infoState_734_; lean_object* v_trees_735_; lean_object* v___x_736_; 
v___x_733_ = lean_st_ref_get(v___y_731_);
v_infoState_734_ = lean_ctor_get(v___x_733_, 8);
lean_inc_ref(v_infoState_734_);
lean_dec(v___x_733_);
v_trees_735_ = lean_ctor_get(v_infoState_734_, 2);
lean_inc_ref(v_trees_735_);
lean_dec_ref(v_infoState_734_);
v___x_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_736_, 0, v_trees_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4___redArg___boxed(lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4___redArg(v___y_737_);
lean_dec(v___y_737_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4(lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4___redArg(v___y_741_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4___boxed(lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4(v___y_744_, v___y_745_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
return v_res_747_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__20(lean_object* v_opts_748_, lean_object* v_opt_749_){
_start:
{
lean_object* v_name_750_; lean_object* v_defValue_751_; lean_object* v_map_752_; lean_object* v___x_753_; 
v_name_750_ = lean_ctor_get(v_opt_749_, 0);
v_defValue_751_ = lean_ctor_get(v_opt_749_, 1);
v_map_752_ = lean_ctor_get(v_opts_748_, 0);
v___x_753_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_752_, v_name_750_);
if (lean_obj_tag(v___x_753_) == 0)
{
uint8_t v___x_754_; 
v___x_754_ = lean_unbox(v_defValue_751_);
return v___x_754_;
}
else
{
lean_object* v_val_755_; 
v_val_755_ = lean_ctor_get(v___x_753_, 0);
lean_inc(v_val_755_);
lean_dec_ref_known(v___x_753_, 1);
if (lean_obj_tag(v_val_755_) == 1)
{
uint8_t v_v_756_; 
v_v_756_ = lean_ctor_get_uint8(v_val_755_, 0);
lean_dec_ref_known(v_val_755_, 0);
return v_v_756_;
}
else
{
uint8_t v___x_757_; 
lean_dec(v_val_755_);
v___x_757_ = lean_unbox(v_defValue_751_);
return v___x_757_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__20___boxed(lean_object* v_opts_758_, lean_object* v_opt_759_){
_start:
{
uint8_t v_res_760_; lean_object* v_r_761_; 
v_res_760_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__20(v_opts_758_, v_opt_759_);
lean_dec_ref(v_opt_759_);
lean_dec_ref(v_opts_758_);
v_r_761_ = lean_box(v_res_760_);
return v_r_761_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__0(void){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_762_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__1(void){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_763_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__0);
v___x_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_764_, 0, v___x_763_);
return v___x_764_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__2(void){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_765_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__1);
v___x_766_ = lean_unsigned_to_nat(0u);
v___x_767_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
lean_ctor_set(v___x_767_, 1, v___x_766_);
lean_ctor_set(v___x_767_, 2, v___x_766_);
lean_ctor_set(v___x_767_, 3, v___x_766_);
lean_ctor_set(v___x_767_, 4, v___x_765_);
lean_ctor_set(v___x_767_, 5, v___x_765_);
lean_ctor_set(v___x_767_, 6, v___x_765_);
lean_ctor_set(v___x_767_, 7, v___x_765_);
lean_ctor_set(v___x_767_, 8, v___x_765_);
lean_ctor_set(v___x_767_, 9, v___x_765_);
lean_ctor_set(v___x_767_, 10, v___x_765_);
return v___x_767_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__3(void){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_768_ = lean_unsigned_to_nat(32u);
v___x_769_ = lean_mk_empty_array_with_capacity(v___x_768_);
v___x_770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_770_, 0, v___x_769_);
return v___x_770_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__4(void){
_start:
{
size_t v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_771_ = ((size_t)5ULL);
v___x_772_ = lean_unsigned_to_nat(0u);
v___x_773_ = lean_unsigned_to_nat(32u);
v___x_774_ = lean_mk_empty_array_with_capacity(v___x_773_);
v___x_775_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__3);
v___x_776_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_776_, 0, v___x_775_);
lean_ctor_set(v___x_776_, 1, v___x_774_);
lean_ctor_set(v___x_776_, 2, v___x_772_);
lean_ctor_set(v___x_776_, 3, v___x_772_);
lean_ctor_set_usize(v___x_776_, 4, v___x_771_);
return v___x_776_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__5(void){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_777_ = lean_box(1);
v___x_778_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__4);
v___x_779_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__1);
v___x_780_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
lean_ctor_set(v___x_780_, 1, v___x_778_);
lean_ctor_set(v___x_780_, 2, v___x_777_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg(lean_object* v_msgData_781_, lean_object* v___y_782_){
_start:
{
lean_object* v___x_784_; lean_object* v_env_785_; lean_object* v___x_786_; lean_object* v_scopes_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v_opts_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_784_ = lean_st_ref_get(v___y_782_);
v_env_785_ = lean_ctor_get(v___x_784_, 0);
lean_inc_ref(v_env_785_);
lean_dec(v___x_784_);
v___x_786_ = lean_st_ref_get(v___y_782_);
v_scopes_787_ = lean_ctor_get(v___x_786_, 2);
lean_inc(v_scopes_787_);
lean_dec(v___x_786_);
v___x_788_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_789_ = l_List_head_x21___redArg(v___x_788_, v_scopes_787_);
lean_dec(v_scopes_787_);
v_opts_790_ = lean_ctor_get(v___x_789_, 1);
lean_inc_ref(v_opts_790_);
lean_dec(v___x_789_);
v___x_791_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__2);
v___x_792_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__5);
v___x_793_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_793_, 0, v_env_785_);
lean_ctor_set(v___x_793_, 1, v___x_791_);
lean_ctor_set(v___x_793_, 2, v___x_792_);
lean_ctor_set(v___x_793_, 3, v_opts_790_);
v___x_794_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_794_, 0, v___x_793_);
lean_ctor_set(v___x_794_, 1, v_msgData_781_);
v___x_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_795_, 0, v___x_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___boxed(lean_object* v_msgData_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg(v_msgData_796_, v___y_797_);
lean_dec(v___y_797_);
return v_res_799_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13___lam__0(uint8_t v_suppressElabErrors_801_, uint8_t v___y_802_, lean_object* v_x_803_){
_start:
{
if (lean_obj_tag(v_x_803_) == 1)
{
lean_object* v_pre_804_; 
v_pre_804_ = lean_ctor_get(v_x_803_, 0);
if (lean_obj_tag(v_pre_804_) == 0)
{
lean_object* v_str_805_; lean_object* v___x_806_; uint8_t v___x_807_; 
v_str_805_ = lean_ctor_get(v_x_803_, 1);
v___x_806_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13___lam__0___closed__0));
v___x_807_ = lean_string_dec_eq(v_str_805_, v___x_806_);
if (v___x_807_ == 0)
{
return v___x_807_;
}
else
{
return v_suppressElabErrors_801_;
}
}
else
{
return v___y_802_;
}
}
else
{
return v___y_802_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13___lam__0___boxed(lean_object* v_suppressElabErrors_808_, lean_object* v___y_809_, lean_object* v_x_810_){
_start:
{
uint8_t v_suppressElabErrors_boxed_811_; uint8_t v___y_11152__boxed_812_; uint8_t v_res_813_; lean_object* v_r_814_; 
v_suppressElabErrors_boxed_811_ = lean_unbox(v_suppressElabErrors_808_);
v___y_11152__boxed_812_ = lean_unbox(v___y_809_);
v_res_813_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13___lam__0(v_suppressElabErrors_boxed_811_, v___y_11152__boxed_812_, v_x_810_);
lean_dec(v_x_810_);
v_r_814_ = lean_box(v_res_813_);
return v_r_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13(lean_object* v_ref_816_, lean_object* v_msgData_817_, uint8_t v_severity_818_, uint8_t v_isSilent_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
uint8_t v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; uint8_t v___y_828_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; uint8_t v___y_888_; lean_object* v___y_889_; uint8_t v___y_890_; uint8_t v___y_891_; lean_object* v___y_892_; uint8_t v___y_916_; uint8_t v___y_917_; uint8_t v___y_918_; lean_object* v___y_919_; lean_object* v___y_920_; uint8_t v___y_924_; uint8_t v___y_925_; uint8_t v___y_926_; uint8_t v___x_941_; uint8_t v___y_943_; uint8_t v___y_944_; uint8_t v___y_945_; uint8_t v___y_947_; uint8_t v___x_959_; 
v___x_941_ = 2;
v___x_959_ = l_Lean_instBEqMessageSeverity_beq(v_severity_818_, v___x_941_);
if (v___x_959_ == 0)
{
v___y_947_ = v___x_959_;
goto v___jp_946_;
}
else
{
uint8_t v___x_960_; 
lean_inc_ref(v_msgData_817_);
v___x_960_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_817_);
v___y_947_ = v___x_960_;
goto v___jp_946_;
}
v___jp_823_:
{
lean_object* v___x_832_; 
v___x_832_ = l_Lean_Elab_Command_getScope___redArg(v___y_831_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v_a_833_; lean_object* v___x_834_; 
v_a_833_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_a_833_);
lean_dec_ref_known(v___x_832_, 1);
v___x_834_ = l_Lean_Elab_Command_getScope___redArg(v___y_831_);
if (lean_obj_tag(v___x_834_) == 0)
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_870_; 
v_a_835_ = lean_ctor_get(v___x_834_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_870_ == 0)
{
v___x_837_ = v___x_834_;
v_isShared_838_ = v_isSharedCheck_870_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_834_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_870_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_839_; lean_object* v_currNamespace_840_; lean_object* v_openDecls_841_; lean_object* v_env_842_; lean_object* v_messages_843_; lean_object* v_scopes_844_; lean_object* v_usedQuotCtxts_845_; lean_object* v_nextMacroScope_846_; lean_object* v_maxRecDepth_847_; lean_object* v_ngen_848_; lean_object* v_auxDeclNGen_849_; lean_object* v_infoState_850_; lean_object* v_traceState_851_; lean_object* v_snapshotTasks_852_; lean_object* v_prevLinterStates_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_869_; 
v___x_839_ = lean_st_ref_take(v___y_831_);
v_currNamespace_840_ = lean_ctor_get(v_a_833_, 2);
lean_inc(v_currNamespace_840_);
lean_dec(v_a_833_);
v_openDecls_841_ = lean_ctor_get(v_a_835_, 3);
lean_inc(v_openDecls_841_);
lean_dec(v_a_835_);
v_env_842_ = lean_ctor_get(v___x_839_, 0);
v_messages_843_ = lean_ctor_get(v___x_839_, 1);
v_scopes_844_ = lean_ctor_get(v___x_839_, 2);
v_usedQuotCtxts_845_ = lean_ctor_get(v___x_839_, 3);
v_nextMacroScope_846_ = lean_ctor_get(v___x_839_, 4);
v_maxRecDepth_847_ = lean_ctor_get(v___x_839_, 5);
v_ngen_848_ = lean_ctor_get(v___x_839_, 6);
v_auxDeclNGen_849_ = lean_ctor_get(v___x_839_, 7);
v_infoState_850_ = lean_ctor_get(v___x_839_, 8);
v_traceState_851_ = lean_ctor_get(v___x_839_, 9);
v_snapshotTasks_852_ = lean_ctor_get(v___x_839_, 10);
v_prevLinterStates_853_ = lean_ctor_get(v___x_839_, 11);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_869_ == 0)
{
v___x_855_ = v___x_839_;
v_isShared_856_ = v_isSharedCheck_869_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_prevLinterStates_853_);
lean_inc(v_snapshotTasks_852_);
lean_inc(v_traceState_851_);
lean_inc(v_infoState_850_);
lean_inc(v_auxDeclNGen_849_);
lean_inc(v_ngen_848_);
lean_inc(v_maxRecDepth_847_);
lean_inc(v_nextMacroScope_846_);
lean_inc(v_usedQuotCtxts_845_);
lean_inc(v_scopes_844_);
lean_inc(v_messages_843_);
lean_inc(v_env_842_);
lean_dec(v___x_839_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_869_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_862_; 
v___x_857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_857_, 0, v_currNamespace_840_);
lean_ctor_set(v___x_857_, 1, v_openDecls_841_);
v___x_858_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
lean_ctor_set(v___x_858_, 1, v___y_825_);
lean_inc_ref(v___y_827_);
lean_inc_ref(v___y_830_);
v___x_859_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_859_, 0, v___y_830_);
lean_ctor_set(v___x_859_, 1, v___y_829_);
lean_ctor_set(v___x_859_, 2, v___y_826_);
lean_ctor_set(v___x_859_, 3, v___y_827_);
lean_ctor_set(v___x_859_, 4, v___x_858_);
lean_ctor_set_uint8(v___x_859_, sizeof(void*)*5, v___y_824_);
lean_ctor_set_uint8(v___x_859_, sizeof(void*)*5 + 1, v___y_828_);
lean_ctor_set_uint8(v___x_859_, sizeof(void*)*5 + 2, v_isSilent_819_);
v___x_860_ = l_Lean_MessageLog_add(v___x_859_, v_messages_843_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 1, v___x_860_);
v___x_862_ = v___x_855_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_env_842_);
lean_ctor_set(v_reuseFailAlloc_868_, 1, v___x_860_);
lean_ctor_set(v_reuseFailAlloc_868_, 2, v_scopes_844_);
lean_ctor_set(v_reuseFailAlloc_868_, 3, v_usedQuotCtxts_845_);
lean_ctor_set(v_reuseFailAlloc_868_, 4, v_nextMacroScope_846_);
lean_ctor_set(v_reuseFailAlloc_868_, 5, v_maxRecDepth_847_);
lean_ctor_set(v_reuseFailAlloc_868_, 6, v_ngen_848_);
lean_ctor_set(v_reuseFailAlloc_868_, 7, v_auxDeclNGen_849_);
lean_ctor_set(v_reuseFailAlloc_868_, 8, v_infoState_850_);
lean_ctor_set(v_reuseFailAlloc_868_, 9, v_traceState_851_);
lean_ctor_set(v_reuseFailAlloc_868_, 10, v_snapshotTasks_852_);
lean_ctor_set(v_reuseFailAlloc_868_, 11, v_prevLinterStates_853_);
v___x_862_ = v_reuseFailAlloc_868_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_866_; 
v___x_863_ = lean_st_ref_put(v___y_831_, v___x_862_);
v___x_864_ = lean_box(0);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 0, v___x_864_);
v___x_866_ = v___x_837_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v___x_864_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
}
else
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_878_; 
lean_dec(v_a_833_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
v_a_871_ = lean_ctor_get(v___x_834_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_878_ == 0)
{
v___x_873_ = v___x_834_;
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_834_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_876_; 
if (v_isShared_874_ == 0)
{
v___x_876_ = v___x_873_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_a_871_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
}
else
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
lean_dec_ref(v___y_829_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
v_a_879_ = lean_ctor_get(v___x_832_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_886_ == 0)
{
v___x_881_ = v___x_832_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_832_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_879_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
v___jp_887_:
{
lean_object* v_fileName_893_; lean_object* v_fileMap_894_; uint8_t v_suppressElabErrors_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_914_; 
v_fileName_893_ = lean_ctor_get(v___y_820_, 0);
v_fileMap_894_ = lean_ctor_get(v___y_820_, 1);
v_suppressElabErrors_895_ = lean_ctor_get_uint8(v___y_820_, sizeof(void*)*10);
v___x_896_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_817_);
v___x_897_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg(v___x_896_, v___y_821_);
v_a_898_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_914_ == 0)
{
v___x_900_ = v___x_897_;
v_isShared_901_ = v_isSharedCheck_914_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_dec(v___x_897_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_914_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
lean_inc_ref_n(v_fileMap_894_, 2);
v___x_902_ = l_Lean_FileMap_toPosition(v_fileMap_894_, v___y_889_);
lean_dec(v___y_889_);
v___x_903_ = l_Lean_FileMap_toPosition(v_fileMap_894_, v___y_892_);
lean_dec(v___y_892_);
v___x_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
v___x_905_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13___closed__0));
if (v_suppressElabErrors_895_ == 0)
{
lean_del_object(v___x_900_);
v___y_824_ = v___y_890_;
v___y_825_ = v_a_898_;
v___y_826_ = v___x_904_;
v___y_827_ = v___x_905_;
v___y_828_ = v___y_891_;
v___y_829_ = v___x_902_;
v___y_830_ = v_fileName_893_;
v___y_831_ = v___y_821_;
goto v___jp_823_;
}
else
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___f_908_; uint8_t v___x_909_; 
v___x_906_ = lean_box(v_suppressElabErrors_895_);
v___x_907_ = lean_box(v___y_888_);
v___f_908_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13___lam__0___boxed), 3, 2);
lean_closure_set(v___f_908_, 0, v___x_906_);
lean_closure_set(v___f_908_, 1, v___x_907_);
lean_inc(v_a_898_);
v___x_909_ = l_Lean_MessageData_hasTag(v___f_908_, v_a_898_);
if (v___x_909_ == 0)
{
lean_object* v___x_910_; lean_object* v___x_912_; 
lean_dec_ref_known(v___x_904_, 1);
lean_dec_ref(v___x_902_);
lean_dec(v_a_898_);
v___x_910_ = lean_box(0);
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 0, v___x_910_);
v___x_912_ = v___x_900_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_910_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
else
{
lean_del_object(v___x_900_);
v___y_824_ = v___y_890_;
v___y_825_ = v_a_898_;
v___y_826_ = v___x_904_;
v___y_827_ = v___x_905_;
v___y_828_ = v___y_891_;
v___y_829_ = v___x_902_;
v___y_830_ = v_fileName_893_;
v___y_831_ = v___y_821_;
goto v___jp_823_;
}
}
}
}
v___jp_915_:
{
lean_object* v___x_921_; 
v___x_921_ = l_Lean_Syntax_getTailPos_x3f(v___y_919_, v___y_917_);
lean_dec(v___y_919_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_inc(v___y_920_);
v___y_888_ = v___y_916_;
v___y_889_ = v___y_920_;
v___y_890_ = v___y_917_;
v___y_891_ = v___y_918_;
v___y_892_ = v___y_920_;
goto v___jp_887_;
}
else
{
lean_object* v_val_922_; 
v_val_922_ = lean_ctor_get(v___x_921_, 0);
lean_inc(v_val_922_);
lean_dec_ref_known(v___x_921_, 1);
v___y_888_ = v___y_916_;
v___y_889_ = v___y_920_;
v___y_890_ = v___y_917_;
v___y_891_ = v___y_918_;
v___y_892_ = v_val_922_;
goto v___jp_887_;
}
}
v___jp_923_:
{
lean_object* v___x_927_; 
v___x_927_ = l_Lean_Elab_Command_getRef___redArg(v___y_820_);
if (lean_obj_tag(v___x_927_) == 0)
{
lean_object* v_a_928_; lean_object* v_ref_929_; lean_object* v___x_930_; 
v_a_928_ = lean_ctor_get(v___x_927_, 0);
lean_inc(v_a_928_);
lean_dec_ref_known(v___x_927_, 1);
v_ref_929_ = l_Lean_replaceRef(v_ref_816_, v_a_928_);
lean_dec(v_a_928_);
v___x_930_ = l_Lean_Syntax_getPos_x3f(v_ref_929_, v___y_925_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v___x_931_; 
v___x_931_ = lean_unsigned_to_nat(0u);
v___y_916_ = v___y_924_;
v___y_917_ = v___y_925_;
v___y_918_ = v___y_926_;
v___y_919_ = v_ref_929_;
v___y_920_ = v___x_931_;
goto v___jp_915_;
}
else
{
lean_object* v_val_932_; 
v_val_932_ = lean_ctor_get(v___x_930_, 0);
lean_inc(v_val_932_);
lean_dec_ref_known(v___x_930_, 1);
v___y_916_ = v___y_924_;
v___y_917_ = v___y_925_;
v___y_918_ = v___y_926_;
v___y_919_ = v_ref_929_;
v___y_920_ = v_val_932_;
goto v___jp_915_;
}
}
else
{
lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_940_; 
lean_dec_ref(v_msgData_817_);
v_a_933_ = lean_ctor_get(v___x_927_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_940_ == 0)
{
v___x_935_ = v___x_927_;
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v___x_927_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_938_; 
if (v_isShared_936_ == 0)
{
v___x_938_ = v___x_935_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_a_933_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
}
v___jp_942_:
{
if (v___y_945_ == 0)
{
v___y_924_ = v___y_943_;
v___y_925_ = v___y_944_;
v___y_926_ = v_severity_818_;
goto v___jp_923_;
}
else
{
v___y_924_ = v___y_943_;
v___y_925_ = v___y_944_;
v___y_926_ = v___x_941_;
goto v___jp_923_;
}
}
v___jp_946_:
{
if (v___y_947_ == 0)
{
lean_object* v___x_948_; lean_object* v_scopes_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v_opts_952_; uint8_t v___x_953_; uint8_t v___x_954_; 
v___x_948_ = lean_st_ref_get(v___y_821_);
v_scopes_949_ = lean_ctor_get(v___x_948_, 2);
lean_inc(v_scopes_949_);
lean_dec(v___x_948_);
v___x_950_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_951_ = l_List_head_x21___redArg(v___x_950_, v_scopes_949_);
lean_dec(v_scopes_949_);
v_opts_952_ = lean_ctor_get(v___x_951_, 1);
lean_inc_ref(v_opts_952_);
lean_dec(v___x_951_);
v___x_953_ = 1;
v___x_954_ = l_Lean_instBEqMessageSeverity_beq(v_severity_818_, v___x_953_);
if (v___x_954_ == 0)
{
lean_dec_ref(v_opts_952_);
v___y_943_ = v___y_947_;
v___y_944_ = v___y_947_;
v___y_945_ = v___x_954_;
goto v___jp_942_;
}
else
{
lean_object* v___x_955_; uint8_t v___x_956_; 
v___x_955_ = l_Lean_warningAsError;
v___x_956_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__20(v_opts_952_, v___x_955_);
lean_dec_ref(v_opts_952_);
v___y_943_ = v___y_947_;
v___y_944_ = v___y_947_;
v___y_945_ = v___x_956_;
goto v___jp_942_;
}
}
else
{
lean_object* v___x_957_; lean_object* v___x_958_; 
lean_dec_ref(v_msgData_817_);
v___x_957_ = lean_box(0);
v___x_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
return v___x_958_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13___boxed(lean_object* v_ref_961_, lean_object* v_msgData_962_, lean_object* v_severity_963_, lean_object* v_isSilent_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
uint8_t v_severity_boxed_968_; uint8_t v_isSilent_boxed_969_; lean_object* v_res_970_; 
v_severity_boxed_968_ = lean_unbox(v_severity_963_);
v_isSilent_boxed_969_ = lean_unbox(v_isSilent_964_);
v_res_970_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13(v_ref_961_, v_msgData_962_, v_severity_boxed_968_, v_isSilent_boxed_969_, v___y_965_, v___y_966_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v_ref_961_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5(lean_object* v_ref_971_, lean_object* v_msgData_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
uint8_t v___x_976_; uint8_t v___x_977_; lean_object* v___x_978_; 
v___x_976_ = 1;
v___x_977_ = 0;
v___x_978_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13(v_ref_971_, v_msgData_972_, v___x_976_, v___x_977_, v___y_973_, v___y_974_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5___boxed(lean_object* v_ref_979_, lean_object* v_msgData_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5(v_ref_979_, v_msgData_980_, v___y_981_, v___y_982_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec(v_ref_979_);
return v_res_984_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__1(void){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_986_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__0));
v___x_987_ = l_Lean_stringToMessageData(v___x_986_);
return v___x_987_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__3(void){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__2));
v___x_990_ = l_Lean_stringToMessageData(v___x_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3(lean_object* v_linterOption_991_, lean_object* v_stx_992_, lean_object* v_msg_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
lean_object* v_name_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1015_; 
v_name_997_ = lean_ctor_get(v_linterOption_991_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v_linterOption_991_);
if (v_isSharedCheck_1015_ == 0)
{
lean_object* v_unused_1016_; 
v_unused_1016_ = lean_ctor_get(v_linterOption_991_, 1);
lean_dec(v_unused_1016_);
v___x_999_ = v_linterOption_991_;
v_isShared_1000_ = v_isSharedCheck_1015_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_name_997_);
lean_dec(v_linterOption_991_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1015_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1004_; 
v___x_1001_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__1);
lean_inc(v_name_997_);
v___x_1002_ = l_Lean_MessageData_ofName(v_name_997_);
if (v_isShared_1000_ == 0)
{
lean_ctor_set_tag(v___x_999_, 7);
lean_ctor_set(v___x_999_, 1, v___x_1002_);
lean_ctor_set(v___x_999_, 0, v___x_1001_);
v___x_1004_ = v___x_999_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v___x_1001_);
lean_ctor_set(v_reuseFailAlloc_1014_, 1, v___x_1002_);
v___x_1004_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v_disable_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1005_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__3);
v___x_1006_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1004_);
lean_ctor_set(v___x_1006_, 1, v___x_1005_);
v_disable_1007_ = l_Lean_MessageData_note(v___x_1006_);
v___x_1008_ = l_Lean_Linter_linterMessageTag;
v___x_1009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1009_, 0, v_msg_993_);
lean_ctor_set(v___x_1009_, 1, v_disable_1007_);
v___x_1010_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1008_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
v___x_1011_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1011_, 0, v_name_997_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
lean_inc(v_stx_992_);
v___x_1012_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_1012_, 0, v_stx_992_);
lean_ctor_set(v___x_1012_, 1, v___x_1011_);
v___x_1013_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5(v_stx_992_, v___x_1012_, v___y_994_, v___y_995_);
lean_dec(v_stx_992_);
return v___x_1013_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___boxed(lean_object* v_linterOption_1017_, lean_object* v_stx_1018_, lean_object* v_msg_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3(v_linterOption_1017_, v_stx_1018_, v_msg_1019_, v___y_1020_, v___y_1021_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1___redArg(lean_object* v_o_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v___x_1027_; lean_object* v_env_1028_; lean_object* v___x_1029_; lean_object* v_toEnvExtension_1030_; lean_object* v_asyncMode_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v_merged_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1043_; 
v___x_1027_ = lean_st_ref_get(v___y_1025_);
v_env_1028_ = lean_ctor_get(v___x_1027_, 0);
lean_inc_ref(v_env_1028_);
lean_dec(v___x_1027_);
v___x_1029_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_1030_ = lean_ctor_get(v___x_1029_, 0);
v_asyncMode_1031_ = lean_ctor_get(v_toEnvExtension_1030_, 2);
v___x_1032_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_1033_ = lean_box(0);
v___x_1034_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1032_, v___x_1029_, v_env_1028_, v_asyncMode_1031_, v___x_1033_);
v_merged_1035_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1043_ == 0)
{
lean_object* v_unused_1044_; 
v_unused_1044_ = lean_ctor_get(v___x_1034_, 1);
lean_dec(v_unused_1044_);
v___x_1037_ = v___x_1034_;
v_isShared_1038_ = v_isSharedCheck_1043_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_merged_1035_);
lean_dec(v___x_1034_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1043_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1040_; 
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 1, v_merged_1035_);
lean_ctor_set(v___x_1037_, 0, v_o_1024_);
v___x_1040_ = v___x_1037_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_o_1024_);
lean_ctor_set(v_reuseFailAlloc_1042_, 1, v_merged_1035_);
v___x_1040_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
lean_object* v___x_1041_; 
v___x_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
return v___x_1041_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1___redArg___boxed(lean_object* v_o_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1___redArg(v_o_1045_, v___y_1046_);
lean_dec(v___y_1046_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1(lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v___x_1052_; lean_object* v_scopes_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v_opts_1056_; lean_object* v___x_1057_; 
v___x_1052_ = lean_st_ref_get(v___y_1050_);
v_scopes_1053_ = lean_ctor_get(v___x_1052_, 2);
lean_inc(v_scopes_1053_);
lean_dec(v___x_1052_);
v___x_1054_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1055_ = l_List_head_x21___redArg(v___x_1054_, v_scopes_1053_);
lean_dec(v_scopes_1053_);
v_opts_1056_ = lean_ctor_get(v___x_1055_, 1);
lean_inc_ref(v_opts_1056_);
lean_dec(v___x_1055_);
v___x_1057_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1___redArg(v_opts_1056_, v___y_1050_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1___boxed(lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1(v___y_1058_, v___y_1059_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2(lean_object* v_linterOption_1062_, lean_object* v_stx_1063_, lean_object* v_msg_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
lean_object* v___x_1068_; lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1079_; 
v___x_1068_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1(v___y_1065_, v___y_1066_);
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1071_ = v___x_1068_;
v_isShared_1072_ = v_isSharedCheck_1079_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_dec(v___x_1068_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1079_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
uint8_t v___x_1073_; 
v___x_1073_ = l_Lean_Linter_getLinterValue(v_linterOption_1062_, v_a_1069_);
lean_dec(v_a_1069_);
if (v___x_1073_ == 0)
{
lean_object* v___x_1074_; lean_object* v___x_1076_; 
lean_dec_ref(v_msg_1064_);
lean_dec(v_stx_1063_);
lean_dec_ref(v_linterOption_1062_);
v___x_1074_ = lean_box(0);
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 0, v___x_1074_);
v___x_1076_ = v___x_1071_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1074_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
else
{
lean_object* v___x_1078_; 
lean_del_object(v___x_1071_);
v___x_1078_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3(v_linterOption_1062_, v_stx_1063_, v_msg_1064_, v___y_1065_, v___y_1066_);
return v___x_1078_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2___boxed(lean_object* v_linterOption_1080_, lean_object* v_stx_1081_, lean_object* v_msg_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2(v_linterOption_1080_, v_stx_1081_, v_msg_1082_, v___y_1083_, v___y_1084_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
return v_res_1086_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___closed__2(void){
_start:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1090_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___closed__1));
v___x_1091_ = l_Lean_MessageData_ofFormat(v___x_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5(lean_object* v_as_1092_, size_t v_sz_1093_, size_t v_i_1094_, lean_object* v_b_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
lean_object* v_a_1100_; uint8_t v___x_1104_; 
v___x_1104_ = lean_usize_dec_lt(v_i_1094_, v_sz_1093_);
if (v___x_1104_ == 0)
{
lean_object* v___x_1105_; 
v___x_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1105_, 0, v_b_1095_);
return v___x_1105_;
}
else
{
lean_object* v_a_1106_; lean_object* v_fst_1107_; lean_object* v_snd_1108_; lean_object* v_start_1109_; lean_object* v_stop_1110_; lean_object* v_start_1111_; lean_object* v_stop_1112_; lean_object* v___x_1113_; uint8_t v___y_1115_; uint8_t v___x_1126_; 
v_a_1106_ = lean_array_uget_borrowed(v_as_1092_, v_i_1094_);
v_fst_1107_ = lean_ctor_get(v_a_1106_, 0);
v_snd_1108_ = lean_ctor_get(v_a_1106_, 1);
v_start_1109_ = lean_ctor_get(v_b_1095_, 0);
v_stop_1110_ = lean_ctor_get(v_b_1095_, 1);
v_start_1111_ = lean_ctor_get(v_fst_1107_, 0);
v_stop_1112_ = lean_ctor_get(v_fst_1107_, 1);
v___x_1113_ = l_Lean_Linter_Extra_linter_extra_unreachableTactic;
v___x_1126_ = lean_nat_dec_le(v_start_1109_, v_start_1111_);
if (v___x_1126_ == 0)
{
v___y_1115_ = v___x_1126_;
goto v___jp_1114_;
}
else
{
uint8_t v___x_1127_; 
v___x_1127_ = lean_nat_dec_le(v_stop_1112_, v_stop_1110_);
v___y_1115_ = v___x_1127_;
goto v___jp_1114_;
}
v___jp_1114_:
{
if (v___y_1115_ == 0)
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
lean_dec_ref(v_b_1095_);
v___x_1116_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___closed__2);
lean_inc(v_snd_1108_);
v___x_1117_ = l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2(v___x_1113_, v_snd_1108_, v___x_1116_, v___y_1096_, v___y_1097_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_dec_ref_known(v___x_1117_, 1);
lean_inc(v_fst_1107_);
v_a_1100_ = v_fst_1107_;
goto v___jp_1099_;
}
else
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1120_ = v___x_1117_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1117_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1118_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
else
{
v_a_1100_ = v_b_1095_;
goto v___jp_1099_;
}
}
}
v___jp_1099_:
{
size_t v___x_1101_; size_t v___x_1102_; 
v___x_1101_ = ((size_t)1ULL);
v___x_1102_ = lean_usize_add(v_i_1094_, v___x_1101_);
v_i_1094_ = v___x_1102_;
v_b_1095_ = v_a_1100_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___boxed(lean_object* v_as_1128_, lean_object* v_sz_1129_, lean_object* v_i_1130_, lean_object* v_b_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
size_t v_sz_boxed_1135_; size_t v_i_boxed_1136_; lean_object* v_res_1137_; 
v_sz_boxed_1135_ = lean_unbox_usize(v_sz_1129_);
lean_dec(v_sz_1129_);
v_i_boxed_1136_ = lean_unbox_usize(v_i_1130_);
lean_dec(v_i_1130_);
v_res_1137_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5(v_as_1128_, v_sz_boxed_1135_, v_i_boxed_1136_, v_b_1131_, v___y_1132_, v___y_1133_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec_ref(v_as_1128_);
return v_res_1137_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13_spec__16___redArg(lean_object* v_keys_1138_, lean_object* v_i_1139_, lean_object* v_k_1140_){
_start:
{
lean_object* v___x_1141_; uint8_t v___x_1142_; 
v___x_1141_ = lean_array_get_size(v_keys_1138_);
v___x_1142_ = lean_nat_dec_lt(v_i_1139_, v___x_1141_);
if (v___x_1142_ == 0)
{
lean_dec(v_i_1139_);
return v___x_1142_;
}
else
{
lean_object* v_k_x27_1143_; uint8_t v___x_1144_; 
v_k_x27_1143_ = lean_array_fget_borrowed(v_keys_1138_, v_i_1139_);
v___x_1144_ = lean_name_eq(v_k_1140_, v_k_x27_1143_);
if (v___x_1144_ == 0)
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1145_ = lean_unsigned_to_nat(1u);
v___x_1146_ = lean_nat_add(v_i_1139_, v___x_1145_);
lean_dec(v_i_1139_);
v_i_1139_ = v___x_1146_;
goto _start;
}
else
{
lean_dec(v_i_1139_);
return v___x_1142_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13_spec__16___redArg___boxed(lean_object* v_keys_1148_, lean_object* v_i_1149_, lean_object* v_k_1150_){
_start:
{
uint8_t v_res_1151_; lean_object* v_r_1152_; 
v_res_1151_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13_spec__16___redArg(v_keys_1148_, v_i_1149_, v_k_1150_);
lean_dec(v_k_1150_);
lean_dec_ref(v_keys_1148_);
v_r_1152_ = lean_box(v_res_1151_);
return v_r_1152_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg(lean_object* v_x_1153_, size_t v_x_1154_, lean_object* v_x_1155_){
_start:
{
if (lean_obj_tag(v_x_1153_) == 0)
{
lean_object* v_es_1156_; lean_object* v___x_1157_; size_t v___x_1158_; size_t v___x_1159_; lean_object* v_j_1160_; lean_object* v___x_1161_; 
v_es_1156_ = lean_ctor_get(v_x_1153_, 0);
v___x_1157_ = lean_box(2);
v___x_1158_ = ((size_t)31ULL);
v___x_1159_ = lean_usize_land(v_x_1154_, v___x_1158_);
v_j_1160_ = lean_usize_to_nat(v___x_1159_);
v___x_1161_ = lean_array_get_borrowed(v___x_1157_, v_es_1156_, v_j_1160_);
lean_dec(v_j_1160_);
switch(lean_obj_tag(v___x_1161_))
{
case 0:
{
lean_object* v_key_1162_; uint8_t v___x_1163_; 
v_key_1162_ = lean_ctor_get(v___x_1161_, 0);
v___x_1163_ = lean_name_eq(v_x_1155_, v_key_1162_);
return v___x_1163_;
}
case 1:
{
lean_object* v_node_1164_; size_t v___x_1165_; size_t v___x_1166_; 
v_node_1164_ = lean_ctor_get(v___x_1161_, 0);
v___x_1165_ = ((size_t)5ULL);
v___x_1166_ = lean_usize_shift_right(v_x_1154_, v___x_1165_);
v_x_1153_ = v_node_1164_;
v_x_1154_ = v___x_1166_;
goto _start;
}
default: 
{
uint8_t v___x_1168_; 
v___x_1168_ = 0;
return v___x_1168_;
}
}
}
else
{
lean_object* v_ks_1169_; lean_object* v___x_1170_; uint8_t v___x_1171_; 
v_ks_1169_ = lean_ctor_get(v_x_1153_, 0);
v___x_1170_ = lean_unsigned_to_nat(0u);
v___x_1171_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13_spec__16___redArg(v_ks_1169_, v___x_1170_, v_x_1155_);
return v___x_1171_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg___boxed(lean_object* v_x_1172_, lean_object* v_x_1173_, lean_object* v_x_1174_){
_start:
{
size_t v_x_11669__boxed_1175_; uint8_t v_res_1176_; lean_object* v_r_1177_; 
v_x_11669__boxed_1175_ = lean_unbox_usize(v_x_1173_);
lean_dec(v_x_1173_);
v_res_1176_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg(v_x_1172_, v_x_11669__boxed_1175_, v_x_1174_);
lean_dec(v_x_1174_);
lean_dec_ref(v_x_1172_);
v_r_1177_ = lean_box(v_res_1176_);
return v_r_1177_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9___redArg(lean_object* v_x_1178_, lean_object* v_x_1179_){
_start:
{
uint64_t v___y_1181_; 
if (lean_obj_tag(v_x_1179_) == 0)
{
uint64_t v___x_1184_; 
v___x_1184_ = 1723ULL;
v___y_1181_ = v___x_1184_;
goto v___jp_1180_;
}
else
{
uint64_t v_hash_1185_; 
v_hash_1185_ = lean_ctor_get_uint64(v_x_1179_, sizeof(void*)*2);
v___y_1181_ = v_hash_1185_;
goto v___jp_1180_;
}
v___jp_1180_:
{
size_t v___x_1182_; uint8_t v___x_1183_; 
v___x_1182_ = lean_uint64_to_usize(v___y_1181_);
v___x_1183_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg(v_x_1178_, v___x_1182_, v_x_1179_);
return v___x_1183_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9___redArg___boxed(lean_object* v_x_1186_, lean_object* v_x_1187_){
_start:
{
uint8_t v_res_1188_; lean_object* v_r_1189_; 
v_res_1188_ = l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9___redArg(v_x_1186_, v_x_1187_);
lean_dec(v_x_1187_);
lean_dec_ref(v_x_1186_);
v_r_1189_ = lean_box(v_res_1188_);
return v_r_1189_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19_spec__21_spec__25___redArg(lean_object* v_x_1190_, lean_object* v_x_1191_){
_start:
{
if (lean_obj_tag(v_x_1191_) == 0)
{
return v_x_1190_;
}
else
{
lean_object* v_key_1192_; lean_object* v_value_1193_; lean_object* v_tail_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1217_; 
v_key_1192_ = lean_ctor_get(v_x_1191_, 0);
v_value_1193_ = lean_ctor_get(v_x_1191_, 1);
v_tail_1194_ = lean_ctor_get(v_x_1191_, 2);
v_isSharedCheck_1217_ = !lean_is_exclusive(v_x_1191_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1196_ = v_x_1191_;
v_isShared_1197_ = v_isSharedCheck_1217_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_tail_1194_);
lean_inc(v_value_1193_);
lean_inc(v_key_1192_);
lean_dec(v_x_1191_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1217_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1198_; uint64_t v___x_1199_; uint64_t v___x_1200_; uint64_t v___x_1201_; uint64_t v_fold_1202_; uint64_t v___x_1203_; uint64_t v___x_1204_; uint64_t v___x_1205_; size_t v___x_1206_; size_t v___x_1207_; size_t v___x_1208_; size_t v___x_1209_; size_t v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1213_; 
v___x_1198_ = lean_array_get_size(v_x_1190_);
v___x_1199_ = l_Lean_Syntax_instHashableRange_hash(v_key_1192_);
v___x_1200_ = 32ULL;
v___x_1201_ = lean_uint64_shift_right(v___x_1199_, v___x_1200_);
v_fold_1202_ = lean_uint64_xor(v___x_1199_, v___x_1201_);
v___x_1203_ = 16ULL;
v___x_1204_ = lean_uint64_shift_right(v_fold_1202_, v___x_1203_);
v___x_1205_ = lean_uint64_xor(v_fold_1202_, v___x_1204_);
v___x_1206_ = lean_uint64_to_usize(v___x_1205_);
v___x_1207_ = lean_usize_of_nat(v___x_1198_);
v___x_1208_ = ((size_t)1ULL);
v___x_1209_ = lean_usize_sub(v___x_1207_, v___x_1208_);
v___x_1210_ = lean_usize_land(v___x_1206_, v___x_1209_);
v___x_1211_ = lean_array_uget_borrowed(v_x_1190_, v___x_1210_);
lean_inc(v___x_1211_);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 2, v___x_1211_);
v___x_1213_ = v___x_1196_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_key_1192_);
lean_ctor_set(v_reuseFailAlloc_1216_, 1, v_value_1193_);
lean_ctor_set(v_reuseFailAlloc_1216_, 2, v___x_1211_);
v___x_1213_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
lean_object* v___x_1214_; 
v___x_1214_ = lean_array_uset(v_x_1190_, v___x_1210_, v___x_1213_);
v_x_1190_ = v___x_1214_;
v_x_1191_ = v_tail_1194_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19_spec__21___redArg(lean_object* v_i_1218_, lean_object* v_source_1219_, lean_object* v_target_1220_){
_start:
{
lean_object* v___x_1221_; uint8_t v___x_1222_; 
v___x_1221_ = lean_array_get_size(v_source_1219_);
v___x_1222_ = lean_nat_dec_lt(v_i_1218_, v___x_1221_);
if (v___x_1222_ == 0)
{
lean_dec_ref(v_source_1219_);
lean_dec(v_i_1218_);
return v_target_1220_;
}
else
{
lean_object* v_es_1223_; lean_object* v___x_1224_; lean_object* v_source_1225_; lean_object* v_target_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v_es_1223_ = lean_array_fget(v_source_1219_, v_i_1218_);
v___x_1224_ = lean_box(0);
v_source_1225_ = lean_array_fset(v_source_1219_, v_i_1218_, v___x_1224_);
v_target_1226_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19_spec__21_spec__25___redArg(v_target_1220_, v_es_1223_);
v___x_1227_ = lean_unsigned_to_nat(1u);
v___x_1228_ = lean_nat_add(v_i_1218_, v___x_1227_);
lean_dec(v_i_1218_);
v_i_1218_ = v___x_1228_;
v_source_1219_ = v_source_1225_;
v_target_1220_ = v_target_1226_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19___redArg(lean_object* v_data_1230_){
_start:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v_nbuckets_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1231_ = lean_array_get_size(v_data_1230_);
v___x_1232_ = lean_unsigned_to_nat(2u);
v_nbuckets_1233_ = lean_nat_mul(v___x_1231_, v___x_1232_);
v___x_1234_ = lean_unsigned_to_nat(0u);
v___x_1235_ = lean_box(0);
v___x_1236_ = lean_mk_array(v_nbuckets_1233_, v___x_1235_);
v___x_1237_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19_spec__21___redArg(v___x_1234_, v_data_1230_, v___x_1236_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__20___redArg(lean_object* v_a_1238_, lean_object* v_b_1239_, lean_object* v_x_1240_){
_start:
{
if (lean_obj_tag(v_x_1240_) == 0)
{
lean_dec(v_b_1239_);
lean_dec_ref(v_a_1238_);
return v_x_1240_;
}
else
{
lean_object* v_key_1241_; lean_object* v_value_1242_; lean_object* v_tail_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1255_; 
v_key_1241_ = lean_ctor_get(v_x_1240_, 0);
v_value_1242_ = lean_ctor_get(v_x_1240_, 1);
v_tail_1243_ = lean_ctor_get(v_x_1240_, 2);
v_isSharedCheck_1255_ = !lean_is_exclusive(v_x_1240_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1245_ = v_x_1240_;
v_isShared_1246_ = v_isSharedCheck_1255_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_tail_1243_);
lean_inc(v_value_1242_);
lean_inc(v_key_1241_);
lean_dec(v_x_1240_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1255_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
uint8_t v___x_1247_; 
v___x_1247_ = l_Lean_Syntax_instBEqRange_beq(v_key_1241_, v_a_1238_);
if (v___x_1247_ == 0)
{
lean_object* v___x_1248_; lean_object* v___x_1250_; 
v___x_1248_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__20___redArg(v_a_1238_, v_b_1239_, v_tail_1243_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 2, v___x_1248_);
v___x_1250_ = v___x_1245_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_key_1241_);
lean_ctor_set(v_reuseFailAlloc_1251_, 1, v_value_1242_);
lean_ctor_set(v_reuseFailAlloc_1251_, 2, v___x_1248_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
else
{
lean_object* v___x_1253_; 
lean_dec(v_value_1242_);
lean_dec(v_key_1241_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 1, v_b_1239_);
lean_ctor_set(v___x_1245_, 0, v_a_1238_);
v___x_1253_ = v___x_1245_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_a_1238_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v_b_1239_);
lean_ctor_set(v_reuseFailAlloc_1254_, 2, v_tail_1243_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15___redArg(lean_object* v_m_1256_, lean_object* v_a_1257_, lean_object* v_b_1258_){
_start:
{
lean_object* v_size_1259_; lean_object* v_buckets_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1303_; 
v_size_1259_ = lean_ctor_get(v_m_1256_, 0);
v_buckets_1260_ = lean_ctor_get(v_m_1256_, 1);
v_isSharedCheck_1303_ = !lean_is_exclusive(v_m_1256_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1262_ = v_m_1256_;
v_isShared_1263_ = v_isSharedCheck_1303_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_buckets_1260_);
lean_inc(v_size_1259_);
lean_dec(v_m_1256_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1303_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1264_; uint64_t v___x_1265_; uint64_t v___x_1266_; uint64_t v___x_1267_; uint64_t v_fold_1268_; uint64_t v___x_1269_; uint64_t v___x_1270_; uint64_t v___x_1271_; size_t v___x_1272_; size_t v___x_1273_; size_t v___x_1274_; size_t v___x_1275_; size_t v___x_1276_; lean_object* v_bkt_1277_; uint8_t v___x_1278_; 
v___x_1264_ = lean_array_get_size(v_buckets_1260_);
v___x_1265_ = l_Lean_Syntax_instHashableRange_hash(v_a_1257_);
v___x_1266_ = 32ULL;
v___x_1267_ = lean_uint64_shift_right(v___x_1265_, v___x_1266_);
v_fold_1268_ = lean_uint64_xor(v___x_1265_, v___x_1267_);
v___x_1269_ = 16ULL;
v___x_1270_ = lean_uint64_shift_right(v_fold_1268_, v___x_1269_);
v___x_1271_ = lean_uint64_xor(v_fold_1268_, v___x_1270_);
v___x_1272_ = lean_uint64_to_usize(v___x_1271_);
v___x_1273_ = lean_usize_of_nat(v___x_1264_);
v___x_1274_ = ((size_t)1ULL);
v___x_1275_ = lean_usize_sub(v___x_1273_, v___x_1274_);
v___x_1276_ = lean_usize_land(v___x_1272_, v___x_1275_);
v_bkt_1277_ = lean_array_uget_borrowed(v_buckets_1260_, v___x_1276_);
v___x_1278_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5___redArg(v_a_1257_, v_bkt_1277_);
if (v___x_1278_ == 0)
{
lean_object* v___x_1279_; lean_object* v_size_x27_1280_; lean_object* v___x_1281_; lean_object* v_buckets_x27_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; uint8_t v___x_1288_; 
v___x_1279_ = lean_unsigned_to_nat(1u);
v_size_x27_1280_ = lean_nat_add(v_size_1259_, v___x_1279_);
lean_dec(v_size_1259_);
lean_inc(v_bkt_1277_);
v___x_1281_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1281_, 0, v_a_1257_);
lean_ctor_set(v___x_1281_, 1, v_b_1258_);
lean_ctor_set(v___x_1281_, 2, v_bkt_1277_);
v_buckets_x27_1282_ = lean_array_uset(v_buckets_1260_, v___x_1276_, v___x_1281_);
v___x_1283_ = lean_unsigned_to_nat(4u);
v___x_1284_ = lean_nat_mul(v_size_x27_1280_, v___x_1283_);
v___x_1285_ = lean_unsigned_to_nat(3u);
v___x_1286_ = lean_nat_div(v___x_1284_, v___x_1285_);
lean_dec(v___x_1284_);
v___x_1287_ = lean_array_get_size(v_buckets_x27_1282_);
v___x_1288_ = lean_nat_dec_le(v___x_1286_, v___x_1287_);
lean_dec(v___x_1286_);
if (v___x_1288_ == 0)
{
lean_object* v_val_1289_; lean_object* v___x_1291_; 
v_val_1289_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19___redArg(v_buckets_x27_1282_);
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 1, v_val_1289_);
lean_ctor_set(v___x_1262_, 0, v_size_x27_1280_);
v___x_1291_ = v___x_1262_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_size_x27_1280_);
lean_ctor_set(v_reuseFailAlloc_1292_, 1, v_val_1289_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
else
{
lean_object* v___x_1294_; 
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 1, v_buckets_x27_1282_);
lean_ctor_set(v___x_1262_, 0, v_size_x27_1280_);
v___x_1294_ = v___x_1262_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_size_x27_1280_);
lean_ctor_set(v_reuseFailAlloc_1295_, 1, v_buckets_x27_1282_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
else
{
lean_object* v___x_1296_; lean_object* v_buckets_x27_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1301_; 
lean_inc(v_bkt_1277_);
v___x_1296_ = lean_box(0);
v_buckets_x27_1297_ = lean_array_uset(v_buckets_1260_, v___x_1276_, v___x_1296_);
v___x_1298_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__20___redArg(v_a_1257_, v_b_1258_, v_bkt_1277_);
v___x_1299_ = lean_array_uset(v_buckets_x27_1297_, v___x_1276_, v___x_1298_);
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 1, v___x_1299_);
v___x_1301_ = v___x_1262_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_size_1259_);
lean_ctor_set(v_reuseFailAlloc_1302_, 1, v___x_1299_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10(lean_object* v___x_1304_, lean_object* v___x_1305_, uint8_t v___y_1306_, lean_object* v_ignoreTacticKinds_1307_, lean_object* v_stx_1308_, lean_object* v_a_1309_){
_start:
{
lean_object* v___y_1312_; uint8_t v___y_1313_; 
if (lean_obj_tag(v_stx_1308_) == 1)
{
lean_object* v_kind_1331_; lean_object* v_args_1332_; lean_object* v___y_1334_; uint8_t v___x_1337_; 
v_kind_1331_ = lean_ctor_get(v_stx_1308_, 1);
v_args_1332_ = lean_ctor_get(v_stx_1308_, 2);
v___x_1337_ = l_Lean_Linter_Extra_UnreachableTactic_isIgnoreTacticKind(v_ignoreTacticKinds_1307_, v_kind_1331_);
if (v___x_1337_ == 0)
{
lean_object* v___x_1338_; lean_object* v___x_1339_; uint8_t v___x_1340_; 
v___x_1338_ = lean_unsigned_to_nat(0u);
v___x_1339_ = lean_array_get_size(v_args_1332_);
v___x_1340_ = lean_nat_dec_lt(v___x_1338_, v___x_1339_);
if (v___x_1340_ == 0)
{
v___y_1334_ = v_a_1309_;
goto v___jp_1333_;
}
else
{
lean_object* v___x_1341_; size_t v___x_1342_; size_t v___x_1343_; lean_object* v___x_1344_; 
v___x_1341_ = lean_box(0);
v___x_1342_ = ((size_t)0ULL);
v___x_1343_ = lean_usize_of_nat(v___x_1339_);
v___x_1344_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__16(v___x_1304_, v___x_1305_, v___y_1306_, v_ignoreTacticKinds_1307_, v_args_1332_, v___x_1342_, v___x_1343_, v___x_1341_, v_a_1309_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_dec_ref_known(v___x_1344_, 1);
v___y_1334_ = v_a_1309_;
goto v___jp_1333_;
}
else
{
lean_dec_ref_known(v_stx_1308_, 3);
return v___x_1344_;
}
}
}
else
{
v___y_1334_ = v_a_1309_;
goto v___jp_1333_;
}
v___jp_1333_:
{
uint8_t v___x_1335_; 
v___x_1335_ = l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9___redArg(v___x_1304_, v_kind_1331_);
if (v___x_1335_ == 0)
{
uint8_t v___x_1336_; 
v___x_1336_ = l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9___redArg(v___x_1305_, v_kind_1331_);
v___y_1312_ = v___y_1334_;
v___y_1313_ = v___x_1336_;
goto v___jp_1311_;
}
else
{
v___y_1312_ = v___y_1334_;
v___y_1313_ = v___y_1306_;
goto v___jp_1311_;
}
}
}
else
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
lean_dec(v_stx_1308_);
v___x_1345_ = lean_box(0);
v___x_1346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1345_);
return v___x_1346_;
}
v___jp_1311_:
{
if (v___y_1313_ == 0)
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
lean_dec(v_stx_1308_);
v___x_1314_ = lean_box(0);
v___x_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1314_);
return v___x_1315_;
}
else
{
lean_object* v___x_1316_; 
v___x_1316_ = l_Lean_Syntax_getRange_x3f(v_stx_1308_, v___y_1313_);
if (lean_obj_tag(v___x_1316_) == 1)
{
lean_object* v_val_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1328_; 
v_val_1317_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1319_ = v___x_1316_;
v_isShared_1320_ = v_isSharedCheck_1328_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_val_1317_);
lean_dec(v___x_1316_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1328_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1326_; 
v___x_1321_ = lean_st_ref_take(v___y_1312_);
v___x_1322_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15___redArg(v___x_1321_, v_val_1317_, v_stx_1308_);
v___x_1323_ = lean_st_ref_put(v___y_1312_, v___x_1322_);
v___x_1324_ = lean_box(0);
if (v_isShared_1320_ == 0)
{
lean_ctor_set_tag(v___x_1319_, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1324_);
v___x_1326_ = v___x_1319_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v___x_1324_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
else
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
lean_dec(v___x_1316_);
lean_dec(v_stx_1308_);
v___x_1329_ = lean_box(0);
v___x_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1329_);
return v___x_1330_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__16(lean_object* v___x_1347_, lean_object* v___x_1348_, uint8_t v___y_1349_, lean_object* v_ignoreTacticKinds_1350_, lean_object* v_as_1351_, size_t v_i_1352_, size_t v_stop_1353_, lean_object* v_b_1354_, lean_object* v___y_1355_){
_start:
{
uint8_t v___x_1357_; 
v___x_1357_ = lean_usize_dec_eq(v_i_1352_, v_stop_1353_);
if (v___x_1357_ == 0)
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1358_ = lean_array_uget_borrowed(v_as_1351_, v_i_1352_);
lean_inc(v___x_1358_);
v___x_1359_ = l_Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10(v___x_1347_, v___x_1348_, v___y_1349_, v_ignoreTacticKinds_1350_, v___x_1358_, v___y_1355_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v_a_1360_; size_t v___x_1361_; size_t v___x_1362_; 
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
lean_inc(v_a_1360_);
lean_dec_ref_known(v___x_1359_, 1);
v___x_1361_ = ((size_t)1ULL);
v___x_1362_ = lean_usize_add(v_i_1352_, v___x_1361_);
v_i_1352_ = v___x_1362_;
v_b_1354_ = v_a_1360_;
goto _start;
}
else
{
return v___x_1359_;
}
}
else
{
lean_object* v___x_1364_; 
v___x_1364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1364_, 0, v_b_1354_);
return v___x_1364_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__16___boxed(lean_object* v___x_1365_, lean_object* v___x_1366_, lean_object* v___y_1367_, lean_object* v_ignoreTacticKinds_1368_, lean_object* v_as_1369_, lean_object* v_i_1370_, lean_object* v_stop_1371_, lean_object* v_b_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
uint8_t v___y_11917__boxed_1375_; size_t v_i_boxed_1376_; size_t v_stop_boxed_1377_; lean_object* v_res_1378_; 
v___y_11917__boxed_1375_ = lean_unbox(v___y_1367_);
v_i_boxed_1376_ = lean_unbox_usize(v_i_1370_);
lean_dec(v_i_1370_);
v_stop_boxed_1377_ = lean_unbox_usize(v_stop_1371_);
lean_dec(v_stop_1371_);
v_res_1378_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__16(v___x_1365_, v___x_1366_, v___y_11917__boxed_1375_, v_ignoreTacticKinds_1368_, v_as_1369_, v_i_boxed_1376_, v_stop_boxed_1377_, v_b_1372_, v___y_1373_);
lean_dec(v___y_1373_);
lean_dec_ref(v_as_1369_);
lean_dec_ref(v_ignoreTacticKinds_1368_);
lean_dec_ref(v___x_1366_);
lean_dec_ref(v___x_1365_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10___boxed(lean_object* v___x_1379_, lean_object* v___x_1380_, lean_object* v___y_1381_, lean_object* v_ignoreTacticKinds_1382_, lean_object* v_stx_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_){
_start:
{
uint8_t v___y_11931__boxed_1386_; lean_object* v_res_1387_; 
v___y_11931__boxed_1386_ = lean_unbox(v___y_1381_);
v_res_1387_ = l_Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10(v___x_1379_, v___x_1380_, v___y_11931__boxed_1386_, v_ignoreTacticKinds_1382_, v_stx_1383_, v_a_1384_);
lean_dec(v_a_1384_);
lean_dec_ref(v_ignoreTacticKinds_1382_);
lean_dec_ref(v___x_1380_);
lean_dec_ref(v___x_1379_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8___redArg(lean_object* v_keys_1388_, lean_object* v_vals_1389_, lean_object* v_i_1390_, lean_object* v_k_1391_){
_start:
{
lean_object* v___x_1392_; uint8_t v___x_1393_; 
v___x_1392_ = lean_array_get_size(v_keys_1388_);
v___x_1393_ = lean_nat_dec_lt(v_i_1390_, v___x_1392_);
if (v___x_1393_ == 0)
{
lean_object* v___x_1394_; 
lean_dec(v_i_1390_);
v___x_1394_ = lean_box(0);
return v___x_1394_;
}
else
{
lean_object* v_k_x27_1395_; uint8_t v___x_1396_; 
v_k_x27_1395_ = lean_array_fget_borrowed(v_keys_1388_, v_i_1390_);
v___x_1396_ = lean_name_eq(v_k_1391_, v_k_x27_1395_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1397_ = lean_unsigned_to_nat(1u);
v___x_1398_ = lean_nat_add(v_i_1390_, v___x_1397_);
lean_dec(v_i_1390_);
v_i_1390_ = v___x_1398_;
goto _start;
}
else
{
lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1400_ = lean_array_fget_borrowed(v_vals_1389_, v_i_1390_);
lean_dec(v_i_1390_);
lean_inc(v___x_1400_);
v___x_1401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1401_, 0, v___x_1400_);
return v___x_1401_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_keys_1402_, lean_object* v_vals_1403_, lean_object* v_i_1404_, lean_object* v_k_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8___redArg(v_keys_1402_, v_vals_1403_, v_i_1404_, v_k_1405_);
lean_dec(v_k_1405_);
lean_dec_ref(v_vals_1403_);
lean_dec_ref(v_keys_1402_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5___redArg(lean_object* v_x_1407_, size_t v_x_1408_, lean_object* v_x_1409_){
_start:
{
if (lean_obj_tag(v_x_1407_) == 0)
{
lean_object* v_es_1410_; lean_object* v___x_1411_; size_t v___x_1412_; size_t v___x_1413_; lean_object* v_j_1414_; lean_object* v___x_1415_; 
v_es_1410_ = lean_ctor_get(v_x_1407_, 0);
v___x_1411_ = lean_box(2);
v___x_1412_ = ((size_t)31ULL);
v___x_1413_ = lean_usize_land(v_x_1408_, v___x_1412_);
v_j_1414_ = lean_usize_to_nat(v___x_1413_);
v___x_1415_ = lean_array_get_borrowed(v___x_1411_, v_es_1410_, v_j_1414_);
lean_dec(v_j_1414_);
switch(lean_obj_tag(v___x_1415_))
{
case 0:
{
lean_object* v_key_1416_; lean_object* v_val_1417_; uint8_t v___x_1418_; 
v_key_1416_ = lean_ctor_get(v___x_1415_, 0);
v_val_1417_ = lean_ctor_get(v___x_1415_, 1);
v___x_1418_ = lean_name_eq(v_x_1409_, v_key_1416_);
if (v___x_1418_ == 0)
{
lean_object* v___x_1419_; 
v___x_1419_ = lean_box(0);
return v___x_1419_;
}
else
{
lean_object* v___x_1420_; 
lean_inc(v_val_1417_);
v___x_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1420_, 0, v_val_1417_);
return v___x_1420_;
}
}
case 1:
{
lean_object* v_node_1421_; size_t v___x_1422_; size_t v___x_1423_; 
v_node_1421_ = lean_ctor_get(v___x_1415_, 0);
v___x_1422_ = ((size_t)5ULL);
v___x_1423_ = lean_usize_shift_right(v_x_1408_, v___x_1422_);
v_x_1407_ = v_node_1421_;
v_x_1408_ = v___x_1423_;
goto _start;
}
default: 
{
lean_object* v___x_1425_; 
v___x_1425_ = lean_box(0);
return v___x_1425_;
}
}
}
else
{
lean_object* v_ks_1426_; lean_object* v_vs_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v_ks_1426_ = lean_ctor_get(v_x_1407_, 0);
v_vs_1427_ = lean_ctor_get(v_x_1407_, 1);
v___x_1428_ = lean_unsigned_to_nat(0u);
v___x_1429_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8___redArg(v_ks_1426_, v_vs_1427_, v___x_1428_, v_x_1409_);
return v___x_1429_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5___redArg___boxed(lean_object* v_x_1430_, lean_object* v_x_1431_, lean_object* v_x_1432_){
_start:
{
size_t v_x_12053__boxed_1433_; lean_object* v_res_1434_; 
v_x_12053__boxed_1433_ = lean_unbox_usize(v_x_1431_);
lean_dec(v_x_1431_);
v_res_1434_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5___redArg(v_x_1430_, v_x_12053__boxed_1433_, v_x_1432_);
lean_dec(v_x_1432_);
lean_dec_ref(v_x_1430_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3___redArg(lean_object* v_x_1435_, lean_object* v_x_1436_){
_start:
{
uint64_t v___y_1438_; 
if (lean_obj_tag(v_x_1436_) == 0)
{
uint64_t v___x_1441_; 
v___x_1441_ = 1723ULL;
v___y_1438_ = v___x_1441_;
goto v___jp_1437_;
}
else
{
uint64_t v_hash_1442_; 
v_hash_1442_ = lean_ctor_get_uint64(v_x_1436_, sizeof(void*)*2);
v___y_1438_ = v_hash_1442_;
goto v___jp_1437_;
}
v___jp_1437_:
{
size_t v___x_1439_; lean_object* v___x_1440_; 
v___x_1439_ = lean_uint64_to_usize(v___y_1438_);
v___x_1440_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5___redArg(v_x_1435_, v___x_1439_, v_x_1436_);
return v___x_1440_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3___redArg___boxed(lean_object* v_x_1443_, lean_object* v_x_1444_){
_start:
{
lean_object* v_res_1445_; 
v_res_1445_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3___redArg(v_x_1443_, v_x_1444_);
lean_dec(v_x_1444_);
lean_dec_ref(v_x_1443_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7(lean_object* v_x_1446_, lean_object* v_x_1447_){
_start:
{
if (lean_obj_tag(v_x_1447_) == 0)
{
return v_x_1446_;
}
else
{
lean_object* v_key_1448_; lean_object* v_value_1449_; lean_object* v_tail_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
v_key_1448_ = lean_ctor_get(v_x_1447_, 0);
v_value_1449_ = lean_ctor_get(v_x_1447_, 1);
v_tail_1450_ = lean_ctor_get(v_x_1447_, 2);
lean_inc(v_value_1449_);
lean_inc(v_key_1448_);
v___x_1451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1451_, 0, v_key_1448_);
lean_ctor_set(v___x_1451_, 1, v_value_1449_);
v___x_1452_ = lean_array_push(v_x_1446_, v___x_1451_);
v_x_1446_ = v___x_1452_;
v_x_1447_ = v_tail_1450_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___boxed(lean_object* v_x_1454_, lean_object* v_x_1455_){
_start:
{
lean_object* v_res_1456_; 
v_res_1456_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7(v_x_1454_, v_x_1455_);
lean_dec(v_x_1455_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8(lean_object* v_as_1457_, size_t v_i_1458_, size_t v_stop_1459_, lean_object* v_b_1460_){
_start:
{
uint8_t v___x_1461_; 
v___x_1461_ = lean_usize_dec_eq(v_i_1458_, v_stop_1459_);
if (v___x_1461_ == 0)
{
lean_object* v___x_1462_; lean_object* v___x_1463_; size_t v___x_1464_; size_t v___x_1465_; 
v___x_1462_ = lean_array_uget_borrowed(v_as_1457_, v_i_1458_);
v___x_1463_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7(v_b_1460_, v___x_1462_);
v___x_1464_ = ((size_t)1ULL);
v___x_1465_ = lean_usize_add(v_i_1458_, v___x_1464_);
v_i_1458_ = v___x_1465_;
v_b_1460_ = v___x_1463_;
goto _start;
}
else
{
return v_b_1460_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8___boxed(lean_object* v_as_1467_, lean_object* v_i_1468_, lean_object* v_stop_1469_, lean_object* v_b_1470_){
_start:
{
size_t v_i_boxed_1471_; size_t v_stop_boxed_1472_; lean_object* v_res_1473_; 
v_i_boxed_1471_ = lean_unbox_usize(v_i_1468_);
lean_dec(v_i_1468_);
v_stop_boxed_1472_ = lean_unbox_usize(v_stop_1469_);
lean_dec(v_stop_1469_);
v_res_1473_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8(v_as_1467_, v_i_boxed_1471_, v_stop_boxed_1472_, v_b_1470_);
lean_dec_ref(v_as_1467_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___lam__0(lean_object* v_r_1474_){
_start:
{
lean_object* v_start_1475_; lean_object* v_stop_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1485_; 
v_start_1475_ = lean_ctor_get(v_r_1474_, 0);
v_stop_1476_ = lean_ctor_get(v_r_1474_, 1);
v_isSharedCheck_1485_ = !lean_is_exclusive(v_r_1474_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1478_ = v_r_1474_;
v_isShared_1479_ = v_isSharedCheck_1485_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_stop_1476_);
lean_inc(v_start_1475_);
lean_dec(v_r_1474_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1485_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1483_; 
v___x_1480_ = lean_nat_to_int(v_stop_1476_);
v___x_1481_ = lean_int_neg(v___x_1480_);
lean_dec(v___x_1480_);
if (v_isShared_1479_ == 0)
{
lean_ctor_set(v___x_1478_, 1, v___x_1481_);
v___x_1483_ = v___x_1478_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_start_1475_);
lean_ctor_set(v_reuseFailAlloc_1484_, 1, v___x_1481_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9___redArg(lean_object* v_hi_1488_, lean_object* v_pivot_1489_, lean_object* v_as_1490_, lean_object* v_i_1491_, lean_object* v_k_1492_){
_start:
{
uint8_t v___x_1497_; 
v___x_1497_ = lean_nat_dec_lt(v_k_1492_, v_hi_1488_);
if (v___x_1497_ == 0)
{
lean_object* v___x_1498_; lean_object* v___x_1499_; 
lean_dec(v_k_1492_);
lean_dec_ref(v_pivot_1489_);
v___x_1498_ = lean_array_fswap(v_as_1490_, v_i_1491_, v_hi_1488_);
v___x_1499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1499_, 0, v_i_1491_);
lean_ctor_set(v___x_1499_, 1, v___x_1498_);
return v___x_1499_;
}
else
{
lean_object* v___x_1500_; lean_object* v_fst_1501_; lean_object* v_fst_1502_; lean_object* v___f_1503_; lean_object* v___f_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_10744__overap_1507_; lean_object* v___x_1508_; uint8_t v___x_1509_; 
v___x_1500_ = lean_array_fget_borrowed(v_as_1490_, v_k_1492_);
v_fst_1501_ = lean_ctor_get(v___x_1500_, 0);
v_fst_1502_ = lean_ctor_get(v_pivot_1489_, 0);
v___f_1503_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9___redArg___closed__0));
v___f_1504_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9___redArg___closed__1));
lean_inc(v_fst_1501_);
v___x_1505_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___lam__0(v_fst_1501_);
lean_inc(v_fst_1502_);
v___x_1506_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___lam__0(v_fst_1502_);
v___x_10744__overap_1507_ = l_lexOrd___redArg(v___f_1503_, v___f_1504_);
v___x_1508_ = lean_apply_2(v___x_10744__overap_1507_, v___x_1505_, v___x_1506_);
v___x_1509_ = lean_unbox(v___x_1508_);
if (v___x_1509_ == 0)
{
if (v___x_1497_ == 0)
{
goto v___jp_1493_;
}
else
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1510_ = lean_array_fswap(v_as_1490_, v_i_1491_, v_k_1492_);
v___x_1511_ = lean_unsigned_to_nat(1u);
v___x_1512_ = lean_nat_add(v_i_1491_, v___x_1511_);
lean_dec(v_i_1491_);
v___x_1513_ = lean_nat_add(v_k_1492_, v___x_1511_);
lean_dec(v_k_1492_);
v_as_1490_ = v___x_1510_;
v_i_1491_ = v___x_1512_;
v_k_1492_ = v___x_1513_;
goto _start;
}
}
else
{
goto v___jp_1493_;
}
}
v___jp_1493_:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1494_ = lean_unsigned_to_nat(1u);
v___x_1495_ = lean_nat_add(v_k_1492_, v___x_1494_);
lean_dec(v_k_1492_);
v_k_1492_ = v___x_1495_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9___redArg___boxed(lean_object* v_hi_1515_, lean_object* v_pivot_1516_, lean_object* v_as_1517_, lean_object* v_i_1518_, lean_object* v_k_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9___redArg(v_hi_1515_, v_pivot_1516_, v_as_1517_, v_i_1518_, v_k_1519_);
lean_dec(v_hi_1515_);
return v_res_1520_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___lam__1(lean_object* v___f_1521_, lean_object* v___f_1522_, lean_object* v___f_1523_, uint8_t v___x_1524_, lean_object* v_x1_1525_, lean_object* v_x2_1526_){
_start:
{
lean_object* v_fst_1527_; lean_object* v_fst_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_11003__overap_1531_; lean_object* v___x_1532_; uint8_t v___x_1533_; 
v_fst_1527_ = lean_ctor_get(v_x1_1525_, 0);
lean_inc(v_fst_1527_);
lean_dec_ref(v_x1_1525_);
v_fst_1528_ = lean_ctor_get(v_x2_1526_, 0);
lean_inc(v_fst_1528_);
lean_dec_ref(v_x2_1526_);
lean_inc_ref(v___f_1521_);
v___x_1529_ = lean_apply_1(v___f_1521_, v_fst_1527_);
v___x_1530_ = lean_apply_1(v___f_1521_, v_fst_1528_);
v___x_11003__overap_1531_ = l_lexOrd___redArg(v___f_1522_, v___f_1523_);
v___x_1532_ = lean_apply_2(v___x_11003__overap_1531_, v___x_1529_, v___x_1530_);
v___x_1533_ = lean_unbox(v___x_1532_);
if (v___x_1533_ == 0)
{
return v___x_1524_;
}
else
{
uint8_t v___x_1534_; 
v___x_1534_ = 0;
return v___x_1534_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___lam__1___boxed(lean_object* v___f_1535_, lean_object* v___f_1536_, lean_object* v___f_1537_, lean_object* v___x_1538_, lean_object* v_x1_1539_, lean_object* v_x2_1540_){
_start:
{
uint8_t v___x_12210__boxed_1541_; uint8_t v_res_1542_; lean_object* v_r_1543_; 
v___x_12210__boxed_1541_ = lean_unbox(v___x_1538_);
v_res_1542_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___lam__1(v___f_1535_, v___f_1536_, v___f_1537_, v___x_12210__boxed_1541_, v_x1_1539_, v_x2_1540_);
v_r_1543_ = lean_box(v_res_1542_);
return v_r_1543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg(lean_object* v_n_1545_, lean_object* v_as_1546_, lean_object* v_lo_1547_, lean_object* v_hi_1548_){
_start:
{
lean_object* v___y_1550_; uint8_t v___x_1560_; 
v___x_1560_ = lean_nat_dec_lt(v_lo_1547_, v_hi_1548_);
if (v___x_1560_ == 0)
{
lean_dec(v_lo_1547_);
return v_as_1546_;
}
else
{
lean_object* v___f_1561_; lean_object* v___f_1562_; lean_object* v___f_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v_mid_1566_; lean_object* v___y_1568_; lean_object* v___y_1574_; lean_object* v___x_1579_; lean_object* v___x_1580_; uint8_t v___x_1581_; 
v___f_1561_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___closed__0));
v___f_1562_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9___redArg___closed__0));
v___f_1563_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9___redArg___closed__1));
v___x_1564_ = lean_nat_add(v_lo_1547_, v_hi_1548_);
v___x_1565_ = lean_unsigned_to_nat(1u);
v_mid_1566_ = lean_nat_shiftr(v___x_1564_, v___x_1565_);
lean_dec(v___x_1564_);
v___x_1579_ = lean_array_fget_borrowed(v_as_1546_, v_mid_1566_);
v___x_1580_ = lean_array_fget_borrowed(v_as_1546_, v_lo_1547_);
lean_inc(v___x_1580_);
lean_inc(v___x_1579_);
v___x_1581_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___lam__1(v___f_1561_, v___f_1562_, v___f_1563_, v___x_1560_, v___x_1579_, v___x_1580_);
if (v___x_1581_ == 0)
{
v___y_1574_ = v_as_1546_;
goto v___jp_1573_;
}
else
{
lean_object* v___x_1582_; 
v___x_1582_ = lean_array_fswap(v_as_1546_, v_lo_1547_, v_mid_1566_);
v___y_1574_ = v___x_1582_;
goto v___jp_1573_;
}
v___jp_1567_:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; uint8_t v___x_1571_; 
v___x_1569_ = lean_array_fget_borrowed(v___y_1568_, v_mid_1566_);
v___x_1570_ = lean_array_fget_borrowed(v___y_1568_, v_hi_1548_);
lean_inc(v___x_1570_);
lean_inc(v___x_1569_);
v___x_1571_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___lam__1(v___f_1561_, v___f_1562_, v___f_1563_, v___x_1560_, v___x_1569_, v___x_1570_);
if (v___x_1571_ == 0)
{
lean_dec(v_mid_1566_);
v___y_1550_ = v___y_1568_;
goto v___jp_1549_;
}
else
{
lean_object* v___x_1572_; 
v___x_1572_ = lean_array_fswap(v___y_1568_, v_mid_1566_, v_hi_1548_);
lean_dec(v_mid_1566_);
v___y_1550_ = v___x_1572_;
goto v___jp_1549_;
}
}
v___jp_1573_:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; uint8_t v___x_1577_; 
v___x_1575_ = lean_array_fget_borrowed(v___y_1574_, v_hi_1548_);
v___x_1576_ = lean_array_fget_borrowed(v___y_1574_, v_lo_1547_);
lean_inc(v___x_1576_);
lean_inc(v___x_1575_);
v___x_1577_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___lam__1(v___f_1561_, v___f_1562_, v___f_1563_, v___x_1560_, v___x_1575_, v___x_1576_);
if (v___x_1577_ == 0)
{
v___y_1568_ = v___y_1574_;
goto v___jp_1567_;
}
else
{
lean_object* v___x_1578_; 
v___x_1578_ = lean_array_fswap(v___y_1574_, v_lo_1547_, v_hi_1548_);
v___y_1568_ = v___x_1578_;
goto v___jp_1567_;
}
}
}
v___jp_1549_:
{
lean_object* v_pivot_1551_; lean_object* v___x_1552_; lean_object* v_fst_1553_; lean_object* v_snd_1554_; uint8_t v___x_1555_; 
v_pivot_1551_ = lean_array_fget(v___y_1550_, v_hi_1548_);
lean_inc_n(v_lo_1547_, 2);
v___x_1552_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9___redArg(v_hi_1548_, v_pivot_1551_, v___y_1550_, v_lo_1547_, v_lo_1547_);
v_fst_1553_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_fst_1553_);
v_snd_1554_ = lean_ctor_get(v___x_1552_, 1);
lean_inc(v_snd_1554_);
lean_dec_ref(v___x_1552_);
v___x_1555_ = lean_nat_dec_le(v_hi_1548_, v_fst_1553_);
if (v___x_1555_ == 0)
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1556_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg(v_n_1545_, v_snd_1554_, v_lo_1547_, v_fst_1553_);
v___x_1557_ = lean_unsigned_to_nat(1u);
v___x_1558_ = lean_nat_add(v_fst_1553_, v___x_1557_);
lean_dec(v_fst_1553_);
v_as_1546_ = v___x_1556_;
v_lo_1547_ = v___x_1558_;
goto _start;
}
else
{
lean_dec(v_fst_1553_);
lean_dec(v_lo_1547_);
return v_snd_1554_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___boxed(lean_object* v_n_1583_, lean_object* v_as_1584_, lean_object* v_lo_1585_, lean_object* v_hi_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg(v_n_1583_, v_as_1584_, v_lo_1585_, v_hi_1586_);
lean_dec(v_hi_1586_);
lean_dec(v_n_1583_);
return v_res_1587_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1594_ = lean_box(0);
v___x_1595_ = lean_unsigned_to_nat(16u);
v___x_1596_ = lean_mk_array(v___x_1595_, v___x_1594_);
return v___x_1596_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1597_ = lean_obj_once(&l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__4, &l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__4_once, _init_l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__4);
v___x_1598_ = lean_unsigned_to_nat(0u);
v___x_1599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1598_);
lean_ctor_set(v___x_1599_, 1, v___x_1597_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0(lean_object* v___x_1600_, lean_object* v_stx_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_){
_start:
{
lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1639_; lean_object* v___y_1640_; lean_object* v___y_1643_; lean_object* v___y_1644_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___x_1677_; lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1733_; 
v___x_1677_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1(v___y_1602_, v___y_1603_);
v_a_1678_ = lean_ctor_get(v___x_1677_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1680_ = v___x_1677_;
v_isShared_1681_ = v_isSharedCheck_1733_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1677_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1733_;
goto v_resetjp_1679_;
}
v___jp_1605_:
{
size_t v_sz_1608_; size_t v___x_1609_; lean_object* v___x_1610_; 
v_sz_1608_ = lean_array_size(v___y_1607_);
v___x_1609_ = ((size_t)0ULL);
v___x_1610_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5(v___y_1607_, v_sz_1608_, v___x_1609_, v___y_1606_, v___y_1602_, v___y_1603_);
lean_dec_ref(v___y_1607_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1618_; 
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1618_ == 0)
{
lean_object* v_unused_1619_; 
v_unused_1619_ = lean_ctor_get(v___x_1610_, 0);
lean_dec(v_unused_1619_);
v___x_1612_ = v___x_1610_;
v_isShared_1613_ = v_isSharedCheck_1618_;
goto v_resetjp_1611_;
}
else
{
lean_dec(v___x_1610_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1618_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1614_; lean_object* v___x_1616_; 
v___x_1614_ = lean_box(0);
if (v_isShared_1613_ == 0)
{
lean_ctor_set(v___x_1612_, 0, v___x_1614_);
v___x_1616_ = v___x_1612_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v___x_1614_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
else
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1627_; 
v_a_1620_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1622_ = v___x_1610_;
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1610_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
v___jp_1628_:
{
lean_object* v___x_1634_; 
v___x_1634_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg(v___y_1631_, v___y_1629_, v___y_1630_, v___y_1633_);
lean_dec(v___y_1633_);
lean_dec(v___y_1631_);
v___y_1606_ = v___y_1632_;
v___y_1607_ = v___x_1634_;
goto v___jp_1605_;
}
v___jp_1635_:
{
uint8_t v___x_1641_; 
v___x_1641_ = lean_nat_dec_le(v___y_1640_, v___y_1637_);
if (v___x_1641_ == 0)
{
lean_dec(v___y_1637_);
lean_inc(v___y_1640_);
v___y_1629_ = v___y_1636_;
v___y_1630_ = v___y_1640_;
v___y_1631_ = v___y_1638_;
v___y_1632_ = v___y_1639_;
v___y_1633_ = v___y_1640_;
goto v___jp_1628_;
}
else
{
v___y_1629_ = v___y_1636_;
v___y_1630_ = v___y_1640_;
v___y_1631_ = v___y_1638_;
v___y_1632_ = v___y_1639_;
v___y_1633_ = v___y_1637_;
goto v___jp_1628_;
}
}
v___jp_1642_:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; uint8_t v___x_1647_; 
lean_inc_n(v___y_1643_, 2);
v___x_1645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1645_, 0, v___y_1643_);
lean_ctor_set(v___x_1645_, 1, v___y_1643_);
v___x_1646_ = lean_array_get_size(v___y_1644_);
v___x_1647_ = lean_nat_dec_eq(v___x_1646_, v___y_1643_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1648_; lean_object* v___x_1649_; uint8_t v___x_1650_; 
v___x_1648_ = lean_unsigned_to_nat(1u);
v___x_1649_ = lean_nat_sub(v___x_1646_, v___x_1648_);
v___x_1650_ = lean_nat_dec_le(v___y_1643_, v___x_1649_);
if (v___x_1650_ == 0)
{
lean_dec(v___y_1643_);
lean_inc(v___x_1649_);
v___y_1636_ = v___y_1644_;
v___y_1637_ = v___x_1649_;
v___y_1638_ = v___x_1646_;
v___y_1639_ = v___x_1645_;
v___y_1640_ = v___x_1649_;
goto v___jp_1635_;
}
else
{
v___y_1636_ = v___y_1644_;
v___y_1637_ = v___x_1649_;
v___y_1638_ = v___x_1646_;
v___y_1639_ = v___x_1645_;
v___y_1640_ = v___y_1643_;
goto v___jp_1635_;
}
}
else
{
lean_dec(v___y_1643_);
v___y_1606_ = v___x_1645_;
v___y_1607_ = v___y_1644_;
goto v___jp_1605_;
}
}
v___jp_1651_:
{
if (lean_obj_tag(v___y_1654_) == 0)
{
lean_object* v___x_1655_; lean_object* v_size_1656_; lean_object* v_buckets_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; uint8_t v___x_1660_; 
lean_dec_ref_known(v___y_1654_, 1);
v___x_1655_ = lean_st_ref_get(v___y_1652_);
lean_dec(v___y_1652_);
v_size_1656_ = lean_ctor_get(v___x_1655_, 0);
lean_inc(v_size_1656_);
v_buckets_1657_ = lean_ctor_get(v___x_1655_, 1);
lean_inc_ref(v_buckets_1657_);
lean_dec(v___x_1655_);
v___x_1658_ = lean_mk_empty_array_with_capacity(v_size_1656_);
lean_dec(v_size_1656_);
v___x_1659_ = lean_array_get_size(v_buckets_1657_);
v___x_1660_ = lean_nat_dec_lt(v___y_1653_, v___x_1659_);
if (v___x_1660_ == 0)
{
lean_dec_ref(v_buckets_1657_);
v___y_1643_ = v___y_1653_;
v___y_1644_ = v___x_1658_;
goto v___jp_1642_;
}
else
{
size_t v___x_1661_; size_t v___x_1662_; lean_object* v___x_1663_; 
v___x_1661_ = ((size_t)0ULL);
v___x_1662_ = lean_usize_of_nat(v___x_1659_);
v___x_1663_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8(v_buckets_1657_, v___x_1661_, v___x_1662_, v___x_1658_);
lean_dec_ref(v_buckets_1657_);
v___y_1643_ = v___y_1653_;
v___y_1644_ = v___x_1663_;
goto v___jp_1642_;
}
}
else
{
lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1676_; 
lean_dec(v___y_1653_);
lean_dec(v___y_1652_);
v_a_1664_ = lean_ctor_get(v___y_1654_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___y_1654_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1666_ = v___y_1654_;
v_isShared_1667_ = v_isSharedCheck_1676_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_dec(v___y_1654_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1676_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v_ref_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1674_; 
v_ref_1668_ = lean_ctor_get(v___y_1602_, 7);
v___x_1669_ = lean_io_error_to_string(v_a_1664_);
v___x_1670_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1669_);
v___x_1671_ = l_Lean_MessageData_ofFormat(v___x_1670_);
lean_inc(v_ref_1668_);
v___x_1672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1672_, 0, v_ref_1668_);
lean_ctor_set(v___x_1672_, 1, v___x_1671_);
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 0, v___x_1672_);
v___x_1674_ = v___x_1666_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v___x_1672_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
}
v_resetjp_1679_:
{
lean_object* v___x_1682_; uint8_t v___y_1684_; lean_object* v___x_1729_; uint8_t v___x_1730_; 
v___x_1682_ = lean_st_ref_get(v___y_1603_);
v___x_1729_ = l_Lean_Linter_Extra_linter_extra_unreachableTactic;
v___x_1730_ = l_Lean_Linter_getLinterValue(v___x_1729_, v_a_1678_);
lean_dec(v_a_1678_);
if (v___x_1730_ == 0)
{
lean_dec(v___x_1682_);
v___y_1684_ = v___x_1730_;
goto v___jp_1683_;
}
else
{
lean_object* v_infoState_1731_; uint8_t v_enabled_1732_; 
v_infoState_1731_ = lean_ctor_get(v___x_1682_, 8);
lean_inc_ref(v_infoState_1731_);
lean_dec(v___x_1682_);
v_enabled_1732_ = lean_ctor_get_uint8(v_infoState_1731_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1731_);
v___y_1684_ = v_enabled_1732_;
goto v___jp_1683_;
}
v___jp_1683_:
{
if (v___y_1684_ == 0)
{
lean_object* v___x_1685_; lean_object* v___x_1687_; 
lean_dec(v_stx_1601_);
v___x_1685_ = lean_box(0);
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 0, v___x_1685_);
v___x_1687_ = v___x_1680_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1685_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
else
{
lean_object* v___x_1689_; lean_object* v_messages_1690_; uint8_t v___x_1691_; 
v___x_1689_ = lean_st_ref_get(v___y_1603_);
v_messages_1690_ = lean_ctor_get(v___x_1689_, 1);
lean_inc_ref(v_messages_1690_);
lean_dec(v___x_1689_);
v___x_1691_ = l_Lean_MessageLog_hasErrors(v_messages_1690_);
lean_dec_ref(v_messages_1690_);
if (v___x_1691_ == 0)
{
lean_object* v___x_1692_; lean_object* v_env_1693_; lean_object* v___x_1694_; lean_object* v_ext_1695_; lean_object* v_toEnvExtension_1696_; lean_object* v_asyncMode_1697_; lean_object* v___x_1698_; lean_object* v_categories_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1692_ = lean_st_ref_get(v___y_1603_);
v_env_1693_ = lean_ctor_get(v___x_1692_, 0);
lean_inc_ref(v_env_1693_);
lean_dec(v___x_1692_);
v___x_1694_ = l_Lean_Parser_parserExtension;
v_ext_1695_ = lean_ctor_get(v___x_1694_, 1);
v_toEnvExtension_1696_ = lean_ctor_get(v_ext_1695_, 0);
v_asyncMode_1697_ = lean_ctor_get(v_toEnvExtension_1696_, 2);
v___x_1698_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1600_, v___x_1694_, v_env_1693_, v_asyncMode_1697_);
v_categories_1699_ = lean_ctor_get(v___x_1698_, 2);
lean_inc_ref(v_categories_1699_);
lean_dec(v___x_1698_);
v___x_1700_ = ((lean_object*)(l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__1));
v___x_1701_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3___redArg(v_categories_1699_, v___x_1700_);
if (lean_obj_tag(v___x_1701_) == 0)
{
lean_object* v___x_1702_; lean_object* v___x_1704_; 
lean_dec_ref(v_categories_1699_);
lean_dec(v_stx_1601_);
v___x_1702_ = lean_box(0);
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 0, v___x_1702_);
v___x_1704_ = v___x_1680_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v___x_1702_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
else
{
lean_object* v_val_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v_val_1706_ = lean_ctor_get(v___x_1701_, 0);
lean_inc(v_val_1706_);
lean_dec_ref_known(v___x_1701_, 1);
v___x_1707_ = ((lean_object*)(l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__3));
v___x_1708_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3___redArg(v_categories_1699_, v___x_1707_);
lean_dec_ref(v_categories_1699_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v___x_1709_; lean_object* v___x_1711_; 
lean_dec(v_val_1706_);
lean_dec(v_stx_1601_);
v___x_1709_ = lean_box(0);
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 0, v___x_1709_);
v___x_1711_ = v___x_1680_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v___x_1709_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
else
{
lean_object* v_val_1713_; lean_object* v___x_1714_; lean_object* v_a_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v_kinds_1721_; lean_object* v_kinds_1722_; lean_object* v___x_1723_; 
lean_del_object(v___x_1680_);
v_val_1713_ = lean_ctor_get(v___x_1708_, 0);
lean_inc(v_val_1713_);
lean_dec_ref_known(v___x_1708_, 1);
v___x_1714_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4___redArg(v___y_1603_);
v_a_1715_ = lean_ctor_get(v___x_1714_, 0);
lean_inc(v_a_1715_);
lean_dec_ref(v___x_1714_);
v___x_1716_ = lean_unsigned_to_nat(0u);
v___x_1717_ = lean_obj_once(&l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__5, &l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__5_once, _init_l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__5);
v___x_1718_ = lean_st_mk_ref(v___x_1717_);
v___x_1719_ = l_Lean_Linter_Extra_UnreachableTactic_ignoreTacticKindsRef;
v___x_1720_ = lean_st_ref_get(v___x_1719_);
v_kinds_1721_ = lean_ctor_get(v_val_1706_, 1);
lean_inc_ref(v_kinds_1721_);
lean_dec(v_val_1706_);
v_kinds_1722_ = lean_ctor_get(v_val_1713_, 1);
lean_inc_ref(v_kinds_1722_);
lean_dec(v_val_1713_);
v___x_1723_ = l_Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10(v_kinds_1721_, v_kinds_1722_, v___y_1684_, v___x_1720_, v_stx_1601_, v___x_1718_);
lean_dec(v___x_1720_);
lean_dec_ref(v_kinds_1722_);
lean_dec_ref(v_kinds_1721_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v___x_1724_; 
lean_dec_ref_known(v___x_1723_, 1);
v___x_1724_ = l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList(v_a_1715_, v___x_1718_);
v___y_1652_ = v___x_1718_;
v___y_1653_ = v___x_1716_;
v___y_1654_ = v___x_1724_;
goto v___jp_1651_;
}
else
{
lean_dec(v_a_1715_);
v___y_1652_ = v___x_1718_;
v___y_1653_ = v___x_1716_;
v___y_1654_ = v___x_1723_;
goto v___jp_1651_;
}
}
}
}
else
{
lean_object* v___x_1725_; lean_object* v___x_1727_; 
lean_dec(v_stx_1601_);
v___x_1725_ = lean_box(0);
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 0, v___x_1725_);
v___x_1727_ = v___x_1680_;
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___boxed(lean_object* v___x_1734_, lean_object* v_stx_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0(v___x_1734_, v_stx_1735_, v___y_1736_, v___y_1737_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
lean_dec_ref(v___x_1734_);
return v_res_1739_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__0(void){
_start:
{
lean_object* v___x_1740_; lean_object* v___f_1741_; 
v___x_1740_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___f_1741_ = lean_alloc_closure((void*)(l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___boxed), 5, 1);
lean_closure_set(v___f_1741_, 0, v___x_1740_);
return v___f_1741_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__1(void){
_start:
{
lean_object* v___f_1742_; lean_object* v___x_1743_; 
v___f_1742_ = lean_obj_once(&l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__0, &l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__0_once, _init_l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__0);
v___x_1743_ = lean_alloc_closure((void*)(l_Lean_withSetOptionIn___boxed), 6, 2);
lean_closure_set(v___x_1743_, 0, lean_box(0));
lean_closure_set(v___x_1743_, 1, v___f_1742_);
return v___x_1743_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__5(void){
_start:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1752_ = ((lean_object*)(l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__4));
v___x_1753_ = lean_obj_once(&l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__1, &l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__1_once, _init_l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__1);
v___x_1754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1753_);
lean_ctor_set(v___x_1754_, 1, v___x_1752_);
return v___x_1754_;
}
}
static lean_object* _init_l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter(void){
_start:
{
lean_object* v___x_1755_; 
v___x_1755_ = lean_obj_once(&l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__5, &l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__5_once, _init_l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__5);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1(lean_object* v_o_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v___x_1760_; 
v___x_1760_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1___redArg(v_o_1756_, v___y_1758_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1___boxed(lean_object* v_o_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1(v_o_1761_, v___y_1762_, v___y_1763_);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3(lean_object* v_00_u03b2_1766_, lean_object* v_x_1767_, lean_object* v_x_1768_){
_start:
{
lean_object* v___x_1769_; 
v___x_1769_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3___redArg(v_x_1767_, v_x_1768_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3___boxed(lean_object* v_00_u03b2_1770_, lean_object* v_x_1771_, lean_object* v_x_1772_){
_start:
{
lean_object* v_res_1773_; 
v_res_1773_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3(v_00_u03b2_1770_, v_x_1771_, v_x_1772_);
lean_dec(v_x_1772_);
lean_dec_ref(v_x_1771_);
return v_res_1773_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6(lean_object* v_n_1774_, lean_object* v_as_1775_, lean_object* v_lo_1776_, lean_object* v_hi_1777_, lean_object* v_w_1778_, lean_object* v_hlo_1779_, lean_object* v_hhi_1780_){
_start:
{
lean_object* v___x_1781_; 
v___x_1781_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg(v_n_1774_, v_as_1775_, v_lo_1776_, v_hi_1777_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___boxed(lean_object* v_n_1782_, lean_object* v_as_1783_, lean_object* v_lo_1784_, lean_object* v_hi_1785_, lean_object* v_w_1786_, lean_object* v_hlo_1787_, lean_object* v_hhi_1788_){
_start:
{
lean_object* v_res_1789_; 
v_res_1789_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6(v_n_1782_, v_as_1783_, v_lo_1784_, v_hi_1785_, v_w_1786_, v_hlo_1787_, v_hhi_1788_);
lean_dec(v_hi_1785_);
lean_dec(v_n_1782_);
return v_res_1789_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9(lean_object* v_00_u03b2_1790_, lean_object* v_x_1791_, lean_object* v_x_1792_){
_start:
{
uint8_t v___x_1793_; 
v___x_1793_ = l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9___redArg(v_x_1791_, v_x_1792_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9___boxed(lean_object* v_00_u03b2_1794_, lean_object* v_x_1795_, lean_object* v_x_1796_){
_start:
{
uint8_t v_res_1797_; lean_object* v_r_1798_; 
v_res_1797_ = l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9(v_00_u03b2_1794_, v_x_1795_, v_x_1796_);
lean_dec(v_x_1796_);
lean_dec_ref(v_x_1795_);
v_r_1798_ = lean_box(v_res_1797_);
return v_r_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5(lean_object* v_00_u03b2_1799_, lean_object* v_x_1800_, size_t v_x_1801_, lean_object* v_x_1802_){
_start:
{
lean_object* v___x_1803_; 
v___x_1803_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5___redArg(v_x_1800_, v_x_1801_, v_x_1802_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5___boxed(lean_object* v_00_u03b2_1804_, lean_object* v_x_1805_, lean_object* v_x_1806_, lean_object* v_x_1807_){
_start:
{
size_t v_x_12668__boxed_1808_; lean_object* v_res_1809_; 
v_x_12668__boxed_1808_ = lean_unbox_usize(v_x_1806_);
lean_dec(v_x_1806_);
v_res_1809_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5(v_00_u03b2_1804_, v_x_1805_, v_x_12668__boxed_1808_, v_x_1807_);
lean_dec(v_x_1807_);
lean_dec_ref(v_x_1805_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9(lean_object* v_n_1810_, lean_object* v_lo_1811_, lean_object* v_hi_1812_, lean_object* v_hhi_1813_, lean_object* v_pivot_1814_, lean_object* v_as_1815_, lean_object* v_i_1816_, lean_object* v_k_1817_, lean_object* v_ilo_1818_, lean_object* v_ik_1819_, lean_object* v_w_1820_){
_start:
{
lean_object* v___x_1821_; 
v___x_1821_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9___redArg(v_hi_1812_, v_pivot_1814_, v_as_1815_, v_i_1816_, v_k_1817_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9___boxed(lean_object* v_n_1822_, lean_object* v_lo_1823_, lean_object* v_hi_1824_, lean_object* v_hhi_1825_, lean_object* v_pivot_1826_, lean_object* v_as_1827_, lean_object* v_i_1828_, lean_object* v_k_1829_, lean_object* v_ilo_1830_, lean_object* v_ik_1831_, lean_object* v_w_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9(v_n_1822_, v_lo_1823_, v_hi_1824_, v_hhi_1825_, v_pivot_1826_, v_as_1827_, v_i_1828_, v_k_1829_, v_ilo_1830_, v_ik_1831_, v_w_1832_);
lean_dec(v_hi_1824_);
lean_dec(v_lo_1823_);
lean_dec(v_n_1822_);
return v_res_1833_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13(lean_object* v_00_u03b2_1834_, lean_object* v_x_1835_, size_t v_x_1836_, lean_object* v_x_1837_){
_start:
{
uint8_t v___x_1838_; 
v___x_1838_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg(v_x_1835_, v_x_1836_, v_x_1837_);
return v___x_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___boxed(lean_object* v_00_u03b2_1839_, lean_object* v_x_1840_, lean_object* v_x_1841_, lean_object* v_x_1842_){
_start:
{
size_t v_x_12681__boxed_1843_; uint8_t v_res_1844_; lean_object* v_r_1845_; 
v_x_12681__boxed_1843_ = lean_unbox_usize(v_x_1841_);
lean_dec(v_x_1841_);
v_res_1844_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13(v_00_u03b2_1839_, v_x_1840_, v_x_12681__boxed_1843_, v_x_1842_);
lean_dec(v_x_1842_);
lean_dec_ref(v_x_1840_);
v_r_1845_ = lean_box(v_res_1844_);
return v_r_1845_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15(lean_object* v_00_u03b2_1846_, lean_object* v_m_1847_, lean_object* v_a_1848_, lean_object* v_b_1849_){
_start:
{
lean_object* v___x_1850_; 
v___x_1850_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15___redArg(v_m_1847_, v_a_1848_, v_b_1849_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8(lean_object* v_00_u03b2_1851_, lean_object* v_keys_1852_, lean_object* v_vals_1853_, lean_object* v_heq_1854_, lean_object* v_i_1855_, lean_object* v_k_1856_){
_start:
{
lean_object* v___x_1857_; 
v___x_1857_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8___redArg(v_keys_1852_, v_vals_1853_, v_i_1855_, v_k_1856_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1858_, lean_object* v_keys_1859_, lean_object* v_vals_1860_, lean_object* v_heq_1861_, lean_object* v_i_1862_, lean_object* v_k_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8(v_00_u03b2_1858_, v_keys_1859_, v_vals_1860_, v_heq_1861_, v_i_1862_, v_k_1863_);
lean_dec(v_k_1863_);
lean_dec_ref(v_vals_1860_);
lean_dec_ref(v_keys_1859_);
return v_res_1864_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13_spec__16(lean_object* v_00_u03b2_1865_, lean_object* v_keys_1866_, lean_object* v_vals_1867_, lean_object* v_heq_1868_, lean_object* v_i_1869_, lean_object* v_k_1870_){
_start:
{
uint8_t v___x_1871_; 
v___x_1871_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13_spec__16___redArg(v_keys_1866_, v_i_1869_, v_k_1870_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13_spec__16___boxed(lean_object* v_00_u03b2_1872_, lean_object* v_keys_1873_, lean_object* v_vals_1874_, lean_object* v_heq_1875_, lean_object* v_i_1876_, lean_object* v_k_1877_){
_start:
{
uint8_t v_res_1878_; lean_object* v_r_1879_; 
v_res_1878_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13_spec__16(v_00_u03b2_1872_, v_keys_1873_, v_vals_1874_, v_heq_1875_, v_i_1876_, v_k_1877_);
lean_dec(v_k_1877_);
lean_dec_ref(v_vals_1874_);
lean_dec_ref(v_keys_1873_);
v_r_1879_ = lean_box(v_res_1878_);
return v_r_1879_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19(lean_object* v_00_u03b2_1880_, lean_object* v_data_1881_){
_start:
{
lean_object* v___x_1882_; 
v___x_1882_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19___redArg(v_data_1881_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__20(lean_object* v_00_u03b2_1883_, lean_object* v_a_1884_, lean_object* v_b_1885_, lean_object* v_x_1886_){
_start:
{
lean_object* v___x_1887_; 
v___x_1887_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__20___redArg(v_a_1884_, v_b_1885_, v_x_1886_);
return v___x_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19(lean_object* v_msgData_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v___x_1892_; 
v___x_1892_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg(v_msgData_1888_, v___y_1890_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___boxed(lean_object* v_msgData_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19(v_msgData_1893_, v___y_1894_, v___y_1895_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19_spec__21(lean_object* v_00_u03b2_1898_, lean_object* v_i_1899_, lean_object* v_source_1900_, lean_object* v_target_1901_){
_start:
{
lean_object* v___x_1902_; 
v___x_1902_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19_spec__21___redArg(v_i_1899_, v_source_1900_, v_target_1901_);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19_spec__21_spec__25(lean_object* v_00_u03b2_1903_, lean_object* v_x_1904_, lean_object* v_x_1905_){
_start:
{
lean_object* v___x_1906_; 
v___x_1906_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19_spec__21_spec__25___redArg(v_x_1904_, v_x_1905_);
return v___x_1906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_1366347041____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1908_ = l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter;
v___x_1909_ = l_Lean_Elab_Command_addLinter(v___x_1908_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_1366347041____hygCtx___hyg_2____boxed(lean_object* v_a_1910_){
_start:
{
lean_object* v_res_1911_; 
v_res_1911_ = l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_1366347041____hygCtx___hyg_2_();
return v_res_1911_;
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
