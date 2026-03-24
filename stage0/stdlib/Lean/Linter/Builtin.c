// Lean compiler output
// Module: Lean.Linter.Builtin
// Imports: public import Lean.Linter.Util public import Lean.Elab.Command
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
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Linter_linterSetsExt;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_matchesIdent(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Elab_Command_addLinter(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "suspiciousUnexpanderPatterns"};
static const lean_object* l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(128, 75, 2, 63, 36, 64, 134, 16)}};
static const lean_object* l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "enable the 'suspicious unexpander patterns' linter"};
static const lean_object* l_Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l_Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(53, 243, 121, 207, 53, 172, 203, 87)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(187, 83, 153, 174, 192, 198, 91, 54)}};
static const lean_object* l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_linter_suspiciousUnexpanderPatterns;
LEAN_EXPORT uint8_t l_Lean_Linter_getLinterSuspiciousUnexpanderPatterns(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterSuspiciousUnexpanderPatterns___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__3_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__3_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(241, 75, 242, 110, 47, 5, 20, 104)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__5_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__5_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__5_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__5_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__10___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "This linter can be disabled with `set_option "};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__0 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__0_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__1;
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " false`"};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__2 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__2_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__3;
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 142, .m_capacity = 142, .m_length = 141, .m_data = "Unexpanders should match the function name against an antiquotation `$_` so as to be independent of the specific pretty printing of the name."};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__2;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "quot"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__3_value),LEAN_SCALAR_PTR_LITERAL(145, 163, 173, 41, 168, 168, 65, 81)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__6_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__6_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__5_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__7_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__8_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(178, 0, 203, 112, 215, 49, 100, 229)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__6(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__2_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__2_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(107, 67, 254, 234, 65, 174, 209, 53)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "app_unexpander"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__3_value),LEAN_SCALAR_PTR_LITERAL(173, 94, 177, 152, 198, 163, 81, 20)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__4_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3(uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__0 = (const lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__0_value;
static const lean_string_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__1 = (const lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__2_value_aux_1),((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__2_value_aux_2),((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__2 = (const lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__2_value;
static const lean_string_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__3 = (const lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__4_value_aux_1),((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__4_value_aux_2),((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__4 = (const lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__4_value;
static const lean_string_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__5 = (const lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__5_value;
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__6_value_aux_1),((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__6_value_aux_2),((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(248, 187, 217, 228, 39, 184, 218, 135)}};
static const lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__6 = (const lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__6_value;
static const lean_string_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optDeclSig"};
static const lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__7 = (const lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__7_value;
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__8_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__8_value_aux_1),((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__8_value_aux_2),((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(26, 9, 103, 232, 183, 57, 246, 75)}};
static const lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__8 = (const lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__8_value;
static const lean_string_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__9 = (const lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__9_value;
static const lean_string_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declValEqns"};
static const lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__10 = (const lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__10_value;
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__11_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__11_value_aux_1),((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__11_value_aux_2),((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(185, 66, 113, 88, 174, 230, 155, 36)}};
static const lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__11 = (const lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__11_value;
static const lean_string_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "matchAltsWhereDecls"};
static const lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__12 = (const lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__12_value;
static const lean_string_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__13 = (const lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__13_value;
static const lean_string_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__14 = (const lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__14_value;
static const lean_string_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__15 = (const lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__15_value;
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__16_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__16_value_aux_1),((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__14_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__16_value_aux_2),((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__15_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__16 = (const lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__16_value;
static const lean_string_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__17 = (const lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__17_value;
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__18_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__18_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__18_value_aux_2),((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__17_value),LEAN_SCALAR_PTR_LITERAL(66, 184, 196, 169, 25, 125, 40, 35)}};
static const lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__18 = (const lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__18_value;
static const lean_array_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__19 = (const lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__19_value;
static const lean_string_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__20 = (const lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__20_value;
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__21_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__21_value_aux_1),((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__21_value_aux_2),((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__20_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__21 = (const lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__21_value;
LEAN_EXPORT lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Linter_suspiciousUnexpanderPatterns___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___closed__0 = (const lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___closed__0_value;
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___closed__1_value_aux_0),((lean_object*)&l_Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___closed__1_value_aux_1),((lean_object*)&l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(218, 57, 29, 215, 236, 35, 73, 76)}};
static const lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___closed__1 = (const lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___closed__1_value;
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___closed__0_value),((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___closed__1_value)}};
static const lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___closed__2 = (const lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns = (const lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1774244096____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1774244096____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_33_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_isSharedCheck_33_ = !lean_is_exclusive(v_decl_2_);
if (v_isSharedCheck_33_ == 0)
{
v___x_8_ = v_decl_2_;
v_isShared_9_ = v_isSharedCheck_33_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_descr_6_);
lean_inc(v_defValue_5_);
lean_dec(v_decl_2_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_33_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_10_; uint8_t v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_10_ = lean_alloc_ctor(1, 0, 1);
v___x_11_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_10_, 0, v___x_11_);
lean_inc(v_name_1_);
v___x_12_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_12_, 0, v_name_1_);
lean_ctor_set(v___x_12_, 1, v_ref_3_);
lean_ctor_set(v___x_12_, 2, v___x_10_);
lean_ctor_set(v___x_12_, 3, v_descr_6_);
lean_inc(v_name_1_);
v___x_13_ = lean_register_option(v_name_1_, v___x_12_);
if (lean_obj_tag(v___x_13_) == 0)
{
lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_23_; 
v_isSharedCheck_23_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_23_ == 0)
{
lean_object* v_unused_24_; 
v_unused_24_ = lean_ctor_get(v___x_13_, 0);
lean_dec(v_unused_24_);
v___x_15_ = v___x_13_;
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
else
{
lean_dec(v___x_13_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v___x_18_; 
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 1, v_defValue_5_);
lean_ctor_set(v___x_8_, 0, v_name_1_);
v___x_18_ = v___x_8_;
goto v_reusejp_17_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v_name_1_);
lean_ctor_set(v_reuseFailAlloc_22_, 1, v_defValue_5_);
v___x_18_ = v_reuseFailAlloc_22_;
goto v_reusejp_17_;
}
v_reusejp_17_:
{
lean_object* v___x_20_; 
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 0, v___x_18_);
v___x_20_ = v___x_15_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v___x_18_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
}
}
else
{
lean_object* v_a_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_32_; 
lean_del_object(v___x_8_);
lean_dec(v_defValue_5_);
lean_dec(v_name_1_);
v_a_25_ = lean_ctor_get(v___x_13_, 0);
v_isSharedCheck_32_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_32_ == 0)
{
v___x_27_ = v___x_13_;
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_a_25_);
lean_dec(v___x_13_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v___x_30_; 
if (v_isShared_28_ == 0)
{
v___x_30_ = v___x_27_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v_a_25_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_34_, lean_object* v_decl_35_, lean_object* v_ref_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Option_register___at___00Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__spec__0(v_name_34_, v_decl_35_, v_ref_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_57_ = ((lean_object*)(l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_));
v___x_58_ = ((lean_object*)(l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_));
v___x_59_ = ((lean_object*)(l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_));
v___x_60_ = l_Lean_Option_register___at___00Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__spec__0(v___x_57_, v___x_58_, v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4____boxed(lean_object* v_a_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_();
return v_res_62_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_getLinterSuspiciousUnexpanderPatterns(lean_object* v_o_63_){
_start:
{
lean_object* v___x_64_; uint8_t v___x_65_; 
v___x_64_ = l_Lean_Linter_linter_suspiciousUnexpanderPatterns;
v___x_65_ = l_Lean_Linter_getLinterValue(v___x_64_, v_o_63_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterSuspiciousUnexpanderPatterns___boxed(lean_object* v_o_66_){
_start:
{
uint8_t v_res_67_; lean_object* v_r_68_; 
v_res_67_ = l_Lean_Linter_getLinterSuspiciousUnexpanderPatterns(v_o_66_);
lean_dec_ref(v_o_66_);
v_r_68_ = lean_box(v_res_67_);
return v_r_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0___redArg(lean_object* v_o_69_, lean_object* v___y_70_){
_start:
{
lean_object* v___x_72_; lean_object* v_env_73_; lean_object* v___x_74_; lean_object* v_toEnvExtension_75_; lean_object* v_asyncMode_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v_linterSets_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_72_ = lean_st_ref_get(v___y_70_);
v_env_73_ = lean_ctor_get(v___x_72_, 0);
lean_inc_ref(v_env_73_);
lean_dec(v___x_72_);
v___x_74_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_75_ = lean_ctor_get(v___x_74_, 0);
lean_inc_ref(v_toEnvExtension_75_);
v_asyncMode_76_ = lean_ctor_get(v_toEnvExtension_75_, 2);
lean_inc(v_asyncMode_76_);
lean_dec_ref(v_toEnvExtension_75_);
v___x_77_ = lean_box(1);
v___x_78_ = lean_box(0);
v_linterSets_79_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_77_, v___x_74_, v_env_73_, v_asyncMode_76_, v___x_78_);
lean_dec(v_asyncMode_76_);
v___x_80_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_80_, 0, v_o_69_);
lean_ctor_set(v___x_80_, 1, v_linterSets_79_);
v___x_81_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0___redArg___boxed(lean_object* v_o_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0___redArg(v_o_82_, v___y_83_);
lean_dec(v___y_83_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0(lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
lean_object* v___x_89_; lean_object* v_scopes_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v_opts_93_; lean_object* v___x_94_; 
v___x_89_ = lean_st_ref_get(v___y_87_);
v_scopes_90_ = lean_ctor_get(v___x_89_, 2);
lean_inc(v_scopes_90_);
lean_dec(v___x_89_);
v___x_91_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_92_ = l_List_head_x21___redArg(v___x_91_, v_scopes_90_);
lean_dec(v_scopes_90_);
v_opts_93_ = lean_ctor_get(v___x_92_, 1);
lean_inc_ref(v_opts_93_);
lean_dec(v___x_92_);
v___x_94_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0___redArg(v_opts_93_, v___y_87_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0___boxed(lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0(v___y_95_, v___y_96_);
lean_dec(v___y_96_);
lean_dec_ref(v___y_95_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1(size_t v_sz_113_, size_t v_i_114_, lean_object* v_bs_115_){
_start:
{
uint8_t v___x_116_; 
v___x_116_ = lean_usize_dec_lt(v_i_114_, v_sz_113_);
if (v___x_116_ == 0)
{
lean_object* v___x_117_; 
v___x_117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_117_, 0, v_bs_115_);
return v___x_117_;
}
else
{
lean_object* v_v_118_; lean_object* v___x_119_; uint8_t v___x_120_; 
v_v_118_ = lean_array_uget(v_bs_115_, v_i_114_);
v___x_119_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__3));
lean_inc(v_v_118_);
v___x_120_ = l_Lean_Syntax_isOfKind(v_v_118_, v___x_119_);
if (v___x_120_ == 0)
{
lean_object* v___x_121_; 
lean_dec(v_v_118_);
lean_dec_ref(v_bs_115_);
v___x_121_ = lean_box(0);
return v___x_121_;
}
else
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_122_ = lean_unsigned_to_nat(0u);
v___x_123_ = l_Lean_Syntax_getArg(v_v_118_, v___x_122_);
v___x_124_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__5));
lean_inc(v___x_123_);
v___x_125_ = l_Lean_Syntax_isOfKind(v___x_123_, v___x_124_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; 
lean_dec(v___x_123_);
lean_dec(v_v_118_);
lean_dec_ref(v_bs_115_);
v___x_126_ = lean_box(0);
return v___x_126_;
}
else
{
lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_127_ = l_Lean_Syntax_getArg(v___x_123_, v___x_122_);
lean_dec(v___x_123_);
v___x_128_ = l_Lean_Syntax_matchesNull(v___x_127_, v___x_122_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; 
lean_dec(v_v_118_);
lean_dec_ref(v_bs_115_);
v___x_129_ = lean_box(0);
return v___x_129_;
}
else
{
lean_object* v___x_130_; lean_object* v_bs_x27_131_; lean_object* v___x_132_; size_t v___x_133_; size_t v___x_134_; lean_object* v___x_135_; 
v___x_130_ = lean_unsigned_to_nat(1u);
v_bs_x27_131_ = lean_array_uset(v_bs_115_, v_i_114_, v___x_122_);
v___x_132_ = l_Lean_Syntax_getArg(v_v_118_, v___x_130_);
lean_dec(v_v_118_);
v___x_133_ = ((size_t)1ULL);
v___x_134_ = lean_usize_add(v_i_114_, v___x_133_);
v___x_135_ = lean_array_uset(v_bs_x27_131_, v_i_114_, v___x_132_);
v_i_114_ = v___x_134_;
v_bs_115_ = v___x_135_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___boxed(lean_object* v_sz_137_, lean_object* v_i_138_, lean_object* v_bs_139_){
_start:
{
size_t v_sz_boxed_140_; size_t v_i_boxed_141_; lean_object* v_res_142_; 
v_sz_boxed_140_ = lean_unbox_usize(v_sz_137_);
lean_dec(v_sz_137_);
v_i_boxed_141_ = lean_unbox_usize(v_i_138_);
lean_dec(v_i_138_);
v_res_142_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1(v_sz_boxed_140_, v_i_boxed_141_, v_bs_139_);
return v_res_142_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__10(lean_object* v_opts_143_, lean_object* v_opt_144_){
_start:
{
lean_object* v_name_145_; lean_object* v_defValue_146_; lean_object* v_map_147_; lean_object* v___x_148_; 
v_name_145_ = lean_ctor_get(v_opt_144_, 0);
v_defValue_146_ = lean_ctor_get(v_opt_144_, 1);
v_map_147_ = lean_ctor_get(v_opts_143_, 0);
v___x_148_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_147_, v_name_145_);
if (lean_obj_tag(v___x_148_) == 0)
{
uint8_t v___x_149_; 
v___x_149_ = lean_unbox(v_defValue_146_);
return v___x_149_;
}
else
{
lean_object* v_val_150_; 
v_val_150_ = lean_ctor_get(v___x_148_, 0);
lean_inc(v_val_150_);
lean_dec_ref(v___x_148_);
if (lean_obj_tag(v_val_150_) == 1)
{
uint8_t v_v_151_; 
v_v_151_ = lean_ctor_get_uint8(v_val_150_, 0);
lean_dec_ref(v_val_150_);
return v_v_151_;
}
else
{
uint8_t v___x_152_; 
lean_dec(v_val_150_);
v___x_152_ = lean_unbox(v_defValue_146_);
return v___x_152_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__10___boxed(lean_object* v_opts_153_, lean_object* v_opt_154_){
_start:
{
uint8_t v_res_155_; lean_object* v_r_156_; 
v_res_155_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__10(v_opts_153_, v_opt_154_);
lean_dec_ref(v_opt_154_);
lean_dec_ref(v_opts_153_);
v_r_156_ = lean_box(v_res_155_);
return v_r_156_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_157_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_158_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__0);
v___x_159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
return v___x_159_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_160_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1);
v___x_161_ = lean_unsigned_to_nat(0u);
v___x_162_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
lean_ctor_set(v___x_162_, 1, v___x_161_);
lean_ctor_set(v___x_162_, 2, v___x_161_);
lean_ctor_set(v___x_162_, 3, v___x_160_);
lean_ctor_set(v___x_162_, 4, v___x_160_);
lean_ctor_set(v___x_162_, 5, v___x_160_);
lean_ctor_set(v___x_162_, 6, v___x_160_);
lean_ctor_set(v___x_162_, 7, v___x_160_);
lean_ctor_set(v___x_162_, 8, v___x_160_);
return v___x_162_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_163_ = lean_unsigned_to_nat(32u);
v___x_164_ = lean_mk_empty_array_with_capacity(v___x_163_);
v___x_165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
return v___x_165_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__4(void){
_start:
{
size_t v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_166_ = ((size_t)5ULL);
v___x_167_ = lean_unsigned_to_nat(0u);
v___x_168_ = lean_unsigned_to_nat(32u);
v___x_169_ = lean_mk_empty_array_with_capacity(v___x_168_);
v___x_170_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__3);
v___x_171_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_171_, 0, v___x_170_);
lean_ctor_set(v___x_171_, 1, v___x_169_);
lean_ctor_set(v___x_171_, 2, v___x_167_);
lean_ctor_set(v___x_171_, 3, v___x_167_);
lean_ctor_set_usize(v___x_171_, 4, v___x_166_);
return v___x_171_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_172_ = lean_box(1);
v___x_173_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__4);
v___x_174_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1);
v___x_175_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
lean_ctor_set(v___x_175_, 1, v___x_173_);
lean_ctor_set(v___x_175_, 2, v___x_172_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg(lean_object* v_msgData_176_, lean_object* v___y_177_){
_start:
{
lean_object* v___x_179_; lean_object* v_env_180_; lean_object* v___x_181_; lean_object* v_scopes_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v_opts_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_179_ = lean_st_ref_get(v___y_177_);
v_env_180_ = lean_ctor_get(v___x_179_, 0);
lean_inc_ref(v_env_180_);
lean_dec(v___x_179_);
v___x_181_ = lean_st_ref_get(v___y_177_);
v_scopes_182_ = lean_ctor_get(v___x_181_, 2);
lean_inc(v_scopes_182_);
lean_dec(v___x_181_);
v___x_183_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_184_ = l_List_head_x21___redArg(v___x_183_, v_scopes_182_);
lean_dec(v_scopes_182_);
v_opts_185_ = lean_ctor_get(v___x_184_, 1);
lean_inc_ref(v_opts_185_);
lean_dec(v___x_184_);
v___x_186_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__2);
v___x_187_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__5);
v___x_188_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_188_, 0, v_env_180_);
lean_ctor_set(v___x_188_, 1, v___x_186_);
lean_ctor_set(v___x_188_, 2, v___x_187_);
lean_ctor_set(v___x_188_, 3, v_opts_185_);
v___x_189_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
lean_ctor_set(v___x_189_, 1, v_msgData_176_);
v___x_190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___boxed(lean_object* v_msgData_191_, lean_object* v___y_192_, lean_object* v___y_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg(v_msgData_191_, v___y_192_);
lean_dec(v___y_192_);
return v_res_194_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0(uint8_t v___y_196_, uint8_t v_suppressElabErrors_197_, lean_object* v_x_198_){
_start:
{
if (lean_obj_tag(v_x_198_) == 1)
{
lean_object* v_pre_199_; 
v_pre_199_ = lean_ctor_get(v_x_198_, 0);
if (lean_obj_tag(v_pre_199_) == 0)
{
lean_object* v_str_200_; lean_object* v___x_201_; uint8_t v___x_202_; 
v_str_200_ = lean_ctor_get(v_x_198_, 1);
v___x_201_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0___closed__0));
v___x_202_ = lean_string_dec_eq(v_str_200_, v___x_201_);
if (v___x_202_ == 0)
{
return v___y_196_;
}
else
{
return v_suppressElabErrors_197_;
}
}
else
{
return v___y_196_;
}
}
else
{
return v___y_196_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0___boxed(lean_object* v___y_203_, lean_object* v_suppressElabErrors_204_, lean_object* v_x_205_){
_start:
{
uint8_t v___y_26019__boxed_206_; uint8_t v_suppressElabErrors_boxed_207_; uint8_t v_res_208_; lean_object* v_r_209_; 
v___y_26019__boxed_206_ = lean_unbox(v___y_203_);
v_suppressElabErrors_boxed_207_ = lean_unbox(v_suppressElabErrors_204_);
v_res_208_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0(v___y_26019__boxed_206_, v_suppressElabErrors_boxed_207_, v_x_205_);
lean_dec(v_x_205_);
v_r_209_ = lean_box(v_res_208_);
return v_r_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6(lean_object* v_ref_211_, lean_object* v_msgData_212_, uint8_t v_severity_213_, uint8_t v_isSilent_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
lean_object* v___y_219_; lean_object* v___y_220_; uint8_t v___y_221_; lean_object* v___y_222_; uint8_t v___y_223_; lean_object* v___y_224_; lean_object* v___y_225_; lean_object* v___y_226_; uint8_t v___y_282_; uint8_t v___y_283_; lean_object* v___y_284_; uint8_t v___y_285_; lean_object* v___y_286_; uint8_t v___y_310_; lean_object* v___y_311_; uint8_t v___y_312_; uint8_t v___y_313_; lean_object* v___y_314_; uint8_t v___y_318_; uint8_t v___y_319_; uint8_t v___y_320_; uint8_t v___x_335_; uint8_t v___y_337_; uint8_t v___y_338_; uint8_t v___y_339_; uint8_t v___y_341_; uint8_t v___x_353_; 
v___x_335_ = 2;
v___x_353_ = l_Lean_instBEqMessageSeverity_beq(v_severity_213_, v___x_335_);
if (v___x_353_ == 0)
{
v___y_341_ = v___x_353_;
goto v___jp_340_;
}
else
{
uint8_t v___x_354_; 
lean_inc_ref(v_msgData_212_);
v___x_354_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_212_);
v___y_341_ = v___x_354_;
goto v___jp_340_;
}
v___jp_218_:
{
lean_object* v___x_227_; 
v___x_227_ = l_Lean_Elab_Command_getScope___redArg(v___y_226_);
if (lean_obj_tag(v___x_227_) == 0)
{
lean_object* v_a_228_; lean_object* v___x_229_; 
v_a_228_ = lean_ctor_get(v___x_227_, 0);
lean_inc(v_a_228_);
lean_dec_ref(v___x_227_);
v___x_229_ = l_Lean_Elab_Command_getScope___redArg(v___y_226_);
if (lean_obj_tag(v___x_229_) == 0)
{
lean_object* v_a_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_264_; 
v_a_230_ = lean_ctor_get(v___x_229_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_264_ == 0)
{
v___x_232_ = v___x_229_;
v_isShared_233_ = v_isSharedCheck_264_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_a_230_);
lean_dec(v___x_229_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_264_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_234_; lean_object* v_currNamespace_235_; lean_object* v_openDecls_236_; lean_object* v_env_237_; lean_object* v_messages_238_; lean_object* v_scopes_239_; lean_object* v_usedQuotCtxts_240_; lean_object* v_nextMacroScope_241_; lean_object* v_maxRecDepth_242_; lean_object* v_ngen_243_; lean_object* v_auxDeclNGen_244_; lean_object* v_infoState_245_; lean_object* v_traceState_246_; lean_object* v_snapshotTasks_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_263_; 
v___x_234_ = lean_st_ref_take(v___y_226_);
v_currNamespace_235_ = lean_ctor_get(v_a_228_, 2);
lean_inc(v_currNamespace_235_);
lean_dec(v_a_228_);
v_openDecls_236_ = lean_ctor_get(v_a_230_, 3);
lean_inc(v_openDecls_236_);
lean_dec(v_a_230_);
v_env_237_ = lean_ctor_get(v___x_234_, 0);
v_messages_238_ = lean_ctor_get(v___x_234_, 1);
v_scopes_239_ = lean_ctor_get(v___x_234_, 2);
v_usedQuotCtxts_240_ = lean_ctor_get(v___x_234_, 3);
v_nextMacroScope_241_ = lean_ctor_get(v___x_234_, 4);
v_maxRecDepth_242_ = lean_ctor_get(v___x_234_, 5);
v_ngen_243_ = lean_ctor_get(v___x_234_, 6);
v_auxDeclNGen_244_ = lean_ctor_get(v___x_234_, 7);
v_infoState_245_ = lean_ctor_get(v___x_234_, 8);
v_traceState_246_ = lean_ctor_get(v___x_234_, 9);
v_snapshotTasks_247_ = lean_ctor_get(v___x_234_, 10);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_263_ == 0)
{
v___x_249_ = v___x_234_;
v_isShared_250_ = v_isSharedCheck_263_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_snapshotTasks_247_);
lean_inc(v_traceState_246_);
lean_inc(v_infoState_245_);
lean_inc(v_auxDeclNGen_244_);
lean_inc(v_ngen_243_);
lean_inc(v_maxRecDepth_242_);
lean_inc(v_nextMacroScope_241_);
lean_inc(v_usedQuotCtxts_240_);
lean_inc(v_scopes_239_);
lean_inc(v_messages_238_);
lean_inc(v_env_237_);
lean_dec(v___x_234_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_263_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_256_; 
v___x_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_251_, 0, v_currNamespace_235_);
lean_ctor_set(v___x_251_, 1, v_openDecls_236_);
v___x_252_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
lean_ctor_set(v___x_252_, 1, v___y_224_);
v___x_253_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_253_, 0, v___y_222_);
lean_ctor_set(v___x_253_, 1, v___y_220_);
lean_ctor_set(v___x_253_, 2, v___y_219_);
lean_ctor_set(v___x_253_, 3, v___y_225_);
lean_ctor_set(v___x_253_, 4, v___x_252_);
lean_ctor_set_uint8(v___x_253_, sizeof(void*)*5, v___y_221_);
lean_ctor_set_uint8(v___x_253_, sizeof(void*)*5 + 1, v___y_223_);
lean_ctor_set_uint8(v___x_253_, sizeof(void*)*5 + 2, v_isSilent_214_);
v___x_254_ = l_Lean_MessageLog_add(v___x_253_, v_messages_238_);
if (v_isShared_250_ == 0)
{
lean_ctor_set(v___x_249_, 1, v___x_254_);
v___x_256_ = v___x_249_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_env_237_);
lean_ctor_set(v_reuseFailAlloc_262_, 1, v___x_254_);
lean_ctor_set(v_reuseFailAlloc_262_, 2, v_scopes_239_);
lean_ctor_set(v_reuseFailAlloc_262_, 3, v_usedQuotCtxts_240_);
lean_ctor_set(v_reuseFailAlloc_262_, 4, v_nextMacroScope_241_);
lean_ctor_set(v_reuseFailAlloc_262_, 5, v_maxRecDepth_242_);
lean_ctor_set(v_reuseFailAlloc_262_, 6, v_ngen_243_);
lean_ctor_set(v_reuseFailAlloc_262_, 7, v_auxDeclNGen_244_);
lean_ctor_set(v_reuseFailAlloc_262_, 8, v_infoState_245_);
lean_ctor_set(v_reuseFailAlloc_262_, 9, v_traceState_246_);
lean_ctor_set(v_reuseFailAlloc_262_, 10, v_snapshotTasks_247_);
v___x_256_ = v_reuseFailAlloc_262_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_260_; 
v___x_257_ = lean_st_ref_set(v___y_226_, v___x_256_);
v___x_258_ = lean_box(0);
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 0, v___x_258_);
v___x_260_ = v___x_232_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_258_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
}
}
else
{
lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_272_; 
lean_dec(v_a_228_);
lean_dec_ref(v___y_225_);
lean_dec_ref(v___y_224_);
lean_dec_ref(v___y_222_);
lean_dec_ref(v___y_220_);
lean_dec(v___y_219_);
v_a_265_ = lean_ctor_get(v___x_229_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_272_ == 0)
{
v___x_267_ = v___x_229_;
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_dec(v___x_229_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_270_; 
if (v_isShared_268_ == 0)
{
v___x_270_ = v___x_267_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_a_265_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
else
{
lean_object* v_a_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_280_; 
lean_dec_ref(v___y_225_);
lean_dec_ref(v___y_224_);
lean_dec_ref(v___y_222_);
lean_dec_ref(v___y_220_);
lean_dec(v___y_219_);
v_a_273_ = lean_ctor_get(v___x_227_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_280_ == 0)
{
v___x_275_ = v___x_227_;
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_a_273_);
lean_dec(v___x_227_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_278_; 
if (v_isShared_276_ == 0)
{
v___x_278_ = v___x_275_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_a_273_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
}
v___jp_281_:
{
lean_object* v_fileName_287_; lean_object* v_fileMap_288_; uint8_t v_suppressElabErrors_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v_a_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_308_; 
v_fileName_287_ = lean_ctor_get(v___y_215_, 0);
lean_inc_ref(v_fileName_287_);
v_fileMap_288_ = lean_ctor_get(v___y_215_, 1);
lean_inc_ref(v_fileMap_288_);
v_suppressElabErrors_289_ = lean_ctor_get_uint8(v___y_215_, sizeof(void*)*10);
lean_dec_ref(v___y_215_);
v___x_290_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_212_);
v___x_291_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg(v___x_290_, v___y_216_);
v_a_292_ = lean_ctor_get(v___x_291_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_291_);
if (v_isSharedCheck_308_ == 0)
{
v___x_294_ = v___x_291_;
v_isShared_295_ = v_isSharedCheck_308_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_a_292_);
lean_dec(v___x_291_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_308_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
lean_inc_ref(v_fileMap_288_);
v___x_296_ = l_Lean_FileMap_toPosition(v_fileMap_288_, v___y_284_);
lean_dec(v___y_284_);
v___x_297_ = l_Lean_FileMap_toPosition(v_fileMap_288_, v___y_286_);
lean_dec(v___y_286_);
v___x_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
v___x_299_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___closed__0));
if (v_suppressElabErrors_289_ == 0)
{
lean_del_object(v___x_294_);
v___y_219_ = v___x_298_;
v___y_220_ = v___x_296_;
v___y_221_ = v___y_283_;
v___y_222_ = v_fileName_287_;
v___y_223_ = v___y_285_;
v___y_224_ = v_a_292_;
v___y_225_ = v___x_299_;
v___y_226_ = v___y_216_;
goto v___jp_218_;
}
else
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___f_302_; uint8_t v___x_303_; 
v___x_300_ = lean_box(v___y_282_);
v___x_301_ = lean_box(v_suppressElabErrors_289_);
v___f_302_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0___boxed), 3, 2);
lean_closure_set(v___f_302_, 0, v___x_300_);
lean_closure_set(v___f_302_, 1, v___x_301_);
lean_inc(v_a_292_);
v___x_303_ = l_Lean_MessageData_hasTag(v___f_302_, v_a_292_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; lean_object* v___x_306_; 
lean_dec_ref(v___x_298_);
lean_dec_ref(v___x_296_);
lean_dec(v_a_292_);
lean_dec_ref(v_fileName_287_);
v___x_304_ = lean_box(0);
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 0, v___x_304_);
v___x_306_ = v___x_294_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v___x_304_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
else
{
lean_del_object(v___x_294_);
v___y_219_ = v___x_298_;
v___y_220_ = v___x_296_;
v___y_221_ = v___y_283_;
v___y_222_ = v_fileName_287_;
v___y_223_ = v___y_285_;
v___y_224_ = v_a_292_;
v___y_225_ = v___x_299_;
v___y_226_ = v___y_216_;
goto v___jp_218_;
}
}
}
}
v___jp_309_:
{
lean_object* v___x_315_; 
v___x_315_ = l_Lean_Syntax_getTailPos_x3f(v___y_311_, v___y_312_);
lean_dec(v___y_311_);
if (lean_obj_tag(v___x_315_) == 0)
{
lean_inc(v___y_314_);
v___y_282_ = v___y_310_;
v___y_283_ = v___y_312_;
v___y_284_ = v___y_314_;
v___y_285_ = v___y_313_;
v___y_286_ = v___y_314_;
goto v___jp_281_;
}
else
{
lean_object* v_val_316_; 
v_val_316_ = lean_ctor_get(v___x_315_, 0);
lean_inc(v_val_316_);
lean_dec_ref(v___x_315_);
v___y_282_ = v___y_310_;
v___y_283_ = v___y_312_;
v___y_284_ = v___y_314_;
v___y_285_ = v___y_313_;
v___y_286_ = v_val_316_;
goto v___jp_281_;
}
}
v___jp_317_:
{
lean_object* v___x_321_; 
v___x_321_ = l_Lean_Elab_Command_getRef___redArg(v___y_215_);
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v_a_322_; lean_object* v_ref_323_; lean_object* v___x_324_; 
v_a_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_a_322_);
lean_dec_ref(v___x_321_);
v_ref_323_ = l_Lean_replaceRef(v_ref_211_, v_a_322_);
lean_dec(v_a_322_);
v___x_324_ = l_Lean_Syntax_getPos_x3f(v_ref_323_, v___y_319_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v___x_325_; 
v___x_325_ = lean_unsigned_to_nat(0u);
v___y_310_ = v___y_318_;
v___y_311_ = v_ref_323_;
v___y_312_ = v___y_319_;
v___y_313_ = v___y_320_;
v___y_314_ = v___x_325_;
goto v___jp_309_;
}
else
{
lean_object* v_val_326_; 
v_val_326_ = lean_ctor_get(v___x_324_, 0);
lean_inc(v_val_326_);
lean_dec_ref(v___x_324_);
v___y_310_ = v___y_318_;
v___y_311_ = v_ref_323_;
v___y_312_ = v___y_319_;
v___y_313_ = v___y_320_;
v___y_314_ = v_val_326_;
goto v___jp_309_;
}
}
else
{
lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_334_; 
lean_dec_ref(v___y_215_);
lean_dec_ref(v_msgData_212_);
v_a_327_ = lean_ctor_get(v___x_321_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_334_ == 0)
{
v___x_329_ = v___x_321_;
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v___x_321_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_332_; 
if (v_isShared_330_ == 0)
{
v___x_332_ = v___x_329_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_a_327_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
}
v___jp_336_:
{
if (v___y_339_ == 0)
{
v___y_318_ = v___y_337_;
v___y_319_ = v___y_338_;
v___y_320_ = v_severity_213_;
goto v___jp_317_;
}
else
{
v___y_318_ = v___y_337_;
v___y_319_ = v___y_338_;
v___y_320_ = v___x_335_;
goto v___jp_317_;
}
}
v___jp_340_:
{
if (v___y_341_ == 0)
{
lean_object* v___x_342_; lean_object* v_scopes_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v_opts_346_; uint8_t v___x_347_; uint8_t v___x_348_; 
v___x_342_ = lean_st_ref_get(v___y_216_);
v_scopes_343_ = lean_ctor_get(v___x_342_, 2);
lean_inc(v_scopes_343_);
lean_dec(v___x_342_);
v___x_344_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_345_ = l_List_head_x21___redArg(v___x_344_, v_scopes_343_);
lean_dec(v_scopes_343_);
v_opts_346_ = lean_ctor_get(v___x_345_, 1);
lean_inc_ref(v_opts_346_);
lean_dec(v___x_345_);
v___x_347_ = 1;
v___x_348_ = l_Lean_instBEqMessageSeverity_beq(v_severity_213_, v___x_347_);
if (v___x_348_ == 0)
{
lean_dec_ref(v_opts_346_);
v___y_337_ = v___y_341_;
v___y_338_ = v___y_341_;
v___y_339_ = v___x_348_;
goto v___jp_336_;
}
else
{
lean_object* v___x_349_; uint8_t v___x_350_; 
v___x_349_ = l_Lean_warningAsError;
v___x_350_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__10(v_opts_346_, v___x_349_);
lean_dec_ref(v_opts_346_);
v___y_337_ = v___y_341_;
v___y_338_ = v___y_341_;
v___y_339_ = v___x_350_;
goto v___jp_336_;
}
}
else
{
lean_object* v___x_351_; lean_object* v___x_352_; 
lean_dec_ref(v___y_215_);
lean_dec_ref(v_msgData_212_);
v___x_351_ = lean_box(0);
v___x_352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_352_, 0, v___x_351_);
return v___x_352_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___boxed(lean_object* v_ref_355_, lean_object* v_msgData_356_, lean_object* v_severity_357_, lean_object* v_isSilent_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
uint8_t v_severity_boxed_362_; uint8_t v_isSilent_boxed_363_; lean_object* v_res_364_; 
v_severity_boxed_362_ = lean_unbox(v_severity_357_);
v_isSilent_boxed_363_ = lean_unbox(v_isSilent_358_);
v_res_364_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6(v_ref_355_, v_msgData_356_, v_severity_boxed_362_, v_isSilent_boxed_363_, v___y_359_, v___y_360_);
lean_dec(v___y_360_);
lean_dec(v_ref_355_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5(lean_object* v_ref_365_, lean_object* v_msgData_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
uint8_t v___x_370_; uint8_t v___x_371_; lean_object* v___x_372_; 
v___x_370_ = 1;
v___x_371_ = 0;
lean_inc_ref(v___y_367_);
v___x_372_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6(v_ref_365_, v_msgData_366_, v___x_370_, v___x_371_, v___y_367_, v___y_368_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5___boxed(lean_object* v_ref_373_, lean_object* v_msgData_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5(v_ref_373_, v_msgData_374_, v___y_375_, v___y_376_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
lean_dec(v_ref_373_);
return v_res_378_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__1(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__0));
v___x_381_ = l_Lean_stringToMessageData(v___x_380_);
return v___x_381_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__3(void){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__2));
v___x_384_ = l_Lean_stringToMessageData(v___x_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4(lean_object* v_linterOption_385_, lean_object* v_stx_386_, lean_object* v_msg_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_name_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_406_; 
v_name_391_ = lean_ctor_get(v_linterOption_385_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v_linterOption_385_);
if (v_isSharedCheck_406_ == 0)
{
lean_object* v_unused_407_; 
v_unused_407_ = lean_ctor_get(v_linterOption_385_, 1);
lean_dec(v_unused_407_);
v___x_393_ = v_linterOption_385_;
v_isShared_394_ = v_isSharedCheck_406_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_name_391_);
lean_dec(v_linterOption_385_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_406_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_398_; 
v___x_395_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__1);
lean_inc(v_name_391_);
v___x_396_ = l_Lean_MessageData_ofName(v_name_391_);
if (v_isShared_394_ == 0)
{
lean_ctor_set_tag(v___x_393_, 7);
lean_ctor_set(v___x_393_, 1, v___x_396_);
lean_ctor_set(v___x_393_, 0, v___x_395_);
v___x_398_ = v___x_393_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_395_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v___x_396_);
v___x_398_ = v_reuseFailAlloc_405_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v_disable_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_399_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__3);
v___x_400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_400_, 0, v___x_398_);
lean_ctor_set(v___x_400_, 1, v___x_399_);
v_disable_401_ = l_Lean_MessageData_note(v___x_400_);
v___x_402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_402_, 0, v_msg_387_);
lean_ctor_set(v___x_402_, 1, v_disable_401_);
v___x_403_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_403_, 0, v_name_391_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
v___x_404_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5(v_stx_386_, v___x_403_, v___y_388_, v___y_389_);
return v___x_404_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___boxed(lean_object* v_linterOption_408_, lean_object* v_stx_409_, lean_object* v_msg_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4(v_linterOption_408_, v_stx_409_, v_msg_410_, v___y_411_, v___y_412_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
lean_dec(v_stx_409_);
return v_res_414_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__2(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__1));
v___x_419_ = l_Lean_MessageData_ofFormat(v___x_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5(lean_object* v_as_435_, size_t v_sz_436_, size_t v_i_437_, lean_object* v_b_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
lean_object* v_a_443_; uint8_t v___x_447_; 
v___x_447_ = lean_usize_dec_lt(v_i_437_, v_sz_436_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; 
v___x_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_448_, 0, v_b_438_);
return v___x_448_;
}
else
{
lean_object* v___x_449_; lean_object* v_patHead_451_; lean_object* v___y_452_; lean_object* v___y_453_; lean_object* v_a_457_; lean_object* v___x_458_; uint8_t v___x_459_; 
v___x_449_ = lean_box(0);
v_a_457_ = lean_array_uget_borrowed(v_as_435_, v_i_437_);
v___x_458_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__4));
lean_inc(v_a_457_);
v___x_459_ = l_Lean_Syntax_isOfKind(v_a_457_, v___x_458_);
if (v___x_459_ == 0)
{
v_a_443_ = v___x_449_;
goto v___jp_442_;
}
else
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; uint8_t v___x_463_; 
v___x_460_ = lean_unsigned_to_nat(1u);
v___x_461_ = l_Lean_Syntax_getArg(v_a_457_, v___x_460_);
v___x_462_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__6));
lean_inc(v___x_461_);
v___x_463_ = l_Lean_Syntax_isOfKind(v___x_461_, v___x_462_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; uint8_t v___x_465_; 
v___x_464_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__8));
lean_inc(v___x_461_);
v___x_465_ = l_Lean_Syntax_isOfKind(v___x_461_, v___x_464_);
if (v___x_465_ == 0)
{
lean_dec(v___x_461_);
v_a_443_ = v___x_449_;
goto v___jp_442_;
}
else
{
v_patHead_451_ = v___x_461_;
v___y_452_ = v___y_439_;
v___y_453_ = v___y_440_;
goto v___jp_450_;
}
}
else
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; uint8_t v___x_469_; 
v___x_466_ = lean_unsigned_to_nat(0u);
v___x_467_ = l_Lean_Syntax_getArg(v___x_461_, v___x_466_);
lean_dec(v___x_461_);
v___x_468_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__8));
lean_inc(v___x_467_);
v___x_469_ = l_Lean_Syntax_isOfKind(v___x_467_, v___x_468_);
if (v___x_469_ == 0)
{
lean_dec(v___x_467_);
v_a_443_ = v___x_449_;
goto v___jp_442_;
}
else
{
v_patHead_451_ = v___x_467_;
v___y_452_ = v___y_439_;
v___y_453_ = v___y_440_;
goto v___jp_450_;
}
}
}
v___jp_450_:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_454_ = l_Lean_Linter_linter_suspiciousUnexpanderPatterns;
v___x_455_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__2);
v___x_456_ = l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4(v___x_454_, v_patHead_451_, v___x_455_, v___y_452_, v___y_453_);
lean_dec(v_patHead_451_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_dec_ref(v___x_456_);
v_a_443_ = v___x_449_;
goto v___jp_442_;
}
else
{
return v___x_456_;
}
}
}
v___jp_442_:
{
size_t v___x_444_; size_t v___x_445_; 
v___x_444_ = ((size_t)1ULL);
v___x_445_ = lean_usize_add(v_i_437_, v___x_444_);
v_i_437_ = v___x_445_;
v_b_438_ = v_a_443_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___boxed(lean_object* v_as_470_, lean_object* v_sz_471_, lean_object* v_i_472_, lean_object* v_b_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
size_t v_sz_boxed_477_; size_t v_i_boxed_478_; lean_object* v_res_479_; 
v_sz_boxed_477_ = lean_unbox_usize(v_sz_471_);
lean_dec(v_sz_471_);
v_i_boxed_478_ = lean_unbox_usize(v_i_472_);
lean_dec(v_i_472_);
v_res_479_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5(v_as_470_, v_sz_boxed_477_, v_i_boxed_478_, v_b_473_, v___y_474_, v___y_475_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
lean_dec_ref(v_as_470_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2(size_t v_sz_486_, size_t v_i_487_, lean_object* v_bs_488_){
_start:
{
uint8_t v___x_489_; 
v___x_489_ = lean_usize_dec_lt(v_i_487_, v_sz_486_);
if (v___x_489_ == 0)
{
lean_object* v___x_490_; 
v___x_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_490_, 0, v_bs_488_);
return v___x_490_;
}
else
{
lean_object* v_v_491_; lean_object* v___x_492_; uint8_t v___x_493_; 
v_v_491_ = lean_array_uget_borrowed(v_bs_488_, v_i_487_);
v___x_492_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__1));
lean_inc(v_v_491_);
v___x_493_ = l_Lean_Syntax_isOfKind(v_v_491_, v___x_492_);
if (v___x_493_ == 0)
{
lean_object* v___x_494_; 
lean_dec_ref(v_bs_488_);
v___x_494_ = lean_box(0);
return v___x_494_;
}
else
{
lean_object* v___x_495_; lean_object* v___x_496_; uint8_t v___x_497_; 
v___x_495_ = lean_unsigned_to_nat(1u);
v___x_496_ = l_Lean_Syntax_getArg(v_v_491_, v___x_495_);
lean_inc(v___x_496_);
v___x_497_ = l_Lean_Syntax_matchesNull(v___x_496_, v___x_495_);
if (v___x_497_ == 0)
{
lean_object* v___x_498_; 
lean_dec(v___x_496_);
lean_dec_ref(v_bs_488_);
v___x_498_ = lean_box(0);
return v___x_498_;
}
else
{
lean_object* v___x_499_; lean_object* v___x_500_; uint8_t v___x_501_; 
v___x_499_ = lean_unsigned_to_nat(0u);
v___x_500_ = l_Lean_Syntax_getArg(v___x_496_, v___x_499_);
lean_dec(v___x_496_);
lean_inc(v___x_500_);
v___x_501_ = l_Lean_Syntax_matchesNull(v___x_500_, v___x_495_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; 
lean_dec(v___x_500_);
lean_dec_ref(v_bs_488_);
v___x_502_ = lean_box(0);
return v___x_502_;
}
else
{
lean_object* v_bs_x27_503_; lean_object* v___x_504_; size_t v___x_505_; size_t v___x_506_; lean_object* v___x_507_; 
v_bs_x27_503_ = lean_array_uset(v_bs_488_, v_i_487_, v___x_499_);
v___x_504_ = l_Lean_Syntax_getArg(v___x_500_, v___x_499_);
lean_dec(v___x_500_);
v___x_505_ = ((size_t)1ULL);
v___x_506_ = lean_usize_add(v_i_487_, v___x_505_);
v___x_507_ = lean_array_uset(v_bs_x27_503_, v_i_487_, v___x_504_);
v_i_487_ = v___x_506_;
v_bs_488_ = v___x_507_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___boxed(lean_object* v_sz_509_, lean_object* v_i_510_, lean_object* v_bs_511_){
_start:
{
size_t v_sz_boxed_512_; size_t v_i_boxed_513_; lean_object* v_res_514_; 
v_sz_boxed_512_ = lean_unbox_usize(v_sz_509_);
lean_dec(v_sz_509_);
v_i_boxed_513_ = lean_unbox_usize(v_i_510_);
lean_dec(v_i_510_);
v_res_514_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2(v_sz_boxed_512_, v_i_boxed_513_, v_bs_511_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__6(uint8_t v___x_515_, lean_object* v_as_516_, size_t v_i_517_, size_t v_stop_518_, lean_object* v_b_519_){
_start:
{
lean_object* v___y_521_; uint8_t v___x_525_; 
v___x_525_ = lean_usize_dec_eq(v_i_517_, v_stop_518_);
if (v___x_525_ == 0)
{
lean_object* v_fst_526_; uint8_t v___x_527_; 
v_fst_526_ = lean_ctor_get(v_b_519_, 0);
v___x_527_ = lean_unbox(v_fst_526_);
if (v___x_527_ == 0)
{
lean_object* v_snd_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_536_; 
v_snd_528_ = lean_ctor_get(v_b_519_, 1);
v_isSharedCheck_536_ = !lean_is_exclusive(v_b_519_);
if (v_isSharedCheck_536_ == 0)
{
lean_object* v_unused_537_; 
v_unused_537_ = lean_ctor_get(v_b_519_, 0);
lean_dec(v_unused_537_);
v___x_530_ = v_b_519_;
v_isShared_531_ = v_isSharedCheck_536_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_snd_528_);
lean_dec(v_b_519_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_536_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_532_; lean_object* v___x_534_; 
v___x_532_ = lean_box(v___x_515_);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 0, v___x_532_);
v___x_534_ = v___x_530_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_532_);
lean_ctor_set(v_reuseFailAlloc_535_, 1, v_snd_528_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
v___y_521_ = v___x_534_;
goto v___jp_520_;
}
}
}
else
{
lean_object* v_snd_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_548_; 
v_snd_538_ = lean_ctor_get(v_b_519_, 1);
v_isSharedCheck_548_ = !lean_is_exclusive(v_b_519_);
if (v_isSharedCheck_548_ == 0)
{
lean_object* v_unused_549_; 
v_unused_549_ = lean_ctor_get(v_b_519_, 0);
lean_dec(v_unused_549_);
v___x_540_ = v_b_519_;
v_isShared_541_ = v_isSharedCheck_548_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_snd_538_);
lean_dec(v_b_519_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_548_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_546_; 
v___x_542_ = lean_array_uget_borrowed(v_as_516_, v_i_517_);
lean_inc(v___x_542_);
v___x_543_ = lean_array_push(v_snd_538_, v___x_542_);
v___x_544_ = lean_box(v___x_525_);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 1, v___x_543_);
lean_ctor_set(v___x_540_, 0, v___x_544_);
v___x_546_ = v___x_540_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_544_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v___x_543_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
v___y_521_ = v___x_546_;
goto v___jp_520_;
}
}
}
}
else
{
return v_b_519_;
}
v___jp_520_:
{
size_t v___x_522_; size_t v___x_523_; 
v___x_522_ = ((size_t)1ULL);
v___x_523_ = lean_usize_add(v_i_517_, v___x_522_);
v_i_517_ = v___x_523_;
v_b_519_ = v___y_521_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__6___boxed(lean_object* v___x_550_, lean_object* v_as_551_, lean_object* v_i_552_, lean_object* v_stop_553_, lean_object* v_b_554_){
_start:
{
uint8_t v___x_26545__boxed_555_; size_t v_i_boxed_556_; size_t v_stop_boxed_557_; lean_object* v_res_558_; 
v___x_26545__boxed_555_ = lean_unbox(v___x_550_);
v_i_boxed_556_ = lean_unbox_usize(v_i_552_);
lean_dec(v_i_552_);
v_stop_boxed_557_ = lean_unbox_usize(v_stop_553_);
lean_dec(v_stop_553_);
v_res_558_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__6(v___x_26545__boxed_555_, v_as_551_, v_i_boxed_556_, v_stop_boxed_557_, v_b_554_);
lean_dec_ref(v_as_551_);
return v_res_558_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3(uint8_t v___x_569_, lean_object* v_as_570_, size_t v_i_571_, size_t v_stop_572_){
_start:
{
uint8_t v___x_573_; 
v___x_573_ = lean_usize_dec_eq(v_i_571_, v_stop_572_);
if (v___x_573_ == 0)
{
uint8_t v___x_574_; uint8_t v___y_576_; lean_object* v___x_580_; lean_object* v___x_581_; uint8_t v___x_582_; 
v___x_574_ = 1;
v___x_580_ = lean_array_uget_borrowed(v_as_570_, v_i_571_);
v___x_581_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__2));
lean_inc(v___x_580_);
v___x_582_ = l_Lean_Syntax_isOfKind(v___x_580_, v___x_581_);
if (v___x_582_ == 0)
{
v___y_576_ = v___x_582_;
goto v___jp_575_;
}
else
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; uint8_t v___x_586_; 
v___x_583_ = lean_unsigned_to_nat(0u);
v___x_584_ = l_Lean_Syntax_getArg(v___x_580_, v___x_583_);
v___x_585_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__4));
v___x_586_ = l_Lean_Syntax_matchesIdent(v___x_584_, v___x_585_);
lean_dec(v___x_584_);
if (v___x_586_ == 0)
{
v___y_576_ = v___x_586_;
goto v___jp_575_;
}
else
{
lean_object* v___x_587_; lean_object* v___x_588_; uint8_t v___x_589_; 
v___x_587_ = lean_unsigned_to_nat(1u);
v___x_588_ = l_Lean_Syntax_getArg(v___x_580_, v___x_587_);
v___x_589_ = l_Lean_Syntax_matchesNull(v___x_588_, v___x_587_);
if (v___x_589_ == 0)
{
v___y_576_ = v___x_589_;
goto v___jp_575_;
}
else
{
v___y_576_ = v___x_569_;
goto v___jp_575_;
}
}
}
v___jp_575_:
{
if (v___y_576_ == 0)
{
size_t v___x_577_; size_t v___x_578_; 
v___x_577_ = ((size_t)1ULL);
v___x_578_ = lean_usize_add(v_i_571_, v___x_577_);
v_i_571_ = v___x_578_;
goto _start;
}
else
{
return v___x_574_;
}
}
}
else
{
uint8_t v___x_590_; 
v___x_590_ = 0;
return v___x_590_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___boxed(lean_object* v___x_591_, lean_object* v_as_592_, lean_object* v_i_593_, lean_object* v_stop_594_){
_start:
{
uint8_t v___x_26630__boxed_595_; size_t v_i_boxed_596_; size_t v_stop_boxed_597_; uint8_t v_res_598_; lean_object* v_r_599_; 
v___x_26630__boxed_595_ = lean_unbox(v___x_591_);
v_i_boxed_596_ = lean_unbox_usize(v_i_593_);
lean_dec(v_i_593_);
v_stop_boxed_597_ = lean_unbox_usize(v_stop_594_);
lean_dec(v_stop_594_);
v_res_598_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3(v___x_26630__boxed_595_, v_as_592_, v_i_boxed_596_, v_stop_boxed_597_);
lean_dec_ref(v_as_592_);
v_r_599_ = lean_box(v_res_598_);
return v_r_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0(lean_object* v_cmdStx_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
lean_object* v___x_662_; lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_882_; 
v___x_662_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0(v___y_656_, v___y_657_);
v_a_663_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_882_ == 0)
{
v___x_665_ = v___x_662_;
v_isShared_666_ = v_isSharedCheck_882_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_662_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_882_;
goto v_resetjp_664_;
}
v___jp_659_:
{
lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_660_ = lean_box(0);
v___x_661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
return v___x_661_;
}
v_resetjp_664_:
{
uint8_t v___x_667_; 
v___x_667_ = l_Lean_Linter_getLinterSuspiciousUnexpanderPatterns(v_a_663_);
lean_dec(v_a_663_);
if (v___x_667_ == 0)
{
lean_object* v___x_668_; lean_object* v___x_670_; 
lean_dec(v_cmdStx_655_);
v___x_668_ = lean_box(0);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_668_);
v___x_670_ = v___x_665_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v___x_668_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
else
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; uint8_t v___x_675_; 
v___x_672_ = ((lean_object*)(l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_));
v___x_673_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0));
v___x_674_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__2));
lean_inc(v_cmdStx_655_);
v___x_675_ = l_Lean_Syntax_isOfKind(v_cmdStx_655_, v___x_674_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; lean_object* v___x_678_; 
lean_dec(v_cmdStx_655_);
v___x_676_ = lean_box(0);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_676_);
v___x_678_ = v___x_665_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_676_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
else
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; uint8_t v___x_683_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_840_; lean_object* v___y_841_; 
v___x_680_ = lean_unsigned_to_nat(0u);
v___x_681_ = l_Lean_Syntax_getArg(v_cmdStx_655_, v___x_680_);
v___x_682_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__4));
lean_inc(v___x_681_);
v___x_683_ = l_Lean_Syntax_isOfKind(v___x_681_, v___x_682_);
if (v___x_683_ == 0)
{
lean_object* v___x_869_; lean_object* v___x_870_; 
lean_dec(v___x_681_);
lean_del_object(v___x_665_);
lean_dec(v_cmdStx_655_);
v___x_869_ = lean_box(0);
v___x_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
return v___x_870_;
}
else
{
lean_object* v___x_871_; uint8_t v___x_872_; 
v___x_871_ = l_Lean_Syntax_getArg(v___x_681_, v___x_680_);
v___x_872_ = l_Lean_Syntax_isNone(v___x_871_);
if (v___x_872_ == 0)
{
lean_object* v___x_873_; uint8_t v___x_874_; 
v___x_873_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_871_);
v___x_874_ = l_Lean_Syntax_matchesNull(v___x_871_, v___x_873_);
if (v___x_874_ == 0)
{
lean_object* v___x_875_; lean_object* v___x_876_; 
lean_dec(v___x_871_);
lean_dec(v___x_681_);
lean_del_object(v___x_665_);
lean_dec(v_cmdStx_655_);
v___x_875_ = lean_box(0);
v___x_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_876_, 0, v___x_875_);
return v___x_876_;
}
else
{
lean_object* v___x_877_; lean_object* v___x_878_; uint8_t v___x_879_; 
v___x_877_ = l_Lean_Syntax_getArg(v___x_871_, v___x_680_);
lean_dec(v___x_871_);
v___x_878_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__21));
v___x_879_ = l_Lean_Syntax_isOfKind(v___x_877_, v___x_878_);
if (v___x_879_ == 0)
{
lean_object* v___x_880_; lean_object* v___x_881_; 
lean_dec(v___x_681_);
lean_del_object(v___x_665_);
lean_dec(v_cmdStx_655_);
v___x_880_ = lean_box(0);
v___x_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_881_, 0, v___x_880_);
return v___x_881_;
}
else
{
v___y_840_ = v___y_656_;
v___y_841_ = v___y_657_;
goto v___jp_839_;
}
}
}
else
{
lean_dec(v___x_871_);
v___y_840_ = v___y_656_;
v___y_841_ = v___y_657_;
goto v___jp_839_;
}
}
v___jp_684_:
{
size_t v_sz_690_; size_t v___x_691_; lean_object* v___x_692_; 
v_sz_690_ = lean_array_size(v___y_689_);
v___x_691_ = ((size_t)0ULL);
v___x_692_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1(v_sz_690_, v___x_691_, v___y_689_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v___x_693_; lean_object* v___x_695_; 
lean_dec_ref(v___y_688_);
lean_dec(v___x_681_);
lean_dec(v_cmdStx_655_);
v___x_693_ = lean_box(0);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_693_);
v___x_695_ = v___x_665_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v___x_693_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
else
{
lean_object* v_val_697_; lean_object* v___x_698_; lean_object* v___x_699_; uint8_t v___x_700_; 
v_val_697_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_val_697_);
lean_dec_ref(v___x_692_);
v___x_698_ = lean_unsigned_to_nat(3u);
v___x_699_ = l_Lean_Syntax_getArg(v___x_681_, v___x_698_);
v___x_700_ = l_Lean_Syntax_matchesNull(v___x_699_, v___x_680_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; lean_object* v___x_703_; 
lean_dec(v_val_697_);
lean_dec_ref(v___y_688_);
lean_dec(v___x_681_);
lean_dec(v_cmdStx_655_);
v___x_701_ = lean_box(0);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_701_);
v___x_703_ = v___x_665_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_701_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
else
{
lean_object* v___x_705_; lean_object* v___x_706_; uint8_t v___x_707_; 
v___x_705_ = lean_unsigned_to_nat(4u);
v___x_706_ = l_Lean_Syntax_getArg(v___x_681_, v___x_705_);
v___x_707_ = l_Lean_Syntax_matchesNull(v___x_706_, v___x_680_);
if (v___x_707_ == 0)
{
lean_object* v___x_708_; lean_object* v___x_710_; 
lean_dec(v_val_697_);
lean_dec_ref(v___y_688_);
lean_dec(v___x_681_);
lean_dec(v_cmdStx_655_);
v___x_708_ = lean_box(0);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_708_);
v___x_710_ = v___x_665_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v___x_708_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
else
{
lean_object* v___x_712_; lean_object* v___x_713_; uint8_t v___x_714_; 
v___x_712_ = lean_unsigned_to_nat(5u);
v___x_713_ = l_Lean_Syntax_getArg(v___x_681_, v___x_712_);
v___x_714_ = l_Lean_Syntax_matchesNull(v___x_713_, v___x_680_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; lean_object* v___x_717_; 
lean_dec(v_val_697_);
lean_dec_ref(v___y_688_);
lean_dec(v___x_681_);
lean_dec(v_cmdStx_655_);
v___x_715_ = lean_box(0);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_715_);
v___x_717_ = v___x_665_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_715_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
else
{
lean_object* v___x_719_; lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_719_ = lean_unsigned_to_nat(6u);
v___x_720_ = l_Lean_Syntax_getArg(v___x_681_, v___x_719_);
lean_dec(v___x_681_);
v___x_721_ = l_Lean_Syntax_matchesNull(v___x_720_, v___x_680_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; lean_object* v___x_724_; 
lean_dec(v_val_697_);
lean_dec_ref(v___y_688_);
lean_dec(v_cmdStx_655_);
v___x_722_ = lean_box(0);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_722_);
v___x_724_ = v___x_665_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_722_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
else
{
lean_object* v___x_726_; lean_object* v___x_727_; uint8_t v___x_728_; 
v___x_726_ = l_Lean_Syntax_getArg(v_cmdStx_655_, v___y_687_);
lean_dec(v_cmdStx_655_);
v___x_727_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__6));
lean_inc(v___x_726_);
v___x_728_ = l_Lean_Syntax_isOfKind(v___x_726_, v___x_727_);
if (v___x_728_ == 0)
{
lean_object* v___x_729_; lean_object* v___x_731_; 
lean_dec(v___x_726_);
lean_dec(v_val_697_);
lean_dec_ref(v___y_688_);
v___x_729_ = lean_box(0);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_729_);
v___x_731_ = v___x_665_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_729_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
else
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; uint8_t v___x_736_; 
v___x_733_ = lean_unsigned_to_nat(2u);
v___x_734_ = l_Lean_Syntax_getArg(v___x_726_, v___x_733_);
v___x_735_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__8));
lean_inc(v___x_734_);
v___x_736_ = l_Lean_Syntax_isOfKind(v___x_734_, v___x_735_);
if (v___x_736_ == 0)
{
lean_object* v___x_737_; lean_object* v___x_739_; 
lean_dec(v___x_734_);
lean_dec(v___x_726_);
lean_dec(v_val_697_);
lean_dec_ref(v___y_688_);
v___x_737_ = lean_box(0);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_737_);
v___x_739_ = v___x_665_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_737_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
else
{
lean_object* v___x_741_; uint8_t v___x_742_; 
v___x_741_ = l_Lean_Syntax_getArg(v___x_734_, v___x_680_);
v___x_742_ = l_Lean_Syntax_matchesNull(v___x_741_, v___x_680_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; lean_object* v___x_745_; 
lean_dec(v___x_734_);
lean_dec(v___x_726_);
lean_dec(v_val_697_);
lean_dec_ref(v___y_688_);
v___x_743_ = lean_box(0);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_743_);
v___x_745_ = v___x_665_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_743_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
else
{
lean_object* v___x_747_; uint8_t v___x_748_; 
v___x_747_ = l_Lean_Syntax_getArg(v___x_734_, v___y_687_);
lean_dec(v___x_734_);
lean_inc(v___x_747_);
v___x_748_ = l_Lean_Syntax_matchesNull(v___x_747_, v___y_687_);
if (v___x_748_ == 0)
{
lean_object* v___x_749_; lean_object* v___x_751_; 
lean_dec(v___x_747_);
lean_dec(v___x_726_);
lean_dec(v_val_697_);
lean_dec_ref(v___y_688_);
v___x_749_ = lean_box(0);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_749_);
v___x_751_ = v___x_665_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v___x_749_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
else
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; uint8_t v___x_756_; 
v___x_753_ = l_Lean_Syntax_getArg(v___x_747_, v___x_680_);
lean_dec(v___x_747_);
v___x_754_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__9));
lean_inc_ref(v___y_688_);
v___x_755_ = l_Lean_Name_mkStr4(v___x_672_, v___x_673_, v___y_688_, v___x_754_);
v___x_756_ = l_Lean_Syntax_isOfKind(v___x_753_, v___x_755_);
lean_dec(v___x_755_);
if (v___x_756_ == 0)
{
lean_object* v___x_757_; lean_object* v___x_759_; 
lean_dec(v___x_726_);
lean_dec(v_val_697_);
lean_dec_ref(v___y_688_);
v___x_757_ = lean_box(0);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_757_);
v___x_759_ = v___x_665_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___x_757_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
else
{
lean_object* v___x_761_; lean_object* v___x_762_; uint8_t v___x_763_; 
v___x_761_ = l_Lean_Syntax_getArg(v___x_726_, v___x_698_);
v___x_762_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__11));
lean_inc(v___x_761_);
v___x_763_ = l_Lean_Syntax_isOfKind(v___x_761_, v___x_762_);
if (v___x_763_ == 0)
{
lean_object* v___x_764_; lean_object* v___x_766_; 
lean_dec(v___x_761_);
lean_dec(v___x_726_);
lean_dec(v_val_697_);
lean_dec_ref(v___y_688_);
v___x_764_ = lean_box(0);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_764_);
v___x_766_ = v___x_665_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v___x_764_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
else
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; uint8_t v___x_771_; 
v___x_768_ = l_Lean_Syntax_getArg(v___x_761_, v___x_680_);
lean_dec(v___x_761_);
v___x_769_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__12));
lean_inc_ref(v___y_688_);
v___x_770_ = l_Lean_Name_mkStr4(v___x_672_, v___x_673_, v___y_688_, v___x_769_);
lean_inc(v___x_768_);
v___x_771_ = l_Lean_Syntax_isOfKind(v___x_768_, v___x_770_);
lean_dec(v___x_770_);
if (v___x_771_ == 0)
{
lean_object* v___x_772_; lean_object* v___x_774_; 
lean_dec(v___x_768_);
lean_dec(v___x_726_);
lean_dec(v_val_697_);
lean_dec_ref(v___y_688_);
v___x_772_ = lean_box(0);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_772_);
v___x_774_ = v___x_665_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_772_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
else
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; uint8_t v___x_779_; 
v___x_776_ = l_Lean_Syntax_getArg(v___x_768_, v___x_680_);
v___x_777_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__13));
v___x_778_ = l_Lean_Name_mkStr4(v___x_672_, v___x_673_, v___y_688_, v___x_777_);
lean_inc(v___x_776_);
v___x_779_ = l_Lean_Syntax_isOfKind(v___x_776_, v___x_778_);
lean_dec(v___x_778_);
if (v___x_779_ == 0)
{
lean_object* v___x_780_; lean_object* v___x_782_; 
lean_dec(v___x_776_);
lean_dec(v___x_768_);
lean_dec(v___x_726_);
lean_dec(v_val_697_);
v___x_780_ = lean_box(0);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_780_);
v___x_782_ = v___x_665_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_780_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
else
{
lean_object* v___x_784_; lean_object* v___x_785_; size_t v_sz_786_; lean_object* v___x_787_; 
v___x_784_ = l_Lean_Syntax_getArg(v___x_776_, v___x_680_);
lean_dec(v___x_776_);
v___x_785_ = l_Lean_Syntax_getArgs(v___x_784_);
lean_dec(v___x_784_);
v_sz_786_ = lean_array_size(v___x_785_);
v___x_787_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2(v_sz_786_, v___x_691_, v___x_785_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v___x_788_; lean_object* v___x_790_; 
lean_dec(v___x_768_);
lean_dec(v___x_726_);
lean_dec(v_val_697_);
v___x_788_ = lean_box(0);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_788_);
v___x_790_ = v___x_665_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_788_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
else
{
lean_object* v_val_792_; lean_object* v___x_793_; lean_object* v___x_794_; uint8_t v___x_795_; 
v_val_792_ = lean_ctor_get(v___x_787_, 0);
lean_inc(v_val_792_);
lean_dec_ref(v___x_787_);
v___x_793_ = l_Lean_Syntax_getArg(v___x_768_, v___y_687_);
v___x_794_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__16));
lean_inc(v___x_793_);
v___x_795_ = l_Lean_Syntax_isOfKind(v___x_793_, v___x_794_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; lean_object* v___x_798_; 
lean_dec(v___x_793_);
lean_dec(v_val_792_);
lean_dec(v___x_768_);
lean_dec(v___x_726_);
lean_dec(v_val_697_);
v___x_796_ = lean_box(0);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_796_);
v___x_798_ = v___x_665_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v___x_796_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
else
{
lean_object* v___x_800_; uint8_t v___x_801_; 
v___x_800_ = l_Lean_Syntax_getArg(v___x_793_, v___x_680_);
v___x_801_ = l_Lean_Syntax_matchesNull(v___x_800_, v___x_680_);
if (v___x_801_ == 0)
{
lean_object* v___x_802_; lean_object* v___x_804_; 
lean_dec(v___x_793_);
lean_dec(v_val_792_);
lean_dec(v___x_768_);
lean_dec(v___x_726_);
lean_dec(v_val_697_);
v___x_802_ = lean_box(0);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_802_);
v___x_804_ = v___x_665_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_802_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
else
{
lean_object* v___x_806_; uint8_t v___x_807_; 
v___x_806_ = l_Lean_Syntax_getArg(v___x_793_, v___y_687_);
lean_dec(v___x_793_);
v___x_807_ = l_Lean_Syntax_matchesNull(v___x_806_, v___x_680_);
if (v___x_807_ == 0)
{
lean_object* v___x_808_; lean_object* v___x_810_; 
lean_dec(v_val_792_);
lean_dec(v___x_768_);
lean_dec(v___x_726_);
lean_dec(v_val_697_);
v___x_808_ = lean_box(0);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_808_);
v___x_810_ = v___x_665_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_808_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
else
{
lean_object* v___x_812_; uint8_t v___x_813_; 
v___x_812_ = l_Lean_Syntax_getArg(v___x_768_, v___x_733_);
lean_dec(v___x_768_);
v___x_813_ = l_Lean_Syntax_matchesNull(v___x_812_, v___x_680_);
if (v___x_813_ == 0)
{
lean_object* v___x_814_; lean_object* v___x_816_; 
lean_dec(v_val_792_);
lean_dec(v___x_726_);
lean_dec(v_val_697_);
v___x_814_ = lean_box(0);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_814_);
v___x_816_ = v___x_665_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_814_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
else
{
lean_object* v___x_818_; uint8_t v___x_819_; 
v___x_818_ = l_Lean_Syntax_getArg(v___x_726_, v___x_705_);
lean_dec(v___x_726_);
v___x_819_ = l_Lean_Syntax_matchesNull(v___x_818_, v___x_680_);
if (v___x_819_ == 0)
{
lean_object* v___x_820_; lean_object* v___x_822_; 
lean_dec(v_val_792_);
lean_dec(v_val_697_);
v___x_820_ = lean_box(0);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_820_);
v___x_822_ = v___x_665_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_820_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
else
{
lean_object* v___x_824_; uint8_t v___x_825_; 
lean_del_object(v___x_665_);
v___x_824_ = lean_array_get_size(v_val_697_);
v___x_825_ = lean_nat_dec_lt(v___x_680_, v___x_824_);
if (v___x_825_ == 0)
{
lean_dec(v_val_792_);
lean_dec(v_val_697_);
goto v___jp_659_;
}
else
{
if (v___x_825_ == 0)
{
lean_dec(v_val_792_);
lean_dec(v_val_697_);
goto v___jp_659_;
}
else
{
size_t v___x_826_; uint8_t v___x_827_; 
v___x_826_ = lean_usize_of_nat(v___x_824_);
v___x_827_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3(v___x_683_, v_val_697_, v___x_691_, v___x_826_);
lean_dec(v_val_697_);
if (v___x_827_ == 0)
{
lean_dec(v_val_792_);
goto v___jp_659_;
}
else
{
lean_object* v___x_828_; size_t v_sz_829_; lean_object* v___x_830_; 
v___x_828_ = lean_box(0);
v_sz_829_ = lean_array_size(v_val_792_);
v___x_830_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5(v_val_792_, v_sz_829_, v___x_691_, v___x_828_, v___y_685_, v___y_686_);
lean_dec(v_val_792_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_837_ == 0)
{
lean_object* v_unused_838_; 
v_unused_838_ = lean_ctor_get(v___x_830_, 0);
lean_dec(v_unused_838_);
v___x_832_ = v___x_830_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_dec(v___x_830_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 0, v___x_828_);
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_828_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
else
{
return v___x_830_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
v___jp_839_:
{
lean_object* v___x_842_; lean_object* v___x_843_; uint8_t v___x_844_; 
v___x_842_ = lean_unsigned_to_nat(1u);
v___x_843_ = l_Lean_Syntax_getArg(v___x_681_, v___x_842_);
lean_inc(v___x_843_);
v___x_844_ = l_Lean_Syntax_matchesNull(v___x_843_, v___x_842_);
if (v___x_844_ == 0)
{
lean_object* v___x_845_; lean_object* v___x_846_; 
lean_dec(v___x_843_);
lean_dec(v___x_681_);
lean_del_object(v___x_665_);
lean_dec(v_cmdStx_655_);
v___x_845_ = lean_box(0);
v___x_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
return v___x_846_;
}
else
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; uint8_t v___x_850_; 
v___x_847_ = l_Lean_Syntax_getArg(v___x_843_, v___x_680_);
lean_dec(v___x_843_);
v___x_848_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__1));
v___x_849_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__18));
lean_inc(v___x_847_);
v___x_850_ = l_Lean_Syntax_isOfKind(v___x_847_, v___x_849_);
if (v___x_850_ == 0)
{
lean_object* v___x_851_; lean_object* v___x_852_; 
lean_dec(v___x_847_);
lean_dec(v___x_681_);
lean_del_object(v___x_665_);
lean_dec(v_cmdStx_655_);
v___x_851_ = lean_box(0);
v___x_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_852_, 0, v___x_851_);
return v___x_852_;
}
else
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; uint8_t v___x_857_; 
v___x_853_ = l_Lean_Syntax_getArg(v___x_847_, v___x_842_);
lean_dec(v___x_847_);
v___x_854_ = l_Lean_Syntax_getArgs(v___x_853_);
lean_dec(v___x_853_);
v___x_855_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__19));
v___x_856_ = lean_array_get_size(v___x_854_);
v___x_857_ = lean_nat_dec_lt(v___x_680_, v___x_856_);
if (v___x_857_ == 0)
{
lean_dec_ref(v___x_854_);
v___y_685_ = v___y_840_;
v___y_686_ = v___y_841_;
v___y_687_ = v___x_842_;
v___y_688_ = v___x_848_;
v___y_689_ = v___x_855_;
goto v___jp_684_;
}
else
{
lean_object* v___x_858_; lean_object* v___x_859_; uint8_t v___x_860_; 
v___x_858_ = lean_box(v___x_850_);
v___x_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_859_, 0, v___x_858_);
lean_ctor_set(v___x_859_, 1, v___x_855_);
v___x_860_ = lean_nat_dec_le(v___x_856_, v___x_856_);
if (v___x_860_ == 0)
{
if (v___x_857_ == 0)
{
lean_dec_ref(v___x_859_);
lean_dec_ref(v___x_854_);
v___y_685_ = v___y_840_;
v___y_686_ = v___y_841_;
v___y_687_ = v___x_842_;
v___y_688_ = v___x_848_;
v___y_689_ = v___x_855_;
goto v___jp_684_;
}
else
{
size_t v___x_861_; size_t v___x_862_; lean_object* v___x_863_; lean_object* v_snd_864_; 
v___x_861_ = ((size_t)0ULL);
v___x_862_ = lean_usize_of_nat(v___x_856_);
v___x_863_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__6(v___x_850_, v___x_854_, v___x_861_, v___x_862_, v___x_859_);
lean_dec_ref(v___x_854_);
v_snd_864_ = lean_ctor_get(v___x_863_, 1);
lean_inc(v_snd_864_);
lean_dec_ref(v___x_863_);
v___y_685_ = v___y_840_;
v___y_686_ = v___y_841_;
v___y_687_ = v___x_842_;
v___y_688_ = v___x_848_;
v___y_689_ = v_snd_864_;
goto v___jp_684_;
}
}
else
{
size_t v___x_865_; size_t v___x_866_; lean_object* v___x_867_; lean_object* v_snd_868_; 
v___x_865_ = ((size_t)0ULL);
v___x_866_ = lean_usize_of_nat(v___x_856_);
v___x_867_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__6(v___x_850_, v___x_854_, v___x_865_, v___x_866_, v___x_859_);
lean_dec_ref(v___x_854_);
v_snd_868_ = lean_ctor_get(v___x_867_, 1);
lean_inc(v_snd_868_);
lean_dec_ref(v___x_867_);
v___y_685_ = v___y_840_;
v___y_686_ = v___y_841_;
v___y_687_ = v___x_842_;
v___y_688_ = v___x_848_;
v___y_689_ = v_snd_868_;
goto v___jp_684_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___boxed(lean_object* v_cmdStx_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0(v_cmdStx_883_, v___y_884_, v___y_885_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0(lean_object* v_o_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
lean_object* v___x_901_; 
v___x_901_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0___redArg(v_o_897_, v___y_899_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0___boxed(lean_object* v_o_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0(v_o_902_, v___y_903_, v___y_904_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9(lean_object* v_msgData_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg(v_msgData_907_, v___y_909_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___boxed(lean_object* v_msgData_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9(v_msgData_912_, v___y_913_, v___y_914_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1774244096____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_918_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns));
v___x_919_ = l_Lean_Elab_Command_addLinter(v___x_918_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1774244096____hygCtx___hyg_2____boxed(lean_object* v_a_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1774244096____hygCtx___hyg_2_();
return v_res_921_;
}
}
lean_object* runtime_initialize_Lean_Linter_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_Builtin(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Linter_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_linter_suspiciousUnexpanderPatterns = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_linter_suspiciousUnexpanderPatterns);
lean_dec_ref(res);
res = l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1774244096____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Linter_Builtin(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Linter_Util(uint8_t builtin);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Linter_Builtin(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Linter_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Builtin(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Linter_Builtin(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Linter_Builtin(builtin);
}
#ifdef __cplusplus
}
#endif
