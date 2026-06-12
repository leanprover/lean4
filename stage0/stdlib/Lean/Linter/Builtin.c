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
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
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
extern lean_object* l_Lean_Linter_linterMessageTag;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Elab_Command_addLinter(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "suspiciousUnexpanderPatterns"};
static const lean_object* l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(128, 75, 2, 63, 36, 64, 134, 16)}};
static const lean_object* l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "enable the 'suspicious unexpander patterns' linter"};
static const lean_object* l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(53, 243, 121, 207, 53, 172, 203, 87)}};
static const lean_ctor_object l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(187, 83, 153, 174, 192, 198, 91, 54)}};
static const lean_object* l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4____boxed(lean_object*);
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
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__3_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__3_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(241, 75, 242, 110, 47, 5, 20, 104)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__3_value),LEAN_SCALAR_PTR_LITERAL(145, 163, 173, 41, 168, 168, 65, 81)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__2_value_aux_1),((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__2_value_aux_2),((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__2 = (const lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__2_value;
static const lean_string_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__3 = (const lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__4_value_aux_1),((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__4_value_aux_2),((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__4 = (const lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__4_value;
static const lean_string_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__5 = (const lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__5_value;
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__6_value_aux_1),((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__6_value_aux_2),((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(248, 187, 217, 228, 39, 184, 218, 135)}};
static const lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__6 = (const lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__6_value;
static const lean_string_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optDeclSig"};
static const lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__7 = (const lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__7_value;
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__8_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__8_value_aux_1),((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__8_value_aux_2),((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(26, 9, 103, 232, 183, 57, 246, 75)}};
static const lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__8 = (const lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__8_value;
static const lean_string_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__9 = (const lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__9_value;
static const lean_string_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declValEqns"};
static const lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__10 = (const lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__10_value;
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__16_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__16_value_aux_1),((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__14_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__16_value_aux_2),((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__15_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__16 = (const lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__16_value;
static const lean_string_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__17 = (const lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__17_value;
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__18_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__18_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__18_value_aux_2),((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__17_value),LEAN_SCALAR_PTR_LITERAL(66, 184, 196, 169, 25, 125, 40, 35)}};
static const lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__18 = (const lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__18_value;
static const lean_array_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__19 = (const lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__19_value;
static const lean_string_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__20 = (const lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__20_value;
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__21_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__21_value_aux_1),((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__21_value_aux_2),((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__20_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__21 = (const lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__21_value;
LEAN_EXPORT lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Linter_suspiciousUnexpanderPatterns___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___closed__0 = (const lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___closed__0_value;
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_Lean_Linter_suspiciousUnexpanderPatterns___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_suspiciousUnexpanderPatterns___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(218, 57, 29, 215, 236, 35, 73, 76)}};
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_53_ = ((lean_object*)(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_));
v___x_54_ = ((lean_object*)(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_));
v___x_55_ = ((lean_object*)(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_));
v___x_56_ = l_Lean_Option_register___at___00__private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__spec__0(v___x_53_, v___x_54_, v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4____boxed(lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_();
return v_res_58_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_getLinterSuspiciousUnexpanderPatterns(lean_object* v_o_59_){
_start:
{
lean_object* v___x_60_; uint8_t v___x_61_; 
v___x_60_ = l_Lean_Linter_linter_suspiciousUnexpanderPatterns;
v___x_61_ = l_Lean_Linter_getLinterValue(v___x_60_, v_o_59_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterSuspiciousUnexpanderPatterns___boxed(lean_object* v_o_62_){
_start:
{
uint8_t v_res_63_; lean_object* v_r_64_; 
v_res_63_ = l_Lean_Linter_getLinterSuspiciousUnexpanderPatterns(v_o_62_);
lean_dec_ref(v_o_62_);
v_r_64_ = lean_box(v_res_63_);
return v_r_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0___redArg(lean_object* v_o_65_, lean_object* v___y_66_){
_start:
{
lean_object* v___x_68_; lean_object* v_env_69_; lean_object* v___x_70_; lean_object* v_toEnvExtension_71_; lean_object* v_asyncMode_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v_merged_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_84_; 
v___x_68_ = lean_st_ref_get(v___y_66_);
v_env_69_ = lean_ctor_get(v___x_68_, 0);
lean_inc_ref(v_env_69_);
lean_dec(v___x_68_);
v___x_70_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_71_ = lean_ctor_get(v___x_70_, 0);
v_asyncMode_72_ = lean_ctor_get(v_toEnvExtension_71_, 2);
v___x_73_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_74_ = lean_box(0);
v___x_75_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_73_, v___x_70_, v_env_69_, v_asyncMode_72_, v___x_74_);
v_merged_76_ = lean_ctor_get(v___x_75_, 0);
v_isSharedCheck_84_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_84_ == 0)
{
lean_object* v_unused_85_; 
v_unused_85_ = lean_ctor_get(v___x_75_, 1);
lean_dec(v_unused_85_);
v___x_78_ = v___x_75_;
v_isShared_79_ = v_isSharedCheck_84_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_merged_76_);
lean_dec(v___x_75_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_84_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___x_81_; 
if (v_isShared_79_ == 0)
{
lean_ctor_set(v___x_78_, 1, v_merged_76_);
lean_ctor_set(v___x_78_, 0, v_o_65_);
v___x_81_ = v___x_78_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_o_65_);
lean_ctor_set(v_reuseFailAlloc_83_, 1, v_merged_76_);
v___x_81_ = v_reuseFailAlloc_83_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
lean_object* v___x_82_; 
v___x_82_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
return v___x_82_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0___redArg___boxed(lean_object* v_o_86_, lean_object* v___y_87_, lean_object* v___y_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0___redArg(v_o_86_, v___y_87_);
lean_dec(v___y_87_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0(lean_object* v___y_90_, lean_object* v___y_91_){
_start:
{
lean_object* v___x_93_; lean_object* v_scopes_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v_opts_97_; lean_object* v___x_98_; 
v___x_93_ = lean_st_ref_get(v___y_91_);
v_scopes_94_ = lean_ctor_get(v___x_93_, 2);
lean_inc(v_scopes_94_);
lean_dec(v___x_93_);
v___x_95_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_96_ = l_List_head_x21___redArg(v___x_95_, v_scopes_94_);
lean_dec(v_scopes_94_);
v_opts_97_ = lean_ctor_get(v___x_96_, 1);
lean_inc_ref(v_opts_97_);
lean_dec(v___x_96_);
v___x_98_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0___redArg(v_opts_97_, v___y_91_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0___boxed(lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0(v___y_99_, v___y_100_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_99_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1(size_t v_sz_117_, size_t v_i_118_, lean_object* v_bs_119_){
_start:
{
uint8_t v___x_120_; 
v___x_120_ = lean_usize_dec_lt(v_i_118_, v_sz_117_);
if (v___x_120_ == 0)
{
lean_object* v___x_121_; 
v___x_121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_121_, 0, v_bs_119_);
return v___x_121_;
}
else
{
lean_object* v_v_122_; lean_object* v___x_123_; uint8_t v___x_124_; 
v_v_122_ = lean_array_uget(v_bs_119_, v_i_118_);
v___x_123_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__3));
lean_inc(v_v_122_);
v___x_124_ = l_Lean_Syntax_isOfKind(v_v_122_, v___x_123_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; 
lean_dec(v_v_122_);
lean_dec_ref(v_bs_119_);
v___x_125_ = lean_box(0);
return v___x_125_;
}
else
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_126_ = lean_unsigned_to_nat(0u);
v___x_127_ = l_Lean_Syntax_getArg(v_v_122_, v___x_126_);
v___x_128_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__5));
lean_inc(v___x_127_);
v___x_129_ = l_Lean_Syntax_isOfKind(v___x_127_, v___x_128_);
if (v___x_129_ == 0)
{
lean_object* v___x_130_; 
lean_dec(v___x_127_);
lean_dec(v_v_122_);
lean_dec_ref(v_bs_119_);
v___x_130_ = lean_box(0);
return v___x_130_;
}
else
{
lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_131_ = l_Lean_Syntax_getArg(v___x_127_, v___x_126_);
lean_dec(v___x_127_);
v___x_132_ = l_Lean_Syntax_matchesNull(v___x_131_, v___x_126_);
if (v___x_132_ == 0)
{
lean_object* v___x_133_; 
lean_dec(v_v_122_);
lean_dec_ref(v_bs_119_);
v___x_133_ = lean_box(0);
return v___x_133_;
}
else
{
lean_object* v___x_134_; lean_object* v_bs_x27_135_; lean_object* v___x_136_; size_t v___x_137_; size_t v___x_138_; lean_object* v___x_139_; 
v___x_134_ = lean_unsigned_to_nat(1u);
v_bs_x27_135_ = lean_array_uset(v_bs_119_, v_i_118_, v___x_126_);
v___x_136_ = l_Lean_Syntax_getArg(v_v_122_, v___x_134_);
lean_dec(v_v_122_);
v___x_137_ = ((size_t)1ULL);
v___x_138_ = lean_usize_add(v_i_118_, v___x_137_);
v___x_139_ = lean_array_uset(v_bs_x27_135_, v_i_118_, v___x_136_);
v_i_118_ = v___x_138_;
v_bs_119_ = v___x_139_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___boxed(lean_object* v_sz_141_, lean_object* v_i_142_, lean_object* v_bs_143_){
_start:
{
size_t v_sz_boxed_144_; size_t v_i_boxed_145_; lean_object* v_res_146_; 
v_sz_boxed_144_ = lean_unbox_usize(v_sz_141_);
lean_dec(v_sz_141_);
v_i_boxed_145_ = lean_unbox_usize(v_i_142_);
lean_dec(v_i_142_);
v_res_146_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1(v_sz_boxed_144_, v_i_boxed_145_, v_bs_143_);
return v_res_146_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__10(lean_object* v_opts_147_, lean_object* v_opt_148_){
_start:
{
lean_object* v_name_149_; lean_object* v_defValue_150_; lean_object* v_map_151_; lean_object* v___x_152_; 
v_name_149_ = lean_ctor_get(v_opt_148_, 0);
v_defValue_150_ = lean_ctor_get(v_opt_148_, 1);
v_map_151_ = lean_ctor_get(v_opts_147_, 0);
v___x_152_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_151_, v_name_149_);
if (lean_obj_tag(v___x_152_) == 0)
{
uint8_t v___x_153_; 
v___x_153_ = lean_unbox(v_defValue_150_);
return v___x_153_;
}
else
{
lean_object* v_val_154_; 
v_val_154_ = lean_ctor_get(v___x_152_, 0);
lean_inc(v_val_154_);
lean_dec_ref_known(v___x_152_, 1);
if (lean_obj_tag(v_val_154_) == 1)
{
uint8_t v_v_155_; 
v_v_155_ = lean_ctor_get_uint8(v_val_154_, 0);
lean_dec_ref_known(v_val_154_, 0);
return v_v_155_;
}
else
{
uint8_t v___x_156_; 
lean_dec(v_val_154_);
v___x_156_ = lean_unbox(v_defValue_150_);
return v___x_156_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__10___boxed(lean_object* v_opts_157_, lean_object* v_opt_158_){
_start:
{
uint8_t v_res_159_; lean_object* v_r_160_; 
v_res_159_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__10(v_opts_157_, v_opt_158_);
lean_dec_ref(v_opt_158_);
lean_dec_ref(v_opts_157_);
v_r_160_ = lean_box(v_res_159_);
return v_r_160_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_161_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__0);
v___x_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
return v___x_163_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_164_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1);
v___x_165_ = lean_unsigned_to_nat(0u);
v___x_166_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
lean_ctor_set(v___x_166_, 1, v___x_165_);
lean_ctor_set(v___x_166_, 2, v___x_165_);
lean_ctor_set(v___x_166_, 3, v___x_165_);
lean_ctor_set(v___x_166_, 4, v___x_164_);
lean_ctor_set(v___x_166_, 5, v___x_164_);
lean_ctor_set(v___x_166_, 6, v___x_164_);
lean_ctor_set(v___x_166_, 7, v___x_164_);
lean_ctor_set(v___x_166_, 8, v___x_164_);
lean_ctor_set(v___x_166_, 9, v___x_164_);
return v___x_166_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_167_ = lean_unsigned_to_nat(32u);
v___x_168_ = lean_mk_empty_array_with_capacity(v___x_167_);
v___x_169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
return v___x_169_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__4(void){
_start:
{
size_t v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_170_ = ((size_t)5ULL);
v___x_171_ = lean_unsigned_to_nat(0u);
v___x_172_ = lean_unsigned_to_nat(32u);
v___x_173_ = lean_mk_empty_array_with_capacity(v___x_172_);
v___x_174_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__3);
v___x_175_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_175_, 0, v___x_174_);
lean_ctor_set(v___x_175_, 1, v___x_173_);
lean_ctor_set(v___x_175_, 2, v___x_171_);
lean_ctor_set(v___x_175_, 3, v___x_171_);
lean_ctor_set_usize(v___x_175_, 4, v___x_170_);
return v___x_175_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_176_ = lean_box(1);
v___x_177_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__4);
v___x_178_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1);
v___x_179_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
lean_ctor_set(v___x_179_, 1, v___x_177_);
lean_ctor_set(v___x_179_, 2, v___x_176_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg(lean_object* v_msgData_180_, lean_object* v___y_181_){
_start:
{
lean_object* v___x_183_; lean_object* v_env_184_; lean_object* v___x_185_; lean_object* v_scopes_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v_opts_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_183_ = lean_st_ref_get(v___y_181_);
v_env_184_ = lean_ctor_get(v___x_183_, 0);
lean_inc_ref(v_env_184_);
lean_dec(v___x_183_);
v___x_185_ = lean_st_ref_get(v___y_181_);
v_scopes_186_ = lean_ctor_get(v___x_185_, 2);
lean_inc(v_scopes_186_);
lean_dec(v___x_185_);
v___x_187_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_188_ = l_List_head_x21___redArg(v___x_187_, v_scopes_186_);
lean_dec(v_scopes_186_);
v_opts_189_ = lean_ctor_get(v___x_188_, 1);
lean_inc_ref(v_opts_189_);
lean_dec(v___x_188_);
v___x_190_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__2);
v___x_191_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__5);
v___x_192_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_192_, 0, v_env_184_);
lean_ctor_set(v___x_192_, 1, v___x_190_);
lean_ctor_set(v___x_192_, 2, v___x_191_);
lean_ctor_set(v___x_192_, 3, v_opts_189_);
v___x_193_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
lean_ctor_set(v___x_193_, 1, v_msgData_180_);
v___x_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___boxed(lean_object* v_msgData_195_, lean_object* v___y_196_, lean_object* v___y_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg(v_msgData_195_, v___y_196_);
lean_dec(v___y_196_);
return v_res_198_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0(uint8_t v___y_200_, uint8_t v_suppressElabErrors_201_, lean_object* v_x_202_){
_start:
{
if (lean_obj_tag(v_x_202_) == 1)
{
lean_object* v_pre_203_; 
v_pre_203_ = lean_ctor_get(v_x_202_, 0);
if (lean_obj_tag(v_pre_203_) == 0)
{
lean_object* v_str_204_; lean_object* v___x_205_; uint8_t v___x_206_; 
v_str_204_ = lean_ctor_get(v_x_202_, 1);
v___x_205_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0___closed__0));
v___x_206_ = lean_string_dec_eq(v_str_204_, v___x_205_);
if (v___x_206_ == 0)
{
return v___y_200_;
}
else
{
return v_suppressElabErrors_201_;
}
}
else
{
return v___y_200_;
}
}
else
{
return v___y_200_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0___boxed(lean_object* v___y_207_, lean_object* v_suppressElabErrors_208_, lean_object* v_x_209_){
_start:
{
uint8_t v___y_26049__boxed_210_; uint8_t v_suppressElabErrors_boxed_211_; uint8_t v_res_212_; lean_object* v_r_213_; 
v___y_26049__boxed_210_ = lean_unbox(v___y_207_);
v_suppressElabErrors_boxed_211_ = lean_unbox(v_suppressElabErrors_208_);
v_res_212_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0(v___y_26049__boxed_210_, v_suppressElabErrors_boxed_211_, v_x_209_);
lean_dec(v_x_209_);
v_r_213_ = lean_box(v_res_212_);
return v_r_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6(lean_object* v_ref_215_, lean_object* v_msgData_216_, uint8_t v_severity_217_, uint8_t v_isSilent_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
lean_object* v___y_223_; uint8_t v___y_224_; uint8_t v___y_225_; lean_object* v___y_226_; lean_object* v___y_227_; lean_object* v___y_228_; lean_object* v___y_229_; lean_object* v___y_230_; uint8_t v___y_286_; uint8_t v___y_287_; uint8_t v___y_288_; lean_object* v___y_289_; lean_object* v___y_290_; uint8_t v___y_314_; uint8_t v___y_315_; uint8_t v___y_316_; lean_object* v___y_317_; lean_object* v___y_318_; uint8_t v___y_322_; uint8_t v___y_323_; uint8_t v___y_324_; uint8_t v___x_339_; uint8_t v___y_341_; uint8_t v___y_342_; uint8_t v___y_343_; uint8_t v___y_345_; uint8_t v___x_357_; 
v___x_339_ = 2;
v___x_357_ = l_Lean_instBEqMessageSeverity_beq(v_severity_217_, v___x_339_);
if (v___x_357_ == 0)
{
v___y_345_ = v___x_357_;
goto v___jp_344_;
}
else
{
uint8_t v___x_358_; 
lean_inc_ref(v_msgData_216_);
v___x_358_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_216_);
v___y_345_ = v___x_358_;
goto v___jp_344_;
}
v___jp_222_:
{
lean_object* v___x_231_; 
v___x_231_ = l_Lean_Elab_Command_getScope___redArg(v___y_230_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v_a_232_; lean_object* v___x_233_; 
v_a_232_ = lean_ctor_get(v___x_231_, 0);
lean_inc(v_a_232_);
lean_dec_ref_known(v___x_231_, 1);
v___x_233_ = l_Lean_Elab_Command_getScope___redArg(v___y_230_);
if (lean_obj_tag(v___x_233_) == 0)
{
lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_268_; 
v_a_234_ = lean_ctor_get(v___x_233_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_268_ == 0)
{
v___x_236_ = v___x_233_;
v_isShared_237_ = v_isSharedCheck_268_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_dec(v___x_233_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_268_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_238_; lean_object* v_currNamespace_239_; lean_object* v_openDecls_240_; lean_object* v_env_241_; lean_object* v_messages_242_; lean_object* v_scopes_243_; lean_object* v_usedQuotCtxts_244_; lean_object* v_nextMacroScope_245_; lean_object* v_maxRecDepth_246_; lean_object* v_ngen_247_; lean_object* v_auxDeclNGen_248_; lean_object* v_infoState_249_; lean_object* v_traceState_250_; lean_object* v_snapshotTasks_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_267_; 
v___x_238_ = lean_st_ref_take(v___y_230_);
v_currNamespace_239_ = lean_ctor_get(v_a_232_, 2);
lean_inc(v_currNamespace_239_);
lean_dec(v_a_232_);
v_openDecls_240_ = lean_ctor_get(v_a_234_, 3);
lean_inc(v_openDecls_240_);
lean_dec(v_a_234_);
v_env_241_ = lean_ctor_get(v___x_238_, 0);
v_messages_242_ = lean_ctor_get(v___x_238_, 1);
v_scopes_243_ = lean_ctor_get(v___x_238_, 2);
v_usedQuotCtxts_244_ = lean_ctor_get(v___x_238_, 3);
v_nextMacroScope_245_ = lean_ctor_get(v___x_238_, 4);
v_maxRecDepth_246_ = lean_ctor_get(v___x_238_, 5);
v_ngen_247_ = lean_ctor_get(v___x_238_, 6);
v_auxDeclNGen_248_ = lean_ctor_get(v___x_238_, 7);
v_infoState_249_ = lean_ctor_get(v___x_238_, 8);
v_traceState_250_ = lean_ctor_get(v___x_238_, 9);
v_snapshotTasks_251_ = lean_ctor_get(v___x_238_, 10);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_267_ == 0)
{
v___x_253_ = v___x_238_;
v_isShared_254_ = v_isSharedCheck_267_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_snapshotTasks_251_);
lean_inc(v_traceState_250_);
lean_inc(v_infoState_249_);
lean_inc(v_auxDeclNGen_248_);
lean_inc(v_ngen_247_);
lean_inc(v_maxRecDepth_246_);
lean_inc(v_nextMacroScope_245_);
lean_inc(v_usedQuotCtxts_244_);
lean_inc(v_scopes_243_);
lean_inc(v_messages_242_);
lean_inc(v_env_241_);
lean_dec(v___x_238_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_267_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_260_; 
v___x_255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_255_, 0, v_currNamespace_239_);
lean_ctor_set(v___x_255_, 1, v_openDecls_240_);
v___x_256_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
lean_ctor_set(v___x_256_, 1, v___y_226_);
lean_inc_ref(v___y_228_);
lean_inc_ref(v___y_229_);
v___x_257_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_257_, 0, v___y_229_);
lean_ctor_set(v___x_257_, 1, v___y_223_);
lean_ctor_set(v___x_257_, 2, v___y_227_);
lean_ctor_set(v___x_257_, 3, v___y_228_);
lean_ctor_set(v___x_257_, 4, v___x_256_);
lean_ctor_set_uint8(v___x_257_, sizeof(void*)*5, v___y_225_);
lean_ctor_set_uint8(v___x_257_, sizeof(void*)*5 + 1, v___y_224_);
lean_ctor_set_uint8(v___x_257_, sizeof(void*)*5 + 2, v_isSilent_218_);
v___x_258_ = l_Lean_MessageLog_add(v___x_257_, v_messages_242_);
if (v_isShared_254_ == 0)
{
lean_ctor_set(v___x_253_, 1, v___x_258_);
v___x_260_ = v___x_253_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_env_241_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v___x_258_);
lean_ctor_set(v_reuseFailAlloc_266_, 2, v_scopes_243_);
lean_ctor_set(v_reuseFailAlloc_266_, 3, v_usedQuotCtxts_244_);
lean_ctor_set(v_reuseFailAlloc_266_, 4, v_nextMacroScope_245_);
lean_ctor_set(v_reuseFailAlloc_266_, 5, v_maxRecDepth_246_);
lean_ctor_set(v_reuseFailAlloc_266_, 6, v_ngen_247_);
lean_ctor_set(v_reuseFailAlloc_266_, 7, v_auxDeclNGen_248_);
lean_ctor_set(v_reuseFailAlloc_266_, 8, v_infoState_249_);
lean_ctor_set(v_reuseFailAlloc_266_, 9, v_traceState_250_);
lean_ctor_set(v_reuseFailAlloc_266_, 10, v_snapshotTasks_251_);
v___x_260_ = v_reuseFailAlloc_266_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_264_; 
v___x_261_ = lean_st_ref_set(v___y_230_, v___x_260_);
v___x_262_ = lean_box(0);
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 0, v___x_262_);
v___x_264_ = v___x_236_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_262_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
}
}
else
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
lean_dec(v_a_232_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
lean_dec_ref(v___y_223_);
v_a_269_ = lean_ctor_get(v___x_233_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_276_ == 0)
{
v___x_271_ = v___x_233_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_233_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_a_269_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
else
{
lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_284_; 
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
lean_dec_ref(v___y_223_);
v_a_277_ = lean_ctor_get(v___x_231_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_284_ == 0)
{
v___x_279_ = v___x_231_;
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_dec(v___x_231_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_282_; 
if (v_isShared_280_ == 0)
{
v___x_282_ = v___x_279_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_a_277_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
}
v___jp_285_:
{
lean_object* v_fileName_291_; lean_object* v_fileMap_292_; uint8_t v_suppressElabErrors_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v_a_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_312_; 
v_fileName_291_ = lean_ctor_get(v___y_219_, 0);
v_fileMap_292_ = lean_ctor_get(v___y_219_, 1);
v_suppressElabErrors_293_ = lean_ctor_get_uint8(v___y_219_, sizeof(void*)*10);
v___x_294_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_216_);
v___x_295_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg(v___x_294_, v___y_220_);
v_a_296_ = lean_ctor_get(v___x_295_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_312_ == 0)
{
v___x_298_ = v___x_295_;
v_isShared_299_ = v_isSharedCheck_312_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_a_296_);
lean_dec(v___x_295_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_312_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
lean_inc_ref_n(v_fileMap_292_, 2);
v___x_300_ = l_Lean_FileMap_toPosition(v_fileMap_292_, v___y_289_);
lean_dec(v___y_289_);
v___x_301_ = l_Lean_FileMap_toPosition(v_fileMap_292_, v___y_290_);
lean_dec(v___y_290_);
v___x_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
v___x_303_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___closed__0));
if (v_suppressElabErrors_293_ == 0)
{
lean_del_object(v___x_298_);
v___y_223_ = v___x_300_;
v___y_224_ = v___y_288_;
v___y_225_ = v___y_287_;
v___y_226_ = v_a_296_;
v___y_227_ = v___x_302_;
v___y_228_ = v___x_303_;
v___y_229_ = v_fileName_291_;
v___y_230_ = v___y_220_;
goto v___jp_222_;
}
else
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___f_306_; uint8_t v___x_307_; 
v___x_304_ = lean_box(v___y_286_);
v___x_305_ = lean_box(v_suppressElabErrors_293_);
v___f_306_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0___boxed), 3, 2);
lean_closure_set(v___f_306_, 0, v___x_304_);
lean_closure_set(v___f_306_, 1, v___x_305_);
lean_inc(v_a_296_);
v___x_307_ = l_Lean_MessageData_hasTag(v___f_306_, v_a_296_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; lean_object* v___x_310_; 
lean_dec_ref_known(v___x_302_, 1);
lean_dec_ref(v___x_300_);
lean_dec(v_a_296_);
v___x_308_ = lean_box(0);
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 0, v___x_308_);
v___x_310_ = v___x_298_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v___x_308_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
else
{
lean_del_object(v___x_298_);
v___y_223_ = v___x_300_;
v___y_224_ = v___y_288_;
v___y_225_ = v___y_287_;
v___y_226_ = v_a_296_;
v___y_227_ = v___x_302_;
v___y_228_ = v___x_303_;
v___y_229_ = v_fileName_291_;
v___y_230_ = v___y_220_;
goto v___jp_222_;
}
}
}
}
v___jp_313_:
{
lean_object* v___x_319_; 
v___x_319_ = l_Lean_Syntax_getTailPos_x3f(v___y_317_, v___y_316_);
lean_dec(v___y_317_);
if (lean_obj_tag(v___x_319_) == 0)
{
lean_inc(v___y_318_);
v___y_286_ = v___y_314_;
v___y_287_ = v___y_316_;
v___y_288_ = v___y_315_;
v___y_289_ = v___y_318_;
v___y_290_ = v___y_318_;
goto v___jp_285_;
}
else
{
lean_object* v_val_320_; 
v_val_320_ = lean_ctor_get(v___x_319_, 0);
lean_inc(v_val_320_);
lean_dec_ref_known(v___x_319_, 1);
v___y_286_ = v___y_314_;
v___y_287_ = v___y_316_;
v___y_288_ = v___y_315_;
v___y_289_ = v___y_318_;
v___y_290_ = v_val_320_;
goto v___jp_285_;
}
}
v___jp_321_:
{
lean_object* v___x_325_; 
v___x_325_ = l_Lean_Elab_Command_getRef___redArg(v___y_219_);
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v_a_326_; lean_object* v_ref_327_; lean_object* v___x_328_; 
v_a_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_a_326_);
lean_dec_ref_known(v___x_325_, 1);
v_ref_327_ = l_Lean_replaceRef(v_ref_215_, v_a_326_);
lean_dec(v_a_326_);
v___x_328_ = l_Lean_Syntax_getPos_x3f(v_ref_327_, v___y_323_);
if (lean_obj_tag(v___x_328_) == 0)
{
lean_object* v___x_329_; 
v___x_329_ = lean_unsigned_to_nat(0u);
v___y_314_ = v___y_322_;
v___y_315_ = v___y_324_;
v___y_316_ = v___y_323_;
v___y_317_ = v_ref_327_;
v___y_318_ = v___x_329_;
goto v___jp_313_;
}
else
{
lean_object* v_val_330_; 
v_val_330_ = lean_ctor_get(v___x_328_, 0);
lean_inc(v_val_330_);
lean_dec_ref_known(v___x_328_, 1);
v___y_314_ = v___y_322_;
v___y_315_ = v___y_324_;
v___y_316_ = v___y_323_;
v___y_317_ = v_ref_327_;
v___y_318_ = v_val_330_;
goto v___jp_313_;
}
}
else
{
lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_338_; 
lean_dec_ref(v_msgData_216_);
v_a_331_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_338_ == 0)
{
v___x_333_ = v___x_325_;
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v___x_325_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_336_; 
if (v_isShared_334_ == 0)
{
v___x_336_ = v___x_333_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_a_331_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
}
v___jp_340_:
{
if (v___y_343_ == 0)
{
v___y_322_ = v___y_341_;
v___y_323_ = v___y_342_;
v___y_324_ = v_severity_217_;
goto v___jp_321_;
}
else
{
v___y_322_ = v___y_341_;
v___y_323_ = v___y_342_;
v___y_324_ = v___x_339_;
goto v___jp_321_;
}
}
v___jp_344_:
{
if (v___y_345_ == 0)
{
lean_object* v___x_346_; lean_object* v_scopes_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v_opts_350_; uint8_t v___x_351_; uint8_t v___x_352_; 
v___x_346_ = lean_st_ref_get(v___y_220_);
v_scopes_347_ = lean_ctor_get(v___x_346_, 2);
lean_inc(v_scopes_347_);
lean_dec(v___x_346_);
v___x_348_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_349_ = l_List_head_x21___redArg(v___x_348_, v_scopes_347_);
lean_dec(v_scopes_347_);
v_opts_350_ = lean_ctor_get(v___x_349_, 1);
lean_inc_ref(v_opts_350_);
lean_dec(v___x_349_);
v___x_351_ = 1;
v___x_352_ = l_Lean_instBEqMessageSeverity_beq(v_severity_217_, v___x_351_);
if (v___x_352_ == 0)
{
lean_dec_ref(v_opts_350_);
v___y_341_ = v___y_345_;
v___y_342_ = v___y_345_;
v___y_343_ = v___x_352_;
goto v___jp_340_;
}
else
{
lean_object* v___x_353_; uint8_t v___x_354_; 
v___x_353_ = l_Lean_warningAsError;
v___x_354_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__10(v_opts_350_, v___x_353_);
lean_dec_ref(v_opts_350_);
v___y_341_ = v___y_345_;
v___y_342_ = v___y_345_;
v___y_343_ = v___x_354_;
goto v___jp_340_;
}
}
else
{
lean_object* v___x_355_; lean_object* v___x_356_; 
lean_dec_ref(v_msgData_216_);
v___x_355_ = lean_box(0);
v___x_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
return v___x_356_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___boxed(lean_object* v_ref_359_, lean_object* v_msgData_360_, lean_object* v_severity_361_, lean_object* v_isSilent_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
uint8_t v_severity_boxed_366_; uint8_t v_isSilent_boxed_367_; lean_object* v_res_368_; 
v_severity_boxed_366_ = lean_unbox(v_severity_361_);
v_isSilent_boxed_367_ = lean_unbox(v_isSilent_362_);
v_res_368_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6(v_ref_359_, v_msgData_360_, v_severity_boxed_366_, v_isSilent_boxed_367_, v___y_363_, v___y_364_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v_ref_359_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5(lean_object* v_ref_369_, lean_object* v_msgData_370_, lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
uint8_t v___x_374_; uint8_t v___x_375_; lean_object* v___x_376_; 
v___x_374_ = 1;
v___x_375_ = 0;
v___x_376_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6(v_ref_369_, v_msgData_370_, v___x_374_, v___x_375_, v___y_371_, v___y_372_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5___boxed(lean_object* v_ref_377_, lean_object* v_msgData_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5(v_ref_377_, v_msgData_378_, v___y_379_, v___y_380_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec(v_ref_377_);
return v_res_382_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__1(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__0));
v___x_385_ = l_Lean_stringToMessageData(v___x_384_);
return v___x_385_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__3(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__2));
v___x_388_ = l_Lean_stringToMessageData(v___x_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4(lean_object* v_linterOption_389_, lean_object* v_stx_390_, lean_object* v_msg_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v_name_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_412_; 
v_name_395_ = lean_ctor_get(v_linterOption_389_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v_linterOption_389_);
if (v_isSharedCheck_412_ == 0)
{
lean_object* v_unused_413_; 
v_unused_413_ = lean_ctor_get(v_linterOption_389_, 1);
lean_dec(v_unused_413_);
v___x_397_ = v_linterOption_389_;
v_isShared_398_ = v_isSharedCheck_412_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_name_395_);
lean_dec(v_linterOption_389_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_412_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_402_; 
v___x_399_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__1);
lean_inc(v_name_395_);
v___x_400_ = l_Lean_MessageData_ofName(v_name_395_);
if (v_isShared_398_ == 0)
{
lean_ctor_set_tag(v___x_397_, 7);
lean_ctor_set(v___x_397_, 1, v___x_400_);
lean_ctor_set(v___x_397_, 0, v___x_399_);
v___x_402_ = v___x_397_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_399_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v___x_400_);
v___x_402_ = v_reuseFailAlloc_411_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v_disable_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_403_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__3);
v___x_404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_402_);
lean_ctor_set(v___x_404_, 1, v___x_403_);
v_disable_405_ = l_Lean_MessageData_note(v___x_404_);
v___x_406_ = l_Lean_Linter_linterMessageTag;
v___x_407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_407_, 0, v_msg_391_);
lean_ctor_set(v___x_407_, 1, v_disable_405_);
v___x_408_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_406_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
v___x_409_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_409_, 0, v_name_395_);
lean_ctor_set(v___x_409_, 1, v___x_408_);
v___x_410_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5(v_stx_390_, v___x_409_, v___y_392_, v___y_393_);
return v___x_410_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___boxed(lean_object* v_linterOption_414_, lean_object* v_stx_415_, lean_object* v_msg_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4(v_linterOption_414_, v_stx_415_, v_msg_416_, v___y_417_, v___y_418_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v_stx_415_);
return v_res_420_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__2(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__1));
v___x_425_ = l_Lean_MessageData_ofFormat(v___x_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5(lean_object* v_as_441_, size_t v_sz_442_, size_t v_i_443_, lean_object* v_b_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v_a_449_; uint8_t v___x_453_; 
v___x_453_ = lean_usize_dec_lt(v_i_443_, v_sz_442_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; 
v___x_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_454_, 0, v_b_444_);
return v___x_454_;
}
else
{
lean_object* v___x_455_; lean_object* v_patHead_457_; lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v_a_463_; lean_object* v___x_464_; uint8_t v___x_465_; 
v___x_455_ = lean_box(0);
v_a_463_ = lean_array_uget_borrowed(v_as_441_, v_i_443_);
v___x_464_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__4));
lean_inc(v_a_463_);
v___x_465_ = l_Lean_Syntax_isOfKind(v_a_463_, v___x_464_);
if (v___x_465_ == 0)
{
v_a_449_ = v___x_455_;
goto v___jp_448_;
}
else
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; uint8_t v___x_469_; 
v___x_466_ = lean_unsigned_to_nat(1u);
v___x_467_ = l_Lean_Syntax_getArg(v_a_463_, v___x_466_);
v___x_468_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__6));
lean_inc(v___x_467_);
v___x_469_ = l_Lean_Syntax_isOfKind(v___x_467_, v___x_468_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_470_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__8));
lean_inc(v___x_467_);
v___x_471_ = l_Lean_Syntax_isOfKind(v___x_467_, v___x_470_);
if (v___x_471_ == 0)
{
lean_dec(v___x_467_);
v_a_449_ = v___x_455_;
goto v___jp_448_;
}
else
{
v_patHead_457_ = v___x_467_;
v___y_458_ = v___y_445_;
v___y_459_ = v___y_446_;
goto v___jp_456_;
}
}
else
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; uint8_t v___x_475_; 
v___x_472_ = lean_unsigned_to_nat(0u);
v___x_473_ = l_Lean_Syntax_getArg(v___x_467_, v___x_472_);
lean_dec(v___x_467_);
v___x_474_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__8));
lean_inc(v___x_473_);
v___x_475_ = l_Lean_Syntax_isOfKind(v___x_473_, v___x_474_);
if (v___x_475_ == 0)
{
lean_dec(v___x_473_);
v_a_449_ = v___x_455_;
goto v___jp_448_;
}
else
{
v_patHead_457_ = v___x_473_;
v___y_458_ = v___y_445_;
v___y_459_ = v___y_446_;
goto v___jp_456_;
}
}
}
v___jp_456_:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_460_ = l_Lean_Linter_linter_suspiciousUnexpanderPatterns;
v___x_461_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__2);
v___x_462_ = l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4(v___x_460_, v_patHead_457_, v___x_461_, v___y_458_, v___y_459_);
lean_dec(v_patHead_457_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_dec_ref_known(v___x_462_, 1);
v_a_449_ = v___x_455_;
goto v___jp_448_;
}
else
{
return v___x_462_;
}
}
}
v___jp_448_:
{
size_t v___x_450_; size_t v___x_451_; 
v___x_450_ = ((size_t)1ULL);
v___x_451_ = lean_usize_add(v_i_443_, v___x_450_);
v_i_443_ = v___x_451_;
v_b_444_ = v_a_449_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___boxed(lean_object* v_as_476_, lean_object* v_sz_477_, lean_object* v_i_478_, lean_object* v_b_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
size_t v_sz_boxed_483_; size_t v_i_boxed_484_; lean_object* v_res_485_; 
v_sz_boxed_483_ = lean_unbox_usize(v_sz_477_);
lean_dec(v_sz_477_);
v_i_boxed_484_ = lean_unbox_usize(v_i_478_);
lean_dec(v_i_478_);
v_res_485_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5(v_as_476_, v_sz_boxed_483_, v_i_boxed_484_, v_b_479_, v___y_480_, v___y_481_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec_ref(v_as_476_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2(size_t v_sz_492_, size_t v_i_493_, lean_object* v_bs_494_){
_start:
{
uint8_t v___x_495_; 
v___x_495_ = lean_usize_dec_lt(v_i_493_, v_sz_492_);
if (v___x_495_ == 0)
{
lean_object* v___x_496_; 
v___x_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_496_, 0, v_bs_494_);
return v___x_496_;
}
else
{
lean_object* v_v_497_; lean_object* v___x_498_; uint8_t v___x_499_; 
v_v_497_ = lean_array_uget_borrowed(v_bs_494_, v_i_493_);
v___x_498_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__1));
lean_inc(v_v_497_);
v___x_499_ = l_Lean_Syntax_isOfKind(v_v_497_, v___x_498_);
if (v___x_499_ == 0)
{
lean_object* v___x_500_; 
lean_dec_ref(v_bs_494_);
v___x_500_ = lean_box(0);
return v___x_500_;
}
else
{
lean_object* v___x_501_; lean_object* v___x_502_; uint8_t v___x_503_; 
v___x_501_ = lean_unsigned_to_nat(1u);
v___x_502_ = l_Lean_Syntax_getArg(v_v_497_, v___x_501_);
lean_inc(v___x_502_);
v___x_503_ = l_Lean_Syntax_matchesNull(v___x_502_, v___x_501_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; 
lean_dec(v___x_502_);
lean_dec_ref(v_bs_494_);
v___x_504_ = lean_box(0);
return v___x_504_;
}
else
{
lean_object* v___x_505_; lean_object* v___x_506_; uint8_t v___x_507_; 
v___x_505_ = lean_unsigned_to_nat(0u);
v___x_506_ = l_Lean_Syntax_getArg(v___x_502_, v___x_505_);
lean_dec(v___x_502_);
lean_inc(v___x_506_);
v___x_507_ = l_Lean_Syntax_matchesNull(v___x_506_, v___x_501_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; 
lean_dec(v___x_506_);
lean_dec_ref(v_bs_494_);
v___x_508_ = lean_box(0);
return v___x_508_;
}
else
{
lean_object* v_bs_x27_509_; lean_object* v___x_510_; size_t v___x_511_; size_t v___x_512_; lean_object* v___x_513_; 
v_bs_x27_509_ = lean_array_uset(v_bs_494_, v_i_493_, v___x_505_);
v___x_510_ = l_Lean_Syntax_getArg(v___x_506_, v___x_505_);
lean_dec(v___x_506_);
v___x_511_ = ((size_t)1ULL);
v___x_512_ = lean_usize_add(v_i_493_, v___x_511_);
v___x_513_ = lean_array_uset(v_bs_x27_509_, v_i_493_, v___x_510_);
v_i_493_ = v___x_512_;
v_bs_494_ = v___x_513_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___boxed(lean_object* v_sz_515_, lean_object* v_i_516_, lean_object* v_bs_517_){
_start:
{
size_t v_sz_boxed_518_; size_t v_i_boxed_519_; lean_object* v_res_520_; 
v_sz_boxed_518_ = lean_unbox_usize(v_sz_515_);
lean_dec(v_sz_515_);
v_i_boxed_519_ = lean_unbox_usize(v_i_516_);
lean_dec(v_i_516_);
v_res_520_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2(v_sz_boxed_518_, v_i_boxed_519_, v_bs_517_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__6(uint8_t v___x_521_, lean_object* v_as_522_, size_t v_i_523_, size_t v_stop_524_, lean_object* v_b_525_){
_start:
{
lean_object* v___y_527_; uint8_t v___x_531_; 
v___x_531_ = lean_usize_dec_eq(v_i_523_, v_stop_524_);
if (v___x_531_ == 0)
{
lean_object* v_fst_532_; uint8_t v___x_533_; 
v_fst_532_ = lean_ctor_get(v_b_525_, 0);
v___x_533_ = lean_unbox(v_fst_532_);
if (v___x_533_ == 0)
{
lean_object* v_snd_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_542_; 
v_snd_534_ = lean_ctor_get(v_b_525_, 1);
v_isSharedCheck_542_ = !lean_is_exclusive(v_b_525_);
if (v_isSharedCheck_542_ == 0)
{
lean_object* v_unused_543_; 
v_unused_543_ = lean_ctor_get(v_b_525_, 0);
lean_dec(v_unused_543_);
v___x_536_ = v_b_525_;
v_isShared_537_ = v_isSharedCheck_542_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_snd_534_);
lean_dec(v_b_525_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_542_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_538_; lean_object* v___x_540_; 
v___x_538_ = lean_box(v___x_521_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 0, v___x_538_);
v___x_540_ = v___x_536_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v___x_538_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v_snd_534_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
v___y_527_ = v___x_540_;
goto v___jp_526_;
}
}
}
else
{
lean_object* v_snd_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_554_; 
v_snd_544_ = lean_ctor_get(v_b_525_, 1);
v_isSharedCheck_554_ = !lean_is_exclusive(v_b_525_);
if (v_isSharedCheck_554_ == 0)
{
lean_object* v_unused_555_; 
v_unused_555_ = lean_ctor_get(v_b_525_, 0);
lean_dec(v_unused_555_);
v___x_546_ = v_b_525_;
v_isShared_547_ = v_isSharedCheck_554_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_snd_544_);
lean_dec(v_b_525_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_554_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_552_; 
v___x_548_ = lean_array_uget_borrowed(v_as_522_, v_i_523_);
lean_inc(v___x_548_);
v___x_549_ = lean_array_push(v_snd_544_, v___x_548_);
v___x_550_ = lean_box(v___x_531_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 1, v___x_549_);
lean_ctor_set(v___x_546_, 0, v___x_550_);
v___x_552_ = v___x_546_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_550_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v___x_549_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
v___y_527_ = v___x_552_;
goto v___jp_526_;
}
}
}
}
else
{
return v_b_525_;
}
v___jp_526_:
{
size_t v___x_528_; size_t v___x_529_; 
v___x_528_ = ((size_t)1ULL);
v___x_529_ = lean_usize_add(v_i_523_, v___x_528_);
v_i_523_ = v___x_529_;
v_b_525_ = v___y_527_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__6___boxed(lean_object* v___x_556_, lean_object* v_as_557_, lean_object* v_i_558_, lean_object* v_stop_559_, lean_object* v_b_560_){
_start:
{
uint8_t v___x_26579__boxed_561_; size_t v_i_boxed_562_; size_t v_stop_boxed_563_; lean_object* v_res_564_; 
v___x_26579__boxed_561_ = lean_unbox(v___x_556_);
v_i_boxed_562_ = lean_unbox_usize(v_i_558_);
lean_dec(v_i_558_);
v_stop_boxed_563_ = lean_unbox_usize(v_stop_559_);
lean_dec(v_stop_559_);
v_res_564_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__6(v___x_26579__boxed_561_, v_as_557_, v_i_boxed_562_, v_stop_boxed_563_, v_b_560_);
lean_dec_ref(v_as_557_);
return v_res_564_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3(uint8_t v___x_575_, lean_object* v_as_576_, size_t v_i_577_, size_t v_stop_578_){
_start:
{
uint8_t v___x_579_; 
v___x_579_ = lean_usize_dec_eq(v_i_577_, v_stop_578_);
if (v___x_579_ == 0)
{
uint8_t v___x_580_; uint8_t v___y_582_; lean_object* v___x_586_; lean_object* v___x_587_; uint8_t v___x_588_; 
v___x_580_ = 1;
v___x_586_ = lean_array_uget_borrowed(v_as_576_, v_i_577_);
v___x_587_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__2));
lean_inc(v___x_586_);
v___x_588_ = l_Lean_Syntax_isOfKind(v___x_586_, v___x_587_);
if (v___x_588_ == 0)
{
v___y_582_ = v___x_588_;
goto v___jp_581_;
}
else
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; uint8_t v___x_592_; 
v___x_589_ = lean_unsigned_to_nat(0u);
v___x_590_ = l_Lean_Syntax_getArg(v___x_586_, v___x_589_);
v___x_591_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__4));
v___x_592_ = l_Lean_Syntax_matchesIdent(v___x_590_, v___x_591_);
lean_dec(v___x_590_);
if (v___x_592_ == 0)
{
v___y_582_ = v___x_592_;
goto v___jp_581_;
}
else
{
lean_object* v___x_593_; lean_object* v___x_594_; uint8_t v___x_595_; 
v___x_593_ = lean_unsigned_to_nat(1u);
v___x_594_ = l_Lean_Syntax_getArg(v___x_586_, v___x_593_);
v___x_595_ = l_Lean_Syntax_matchesNull(v___x_594_, v___x_593_);
if (v___x_595_ == 0)
{
v___y_582_ = v___x_595_;
goto v___jp_581_;
}
else
{
v___y_582_ = v___x_575_;
goto v___jp_581_;
}
}
}
v___jp_581_:
{
if (v___y_582_ == 0)
{
size_t v___x_583_; size_t v___x_584_; 
v___x_583_ = ((size_t)1ULL);
v___x_584_ = lean_usize_add(v_i_577_, v___x_583_);
v_i_577_ = v___x_584_;
goto _start;
}
else
{
return v___x_580_;
}
}
}
else
{
uint8_t v___x_596_; 
v___x_596_ = 0;
return v___x_596_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___boxed(lean_object* v___x_597_, lean_object* v_as_598_, lean_object* v_i_599_, lean_object* v_stop_600_){
_start:
{
uint8_t v___x_26664__boxed_601_; size_t v_i_boxed_602_; size_t v_stop_boxed_603_; uint8_t v_res_604_; lean_object* v_r_605_; 
v___x_26664__boxed_601_ = lean_unbox(v___x_597_);
v_i_boxed_602_ = lean_unbox_usize(v_i_599_);
lean_dec(v_i_599_);
v_stop_boxed_603_ = lean_unbox_usize(v_stop_600_);
lean_dec(v_stop_600_);
v_res_604_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3(v___x_26664__boxed_601_, v_as_598_, v_i_boxed_602_, v_stop_boxed_603_);
lean_dec_ref(v_as_598_);
v_r_605_ = lean_box(v_res_604_);
return v_r_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0(lean_object* v_cmdStx_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v___x_668_; lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_888_; 
v___x_668_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0(v___y_662_, v___y_663_);
v_a_669_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_888_ == 0)
{
v___x_671_ = v___x_668_;
v_isShared_672_ = v_isSharedCheck_888_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_668_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_888_;
goto v_resetjp_670_;
}
v___jp_665_:
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = lean_box(0);
v___x_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_667_, 0, v___x_666_);
return v___x_667_;
}
v_resetjp_670_:
{
uint8_t v___x_673_; 
v___x_673_ = l_Lean_Linter_getLinterSuspiciousUnexpanderPatterns(v_a_669_);
lean_dec(v_a_669_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; lean_object* v___x_676_; 
lean_dec(v_cmdStx_661_);
v___x_674_ = lean_box(0);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v___x_674_);
v___x_676_ = v___x_671_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_674_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
else
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; uint8_t v___x_681_; 
v___x_678_ = ((lean_object*)(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_));
v___x_679_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0));
v___x_680_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__2));
lean_inc(v_cmdStx_661_);
v___x_681_ = l_Lean_Syntax_isOfKind(v_cmdStx_661_, v___x_680_);
if (v___x_681_ == 0)
{
lean_object* v___x_682_; lean_object* v___x_684_; 
lean_dec(v_cmdStx_661_);
v___x_682_ = lean_box(0);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v___x_682_);
v___x_684_ = v___x_671_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_682_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
else
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; uint8_t v___x_689_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_846_; lean_object* v___y_847_; 
v___x_686_ = lean_unsigned_to_nat(0u);
v___x_687_ = l_Lean_Syntax_getArg(v_cmdStx_661_, v___x_686_);
v___x_688_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__4));
lean_inc(v___x_687_);
v___x_689_ = l_Lean_Syntax_isOfKind(v___x_687_, v___x_688_);
if (v___x_689_ == 0)
{
lean_object* v___x_875_; lean_object* v___x_876_; 
lean_dec(v___x_687_);
lean_del_object(v___x_671_);
lean_dec(v_cmdStx_661_);
v___x_875_ = lean_box(0);
v___x_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_876_, 0, v___x_875_);
return v___x_876_;
}
else
{
lean_object* v___x_877_; uint8_t v___x_878_; 
v___x_877_ = l_Lean_Syntax_getArg(v___x_687_, v___x_686_);
v___x_878_ = l_Lean_Syntax_isNone(v___x_877_);
if (v___x_878_ == 0)
{
lean_object* v___x_879_; uint8_t v___x_880_; 
v___x_879_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_877_);
v___x_880_ = l_Lean_Syntax_matchesNull(v___x_877_, v___x_879_);
if (v___x_880_ == 0)
{
lean_object* v___x_881_; lean_object* v___x_882_; 
lean_dec(v___x_877_);
lean_dec(v___x_687_);
lean_del_object(v___x_671_);
lean_dec(v_cmdStx_661_);
v___x_881_ = lean_box(0);
v___x_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
return v___x_882_;
}
else
{
lean_object* v___x_883_; lean_object* v___x_884_; uint8_t v___x_885_; 
v___x_883_ = l_Lean_Syntax_getArg(v___x_877_, v___x_686_);
lean_dec(v___x_877_);
v___x_884_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__21));
v___x_885_ = l_Lean_Syntax_isOfKind(v___x_883_, v___x_884_);
if (v___x_885_ == 0)
{
lean_object* v___x_886_; lean_object* v___x_887_; 
lean_dec(v___x_687_);
lean_del_object(v___x_671_);
lean_dec(v_cmdStx_661_);
v___x_886_ = lean_box(0);
v___x_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_887_, 0, v___x_886_);
return v___x_887_;
}
else
{
v___y_846_ = v___y_662_;
v___y_847_ = v___y_663_;
goto v___jp_845_;
}
}
}
else
{
lean_dec(v___x_877_);
v___y_846_ = v___y_662_;
v___y_847_ = v___y_663_;
goto v___jp_845_;
}
}
v___jp_690_:
{
size_t v_sz_696_; size_t v___x_697_; lean_object* v___x_698_; 
v_sz_696_ = lean_array_size(v___y_695_);
v___x_697_ = ((size_t)0ULL);
v___x_698_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1(v_sz_696_, v___x_697_, v___y_695_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v___x_699_; lean_object* v___x_701_; 
lean_dec(v___x_687_);
lean_dec(v_cmdStx_661_);
v___x_699_ = lean_box(0);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v___x_699_);
v___x_701_ = v___x_671_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v___x_699_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
else
{
lean_object* v_val_703_; lean_object* v___x_704_; lean_object* v___x_705_; uint8_t v___x_706_; 
v_val_703_ = lean_ctor_get(v___x_698_, 0);
lean_inc(v_val_703_);
lean_dec_ref_known(v___x_698_, 1);
v___x_704_ = lean_unsigned_to_nat(3u);
v___x_705_ = l_Lean_Syntax_getArg(v___x_687_, v___x_704_);
v___x_706_ = l_Lean_Syntax_matchesNull(v___x_705_, v___x_686_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; lean_object* v___x_709_; 
lean_dec(v_val_703_);
lean_dec(v___x_687_);
lean_dec(v_cmdStx_661_);
v___x_707_ = lean_box(0);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v___x_707_);
v___x_709_ = v___x_671_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_707_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
else
{
lean_object* v___x_711_; lean_object* v___x_712_; uint8_t v___x_713_; 
v___x_711_ = lean_unsigned_to_nat(4u);
v___x_712_ = l_Lean_Syntax_getArg(v___x_687_, v___x_711_);
v___x_713_ = l_Lean_Syntax_matchesNull(v___x_712_, v___x_686_);
if (v___x_713_ == 0)
{
lean_object* v___x_714_; lean_object* v___x_716_; 
lean_dec(v_val_703_);
lean_dec(v___x_687_);
lean_dec(v_cmdStx_661_);
v___x_714_ = lean_box(0);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v___x_714_);
v___x_716_ = v___x_671_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_714_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
else
{
lean_object* v___x_718_; lean_object* v___x_719_; uint8_t v___x_720_; 
v___x_718_ = lean_unsigned_to_nat(5u);
v___x_719_ = l_Lean_Syntax_getArg(v___x_687_, v___x_718_);
v___x_720_ = l_Lean_Syntax_matchesNull(v___x_719_, v___x_686_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; lean_object* v___x_723_; 
lean_dec(v_val_703_);
lean_dec(v___x_687_);
lean_dec(v_cmdStx_661_);
v___x_721_ = lean_box(0);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v___x_721_);
v___x_723_ = v___x_671_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_721_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
else
{
lean_object* v___x_725_; lean_object* v___x_726_; uint8_t v___x_727_; 
v___x_725_ = lean_unsigned_to_nat(6u);
v___x_726_ = l_Lean_Syntax_getArg(v___x_687_, v___x_725_);
lean_dec(v___x_687_);
v___x_727_ = l_Lean_Syntax_matchesNull(v___x_726_, v___x_686_);
if (v___x_727_ == 0)
{
lean_object* v___x_728_; lean_object* v___x_730_; 
lean_dec(v_val_703_);
lean_dec(v_cmdStx_661_);
v___x_728_ = lean_box(0);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v___x_728_);
v___x_730_ = v___x_671_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_728_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
else
{
lean_object* v___x_732_; lean_object* v___x_733_; uint8_t v___x_734_; 
v___x_732_ = l_Lean_Syntax_getArg(v_cmdStx_661_, v___y_694_);
lean_dec(v_cmdStx_661_);
v___x_733_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__6));
lean_inc(v___x_732_);
v___x_734_ = l_Lean_Syntax_isOfKind(v___x_732_, v___x_733_);
if (v___x_734_ == 0)
{
lean_object* v___x_735_; lean_object* v___x_737_; 
lean_dec(v___x_732_);
lean_dec(v_val_703_);
v___x_735_ = lean_box(0);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v___x_735_);
v___x_737_ = v___x_671_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_735_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
else
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; uint8_t v___x_742_; 
v___x_739_ = lean_unsigned_to_nat(2u);
v___x_740_ = l_Lean_Syntax_getArg(v___x_732_, v___x_739_);
v___x_741_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__8));
lean_inc(v___x_740_);
v___x_742_ = l_Lean_Syntax_isOfKind(v___x_740_, v___x_741_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; lean_object* v___x_745_; 
lean_dec(v___x_740_);
lean_dec(v___x_732_);
lean_dec(v_val_703_);
v___x_743_ = lean_box(0);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v___x_743_);
v___x_745_ = v___x_671_;
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
v___x_747_ = l_Lean_Syntax_getArg(v___x_740_, v___x_686_);
v___x_748_ = l_Lean_Syntax_matchesNull(v___x_747_, v___x_686_);
if (v___x_748_ == 0)
{
lean_object* v___x_749_; lean_object* v___x_751_; 
lean_dec(v___x_740_);
lean_dec(v___x_732_);
lean_dec(v_val_703_);
v___x_749_ = lean_box(0);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v___x_749_);
v___x_751_ = v___x_671_;
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
lean_object* v___x_753_; uint8_t v___x_754_; 
v___x_753_ = l_Lean_Syntax_getArg(v___x_740_, v___y_694_);
lean_dec(v___x_740_);
lean_inc(v___x_753_);
v___x_754_ = l_Lean_Syntax_matchesNull(v___x_753_, v___y_694_);
if (v___x_754_ == 0)
{
lean_object* v___x_755_; lean_object* v___x_757_; 
lean_dec(v___x_753_);
lean_dec(v___x_732_);
lean_dec(v_val_703_);
v___x_755_ = lean_box(0);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v___x_755_);
v___x_757_ = v___x_671_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_755_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
else
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; uint8_t v___x_762_; 
v___x_759_ = l_Lean_Syntax_getArg(v___x_753_, v___x_686_);
lean_dec(v___x_753_);
v___x_760_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__9));
lean_inc_ref(v___y_691_);
v___x_761_ = l_Lean_Name_mkStr4(v___x_678_, v___x_679_, v___y_691_, v___x_760_);
v___x_762_ = l_Lean_Syntax_isOfKind(v___x_759_, v___x_761_);
lean_dec(v___x_761_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; lean_object* v___x_765_; 
lean_dec(v___x_732_);
lean_dec(v_val_703_);
v___x_763_ = lean_box(0);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v___x_763_);
v___x_765_ = v___x_671_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v___x_763_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
else
{
lean_object* v___x_767_; lean_object* v___x_768_; uint8_t v___x_769_; 
v___x_767_ = l_Lean_Syntax_getArg(v___x_732_, v___x_704_);
v___x_768_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__11));
lean_inc(v___x_767_);
v___x_769_ = l_Lean_Syntax_isOfKind(v___x_767_, v___x_768_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; lean_object* v___x_772_; 
lean_dec(v___x_767_);
lean_dec(v___x_732_);
lean_dec(v_val_703_);
v___x_770_ = lean_box(0);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v___x_770_);
v___x_772_ = v___x_671_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_770_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
else
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; uint8_t v___x_777_; 
v___x_774_ = l_Lean_Syntax_getArg(v___x_767_, v___x_686_);
lean_dec(v___x_767_);
v___x_775_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__12));
lean_inc_ref(v___y_691_);
v___x_776_ = l_Lean_Name_mkStr4(v___x_678_, v___x_679_, v___y_691_, v___x_775_);
lean_inc(v___x_774_);
v___x_777_ = l_Lean_Syntax_isOfKind(v___x_774_, v___x_776_);
lean_dec(v___x_776_);
if (v___x_777_ == 0)
{
lean_object* v___x_778_; lean_object* v___x_780_; 
lean_dec(v___x_774_);
lean_dec(v___x_732_);
lean_dec(v_val_703_);
v___x_778_ = lean_box(0);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v___x_778_);
v___x_780_ = v___x_671_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_778_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
else
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; uint8_t v___x_785_; 
v___x_782_ = l_Lean_Syntax_getArg(v___x_774_, v___x_686_);
v___x_783_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__13));
lean_inc_ref(v___y_691_);
v___x_784_ = l_Lean_Name_mkStr4(v___x_678_, v___x_679_, v___y_691_, v___x_783_);
lean_inc(v___x_782_);
v___x_785_ = l_Lean_Syntax_isOfKind(v___x_782_, v___x_784_);
lean_dec(v___x_784_);
if (v___x_785_ == 0)
{
lean_object* v___x_786_; lean_object* v___x_788_; 
lean_dec(v___x_782_);
lean_dec(v___x_774_);
lean_dec(v___x_732_);
lean_dec(v_val_703_);
v___x_786_ = lean_box(0);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v___x_786_);
v___x_788_ = v___x_671_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_786_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
else
{
lean_object* v___x_790_; lean_object* v___x_791_; size_t v_sz_792_; lean_object* v___x_793_; 
v___x_790_ = l_Lean_Syntax_getArg(v___x_782_, v___x_686_);
lean_dec(v___x_782_);
v___x_791_ = l_Lean_Syntax_getArgs(v___x_790_);
lean_dec(v___x_790_);
v_sz_792_ = lean_array_size(v___x_791_);
v___x_793_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2(v_sz_792_, v___x_697_, v___x_791_);
if (lean_obj_tag(v___x_793_) == 0)
{
lean_object* v___x_794_; lean_object* v___x_796_; 
lean_dec(v___x_774_);
lean_dec(v___x_732_);
lean_dec(v_val_703_);
v___x_794_ = lean_box(0);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v___x_794_);
v___x_796_ = v___x_671_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v___x_794_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
else
{
lean_object* v_val_798_; lean_object* v___x_799_; lean_object* v___x_800_; uint8_t v___x_801_; 
v_val_798_ = lean_ctor_get(v___x_793_, 0);
lean_inc(v_val_798_);
lean_dec_ref_known(v___x_793_, 1);
v___x_799_ = l_Lean_Syntax_getArg(v___x_774_, v___y_694_);
v___x_800_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__16));
lean_inc(v___x_799_);
v___x_801_ = l_Lean_Syntax_isOfKind(v___x_799_, v___x_800_);
if (v___x_801_ == 0)
{
lean_object* v___x_802_; lean_object* v___x_804_; 
lean_dec(v___x_799_);
lean_dec(v_val_798_);
lean_dec(v___x_774_);
lean_dec(v___x_732_);
lean_dec(v_val_703_);
v___x_802_ = lean_box(0);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v___x_802_);
v___x_804_ = v___x_671_;
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
v___x_806_ = l_Lean_Syntax_getArg(v___x_799_, v___x_686_);
v___x_807_ = l_Lean_Syntax_matchesNull(v___x_806_, v___x_686_);
if (v___x_807_ == 0)
{
lean_object* v___x_808_; lean_object* v___x_810_; 
lean_dec(v___x_799_);
lean_dec(v_val_798_);
lean_dec(v___x_774_);
lean_dec(v___x_732_);
lean_dec(v_val_703_);
v___x_808_ = lean_box(0);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v___x_808_);
v___x_810_ = v___x_671_;
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
v___x_812_ = l_Lean_Syntax_getArg(v___x_799_, v___y_694_);
lean_dec(v___x_799_);
v___x_813_ = l_Lean_Syntax_matchesNull(v___x_812_, v___x_686_);
if (v___x_813_ == 0)
{
lean_object* v___x_814_; lean_object* v___x_816_; 
lean_dec(v_val_798_);
lean_dec(v___x_774_);
lean_dec(v___x_732_);
lean_dec(v_val_703_);
v___x_814_ = lean_box(0);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v___x_814_);
v___x_816_ = v___x_671_;
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
v___x_818_ = l_Lean_Syntax_getArg(v___x_774_, v___x_739_);
lean_dec(v___x_774_);
v___x_819_ = l_Lean_Syntax_matchesNull(v___x_818_, v___x_686_);
if (v___x_819_ == 0)
{
lean_object* v___x_820_; lean_object* v___x_822_; 
lean_dec(v_val_798_);
lean_dec(v___x_732_);
lean_dec(v_val_703_);
v___x_820_ = lean_box(0);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v___x_820_);
v___x_822_ = v___x_671_;
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
v___x_824_ = l_Lean_Syntax_getArg(v___x_732_, v___x_711_);
lean_dec(v___x_732_);
v___x_825_ = l_Lean_Syntax_matchesNull(v___x_824_, v___x_686_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; lean_object* v___x_828_; 
lean_dec(v_val_798_);
lean_dec(v_val_703_);
v___x_826_ = lean_box(0);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v___x_826_);
v___x_828_ = v___x_671_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_826_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
else
{
lean_object* v___x_830_; uint8_t v___x_831_; 
lean_del_object(v___x_671_);
v___x_830_ = lean_array_get_size(v_val_703_);
v___x_831_ = lean_nat_dec_lt(v___x_686_, v___x_830_);
if (v___x_831_ == 0)
{
lean_dec(v_val_798_);
lean_dec(v_val_703_);
goto v___jp_665_;
}
else
{
if (v___x_831_ == 0)
{
lean_dec(v_val_798_);
lean_dec(v_val_703_);
goto v___jp_665_;
}
else
{
size_t v___x_832_; uint8_t v___x_833_; 
v___x_832_ = lean_usize_of_nat(v___x_830_);
v___x_833_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3(v___x_689_, v_val_703_, v___x_697_, v___x_832_);
lean_dec(v_val_703_);
if (v___x_833_ == 0)
{
lean_dec(v_val_798_);
goto v___jp_665_;
}
else
{
lean_object* v___x_834_; size_t v_sz_835_; lean_object* v___x_836_; 
v___x_834_ = lean_box(0);
v_sz_835_ = lean_array_size(v_val_798_);
v___x_836_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5(v_val_798_, v_sz_835_, v___x_697_, v___x_834_, v___y_692_, v___y_693_);
lean_dec(v_val_798_);
if (lean_obj_tag(v___x_836_) == 0)
{
lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_843_; 
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_843_ == 0)
{
lean_object* v_unused_844_; 
v_unused_844_ = lean_ctor_get(v___x_836_, 0);
lean_dec(v_unused_844_);
v___x_838_ = v___x_836_;
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
else
{
lean_dec(v___x_836_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_841_; 
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 0, v___x_834_);
v___x_841_ = v___x_838_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_834_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
else
{
return v___x_836_;
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
v___jp_845_:
{
lean_object* v___x_848_; lean_object* v___x_849_; uint8_t v___x_850_; 
v___x_848_ = lean_unsigned_to_nat(1u);
v___x_849_ = l_Lean_Syntax_getArg(v___x_687_, v___x_848_);
lean_inc(v___x_849_);
v___x_850_ = l_Lean_Syntax_matchesNull(v___x_849_, v___x_848_);
if (v___x_850_ == 0)
{
lean_object* v___x_851_; lean_object* v___x_852_; 
lean_dec(v___x_849_);
lean_dec(v___x_687_);
lean_del_object(v___x_671_);
lean_dec(v_cmdStx_661_);
v___x_851_ = lean_box(0);
v___x_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_852_, 0, v___x_851_);
return v___x_852_;
}
else
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; uint8_t v___x_856_; 
v___x_853_ = l_Lean_Syntax_getArg(v___x_849_, v___x_686_);
lean_dec(v___x_849_);
v___x_854_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__1));
v___x_855_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__18));
lean_inc(v___x_853_);
v___x_856_ = l_Lean_Syntax_isOfKind(v___x_853_, v___x_855_);
if (v___x_856_ == 0)
{
lean_object* v___x_857_; lean_object* v___x_858_; 
lean_dec(v___x_853_);
lean_dec(v___x_687_);
lean_del_object(v___x_671_);
lean_dec(v_cmdStx_661_);
v___x_857_ = lean_box(0);
v___x_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
return v___x_858_;
}
else
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; uint8_t v___x_863_; 
v___x_859_ = l_Lean_Syntax_getArg(v___x_853_, v___x_848_);
lean_dec(v___x_853_);
v___x_860_ = l_Lean_Syntax_getArgs(v___x_859_);
lean_dec(v___x_859_);
v___x_861_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__19));
v___x_862_ = lean_array_get_size(v___x_860_);
v___x_863_ = lean_nat_dec_lt(v___x_686_, v___x_862_);
if (v___x_863_ == 0)
{
lean_dec_ref(v___x_860_);
v___y_691_ = v___x_854_;
v___y_692_ = v___y_846_;
v___y_693_ = v___y_847_;
v___y_694_ = v___x_848_;
v___y_695_ = v___x_861_;
goto v___jp_690_;
}
else
{
lean_object* v___x_864_; lean_object* v___x_865_; uint8_t v___x_866_; 
v___x_864_ = lean_box(v___x_856_);
v___x_865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
lean_ctor_set(v___x_865_, 1, v___x_861_);
v___x_866_ = lean_nat_dec_le(v___x_862_, v___x_862_);
if (v___x_866_ == 0)
{
if (v___x_863_ == 0)
{
lean_dec_ref_known(v___x_865_, 2);
lean_dec_ref(v___x_860_);
v___y_691_ = v___x_854_;
v___y_692_ = v___y_846_;
v___y_693_ = v___y_847_;
v___y_694_ = v___x_848_;
v___y_695_ = v___x_861_;
goto v___jp_690_;
}
else
{
size_t v___x_867_; size_t v___x_868_; lean_object* v___x_869_; lean_object* v_snd_870_; 
v___x_867_ = ((size_t)0ULL);
v___x_868_ = lean_usize_of_nat(v___x_862_);
v___x_869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__6(v___x_856_, v___x_860_, v___x_867_, v___x_868_, v___x_865_);
lean_dec_ref(v___x_860_);
v_snd_870_ = lean_ctor_get(v___x_869_, 1);
lean_inc(v_snd_870_);
lean_dec_ref(v___x_869_);
v___y_691_ = v___x_854_;
v___y_692_ = v___y_846_;
v___y_693_ = v___y_847_;
v___y_694_ = v___x_848_;
v___y_695_ = v_snd_870_;
goto v___jp_690_;
}
}
else
{
size_t v___x_871_; size_t v___x_872_; lean_object* v___x_873_; lean_object* v_snd_874_; 
v___x_871_ = ((size_t)0ULL);
v___x_872_ = lean_usize_of_nat(v___x_862_);
v___x_873_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__6(v___x_856_, v___x_860_, v___x_871_, v___x_872_, v___x_865_);
lean_dec_ref(v___x_860_);
v_snd_874_ = lean_ctor_get(v___x_873_, 1);
lean_inc(v_snd_874_);
lean_dec_ref(v___x_873_);
v___y_691_ = v___x_854_;
v___y_692_ = v___y_846_;
v___y_693_ = v___y_847_;
v___y_694_ = v___x_848_;
v___y_695_ = v_snd_874_;
goto v___jp_690_;
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
LEAN_EXPORT lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___boxed(lean_object* v_cmdStx_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0(v_cmdStx_889_, v___y_890_, v___y_891_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0(lean_object* v_o_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0___redArg(v_o_903_, v___y_905_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0___boxed(lean_object* v_o_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0(v_o_908_, v___y_909_, v___y_910_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9(lean_object* v_msgData_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
lean_object* v___x_917_; 
v___x_917_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg(v_msgData_913_, v___y_915_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___boxed(lean_object* v_msgData_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9(v_msgData_918_, v___y_919_, v___y_920_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1774244096____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_924_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns));
v___x_925_ = l_Lean_Elab_Command_addLinter(v___x_924_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1774244096____hygCtx___hyg_2____boxed(lean_object* v_a_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1774244096____hygCtx___hyg_2_();
return v_res_927_;
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
res = l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_();
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
