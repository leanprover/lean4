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
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Linter_linterSetsExt;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0___boxed(lean_object*, lean_object*);
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
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v_env_70_; lean_object* v___x_71_; lean_object* v_toEnvExtension_72_; lean_object* v_asyncMode_73_; lean_object* v___x_74_; uint8_t v___x_75_; lean_object* v___x_76_; lean_object* v_merged_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_85_; 
v___x_68_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_69_ = lean_st_ref_get(v___y_66_);
v_env_70_ = lean_ctor_get(v___x_69_, 0);
lean_inc_ref(v_env_70_);
lean_dec(v___x_69_);
v___x_71_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_72_ = lean_ctor_get(v___x_71_, 0);
v_asyncMode_73_ = lean_ctor_get(v_toEnvExtension_72_, 2);
v___x_74_ = lean_box(0);
v___x_75_ = 0;
v___x_76_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_68_, v___x_71_, v_env_70_, v_asyncMode_73_, v___x_74_, v___x_75_);
v_merged_77_ = lean_ctor_get(v___x_76_, 0);
v_isSharedCheck_85_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_85_ == 0)
{
lean_object* v_unused_86_; 
v_unused_86_ = lean_ctor_get(v___x_76_, 1);
lean_dec(v_unused_86_);
v___x_79_ = v___x_76_;
v_isShared_80_ = v_isSharedCheck_85_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_merged_77_);
lean_dec(v___x_76_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_85_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_82_; 
if (v_isShared_80_ == 0)
{
lean_ctor_set(v___x_79_, 1, v_merged_77_);
lean_ctor_set(v___x_79_, 0, v_o_65_);
v___x_82_ = v___x_79_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v_o_65_);
lean_ctor_set(v_reuseFailAlloc_84_, 1, v_merged_77_);
v___x_82_ = v_reuseFailAlloc_84_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
lean_object* v___x_83_; 
v___x_83_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
return v___x_83_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0___redArg___boxed(lean_object* v_o_87_, lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0___redArg(v_o_87_, v___y_88_);
lean_dec(v___y_88_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0(lean_object* v___y_91_, lean_object* v___y_92_){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v_scopes_96_; lean_object* v___x_97_; lean_object* v_opts_98_; lean_object* v___x_99_; 
v___x_94_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_95_ = lean_st_ref_get(v___y_92_);
v_scopes_96_ = lean_ctor_get(v___x_95_, 2);
lean_inc(v_scopes_96_);
lean_dec(v___x_95_);
v___x_97_ = l_List_head_x21___redArg(v___x_94_, v_scopes_96_);
lean_dec(v_scopes_96_);
v_opts_98_ = lean_ctor_get(v___x_97_, 1);
lean_inc_ref(v_opts_98_);
lean_dec(v___x_97_);
v___x_99_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0___redArg(v_opts_98_, v___y_92_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0___boxed(lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0(v___y_100_, v___y_101_);
lean_dec(v___y_101_);
lean_dec_ref(v___y_100_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1(size_t v_sz_118_, size_t v_i_119_, lean_object* v_bs_120_){
_start:
{
uint8_t v___x_121_; 
v___x_121_ = lean_usize_dec_lt(v_i_119_, v_sz_118_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; 
v___x_122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_122_, 0, v_bs_120_);
return v___x_122_;
}
else
{
lean_object* v_v_123_; lean_object* v___x_124_; uint8_t v___x_125_; 
v_v_123_ = lean_array_uget(v_bs_120_, v_i_119_);
v___x_124_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__3));
lean_inc(v_v_123_);
v___x_125_ = l_Lean_Syntax_isOfKind(v_v_123_, v___x_124_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; 
lean_dec(v_v_123_);
lean_dec_ref(v_bs_120_);
v___x_126_ = lean_box(0);
return v___x_126_;
}
else
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; uint8_t v___x_130_; 
v___x_127_ = lean_unsigned_to_nat(0u);
v___x_128_ = l_Lean_Syntax_getArg(v_v_123_, v___x_127_);
v___x_129_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__5));
lean_inc(v___x_128_);
v___x_130_ = l_Lean_Syntax_isOfKind(v___x_128_, v___x_129_);
if (v___x_130_ == 0)
{
lean_object* v___x_131_; 
lean_dec(v___x_128_);
lean_dec(v_v_123_);
lean_dec_ref(v_bs_120_);
v___x_131_ = lean_box(0);
return v___x_131_;
}
else
{
lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_132_ = l_Lean_Syntax_getArg(v___x_128_, v___x_127_);
lean_dec(v___x_128_);
v___x_133_ = l_Lean_Syntax_matchesNull(v___x_132_, v___x_127_);
if (v___x_133_ == 0)
{
lean_object* v___x_134_; 
lean_dec(v_v_123_);
lean_dec_ref(v_bs_120_);
v___x_134_ = lean_box(0);
return v___x_134_;
}
else
{
lean_object* v___x_135_; lean_object* v_bs_x27_136_; lean_object* v___x_137_; size_t v___x_138_; size_t v___x_139_; lean_object* v___x_140_; 
v___x_135_ = lean_unsigned_to_nat(1u);
v_bs_x27_136_ = lean_array_uset(v_bs_120_, v_i_119_, v___x_127_);
v___x_137_ = l_Lean_Syntax_getArg(v_v_123_, v___x_135_);
lean_dec(v_v_123_);
v___x_138_ = ((size_t)1ULL);
v___x_139_ = lean_usize_add(v_i_119_, v___x_138_);
v___x_140_ = lean_array_uset(v_bs_x27_136_, v_i_119_, v___x_137_);
v_i_119_ = v___x_139_;
v_bs_120_ = v___x_140_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___boxed(lean_object* v_sz_142_, lean_object* v_i_143_, lean_object* v_bs_144_){
_start:
{
size_t v_sz_boxed_145_; size_t v_i_boxed_146_; lean_object* v_res_147_; 
v_sz_boxed_145_ = lean_unbox_usize(v_sz_142_);
lean_dec(v_sz_142_);
v_i_boxed_146_ = lean_unbox_usize(v_i_143_);
lean_dec(v_i_143_);
v_res_147_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1(v_sz_boxed_145_, v_i_boxed_146_, v_bs_144_);
return v_res_147_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__10(lean_object* v_opts_148_, lean_object* v_opt_149_){
_start:
{
lean_object* v_name_150_; lean_object* v_defValue_151_; lean_object* v_map_152_; lean_object* v___x_153_; 
v_name_150_ = lean_ctor_get(v_opt_149_, 0);
v_defValue_151_ = lean_ctor_get(v_opt_149_, 1);
v_map_152_ = lean_ctor_get(v_opts_148_, 0);
v___x_153_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_152_, v_name_150_);
if (lean_obj_tag(v___x_153_) == 0)
{
uint8_t v___x_154_; 
v___x_154_ = lean_unbox(v_defValue_151_);
return v___x_154_;
}
else
{
lean_object* v_val_155_; 
v_val_155_ = lean_ctor_get(v___x_153_, 0);
lean_inc(v_val_155_);
lean_dec_ref_known(v___x_153_, 1);
if (lean_obj_tag(v_val_155_) == 1)
{
uint8_t v_v_156_; 
v_v_156_ = lean_ctor_get_uint8(v_val_155_, 0);
lean_dec_ref_known(v_val_155_, 0);
return v_v_156_;
}
else
{
uint8_t v___x_157_; 
lean_dec(v_val_155_);
v___x_157_ = lean_unbox(v_defValue_151_);
return v___x_157_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__10___boxed(lean_object* v_opts_158_, lean_object* v_opt_159_){
_start:
{
uint8_t v_res_160_; lean_object* v_r_161_; 
v_res_160_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__10(v_opts_158_, v_opt_159_);
lean_dec_ref(v_opt_159_);
lean_dec_ref(v_opts_158_);
v_r_161_ = lean_box(v_res_160_);
return v_r_161_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_162_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__0);
v___x_164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
return v___x_164_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_165_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1);
v___x_166_ = lean_unsigned_to_nat(0u);
v___x_167_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
lean_ctor_set(v___x_167_, 1, v___x_166_);
lean_ctor_set(v___x_167_, 2, v___x_166_);
lean_ctor_set(v___x_167_, 3, v___x_166_);
lean_ctor_set(v___x_167_, 4, v___x_165_);
lean_ctor_set(v___x_167_, 5, v___x_165_);
lean_ctor_set(v___x_167_, 6, v___x_165_);
lean_ctor_set(v___x_167_, 7, v___x_165_);
lean_ctor_set(v___x_167_, 8, v___x_165_);
lean_ctor_set(v___x_167_, 9, v___x_165_);
lean_ctor_set(v___x_167_, 10, v___x_165_);
return v___x_167_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_168_ = lean_unsigned_to_nat(32u);
v___x_169_ = lean_mk_empty_array_with_capacity(v___x_168_);
v___x_170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
return v___x_170_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__4(void){
_start:
{
size_t v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_171_ = ((size_t)5ULL);
v___x_172_ = lean_unsigned_to_nat(0u);
v___x_173_ = lean_unsigned_to_nat(32u);
v___x_174_ = lean_mk_empty_array_with_capacity(v___x_173_);
v___x_175_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__3);
v___x_176_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_176_, 0, v___x_175_);
lean_ctor_set(v___x_176_, 1, v___x_174_);
lean_ctor_set(v___x_176_, 2, v___x_172_);
lean_ctor_set(v___x_176_, 3, v___x_172_);
lean_ctor_set_usize(v___x_176_, 4, v___x_171_);
return v___x_176_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_177_ = lean_box(1);
v___x_178_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__4);
v___x_179_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1);
v___x_180_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
lean_ctor_set(v___x_180_, 1, v___x_178_);
lean_ctor_set(v___x_180_, 2, v___x_177_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg(lean_object* v_msgData_181_, lean_object* v___y_182_){
_start:
{
lean_object* v___x_184_; lean_object* v_env_185_; uint8_t v___x_186_; lean_object* v_env_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v_scopes_190_; lean_object* v___x_191_; lean_object* v_opts_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_184_ = lean_st_ref_get(v___y_182_);
v_env_185_ = lean_ctor_get(v___x_184_, 0);
lean_inc_ref(v_env_185_);
lean_dec(v___x_184_);
v___x_186_ = 0;
v_env_187_ = l_Lean_Environment_setRecordingDeps(v_env_185_, v___x_186_);
v___x_188_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_189_ = lean_st_ref_get(v___y_182_);
v_scopes_190_ = lean_ctor_get(v___x_189_, 2);
lean_inc(v_scopes_190_);
lean_dec(v___x_189_);
v___x_191_ = l_List_head_x21___redArg(v___x_188_, v_scopes_190_);
lean_dec(v_scopes_190_);
v_opts_192_ = lean_ctor_get(v___x_191_, 1);
lean_inc_ref(v_opts_192_);
lean_dec(v___x_191_);
v___x_193_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__2);
v___x_194_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__5);
v___x_195_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_195_, 0, v_env_187_);
lean_ctor_set(v___x_195_, 1, v___x_193_);
lean_ctor_set(v___x_195_, 2, v___x_194_);
lean_ctor_set(v___x_195_, 3, v_opts_192_);
v___x_196_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
lean_ctor_set(v___x_196_, 1, v_msgData_181_);
v___x_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_197_, 0, v___x_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___boxed(lean_object* v_msgData_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg(v_msgData_198_, v___y_199_);
lean_dec(v___y_199_);
return v_res_201_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0(uint8_t v_suppressElabErrors_203_, lean_object* v_x_204_){
_start:
{
if (lean_obj_tag(v_x_204_) == 1)
{
lean_object* v_pre_205_; 
v_pre_205_ = lean_ctor_get(v_x_204_, 0);
if (lean_obj_tag(v_pre_205_) == 0)
{
lean_object* v_str_206_; lean_object* v___x_207_; uint8_t v___x_208_; 
v_str_206_ = lean_ctor_get(v_x_204_, 1);
v___x_207_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0___closed__0));
v___x_208_ = lean_string_dec_eq(v_str_206_, v___x_207_);
if (v___x_208_ == 0)
{
return v___x_208_;
}
else
{
return v_suppressElabErrors_203_;
}
}
else
{
uint8_t v___x_209_; 
v___x_209_ = 0;
return v___x_209_;
}
}
else
{
uint8_t v___x_210_; 
v___x_210_ = 0;
return v___x_210_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0___boxed(lean_object* v_suppressElabErrors_211_, lean_object* v_x_212_){
_start:
{
uint8_t v_suppressElabErrors_boxed_213_; uint8_t v_res_214_; lean_object* v_r_215_; 
v_suppressElabErrors_boxed_213_ = lean_unbox(v_suppressElabErrors_211_);
v_res_214_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0(v_suppressElabErrors_boxed_213_, v_x_212_);
lean_dec(v_x_212_);
v_r_215_ = lean_box(v_res_214_);
return v_r_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6(lean_object* v_ref_217_, lean_object* v_msgData_218_, uint8_t v_severity_219_, uint8_t v_isSilent_220_, lean_object* v___y_221_, lean_object* v___y_222_){
_start:
{
uint8_t v___y_225_; lean_object* v___y_226_; lean_object* v___y_227_; lean_object* v___y_228_; lean_object* v___y_229_; lean_object* v___y_230_; uint8_t v___y_231_; lean_object* v___y_232_; uint8_t v___y_290_; lean_object* v___y_291_; uint8_t v___y_292_; lean_object* v___y_293_; lean_object* v___y_316_; uint8_t v___y_317_; uint8_t v___y_318_; lean_object* v___y_319_; uint8_t v___y_323_; uint8_t v___y_324_; uint8_t v___x_339_; uint8_t v___y_341_; uint8_t v___x_351_; 
v___x_339_ = 2;
v___x_351_ = l_Lean_instBEqMessageSeverity_beq(v_severity_219_, v___x_339_);
if (v___x_351_ == 0)
{
v___y_341_ = v___x_351_;
goto v___jp_340_;
}
else
{
uint8_t v___x_352_; 
lean_inc_ref(v_msgData_218_);
v___x_352_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_218_);
if (v___x_352_ == 0)
{
v___y_341_ = v___x_352_;
goto v___jp_340_;
}
else
{
lean_object* v___x_353_; lean_object* v___x_354_; 
lean_dec_ref(v_msgData_218_);
v___x_353_ = lean_box(0);
v___x_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
return v___x_354_;
}
}
v___jp_224_:
{
lean_object* v___x_233_; 
v___x_233_ = l_Lean_Elab_Command_getScope___redArg(v___y_232_);
if (lean_obj_tag(v___x_233_) == 0)
{
lean_object* v_a_234_; lean_object* v_currNamespace_235_; lean_object* v___x_236_; 
v_a_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc(v_a_234_);
lean_dec_ref_known(v___x_233_, 1);
v_currNamespace_235_ = lean_ctor_get(v_a_234_, 2);
lean_inc(v_currNamespace_235_);
lean_dec(v_a_234_);
v___x_236_ = l_Lean_Elab_Command_getScope___redArg(v___y_232_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_object* v_a_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_272_; 
v_a_237_ = lean_ctor_get(v___x_236_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_272_ == 0)
{
v___x_239_ = v___x_236_;
v_isShared_240_ = v_isSharedCheck_272_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_a_237_);
lean_dec(v___x_236_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_272_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v_openDecls_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v_env_246_; lean_object* v_messages_247_; lean_object* v_scopes_248_; lean_object* v_usedQuotCtxts_249_; lean_object* v_nextMacroScope_250_; lean_object* v_maxRecDepth_251_; lean_object* v_ngen_252_; lean_object* v_auxDeclNGen_253_; lean_object* v_infoState_254_; lean_object* v_traceState_255_; lean_object* v_snapshotTasks_256_; lean_object* v_prevLinterStates_257_; lean_object* v_codeQualityEntryTasks_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_271_; 
v_openDecls_241_ = lean_ctor_get(v_a_237_, 3);
lean_inc(v_openDecls_241_);
lean_dec(v_a_237_);
v___x_242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_242_, 0, v_currNamespace_235_);
lean_ctor_set(v___x_242_, 1, v_openDecls_241_);
v___x_243_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
lean_ctor_set(v___x_243_, 1, v___y_226_);
lean_inc_ref(v___y_229_);
lean_inc_ref(v___y_227_);
v___x_244_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_244_, 0, v___y_227_);
lean_ctor_set(v___x_244_, 1, v___y_230_);
lean_ctor_set(v___x_244_, 2, v___y_228_);
lean_ctor_set(v___x_244_, 3, v___y_229_);
lean_ctor_set(v___x_244_, 4, v___x_243_);
lean_ctor_set_uint8(v___x_244_, sizeof(void*)*5, v___y_231_);
lean_ctor_set_uint8(v___x_244_, sizeof(void*)*5 + 1, v___y_225_);
lean_ctor_set_uint8(v___x_244_, sizeof(void*)*5 + 2, v_isSilent_220_);
v___x_245_ = lean_st_ref_take(v___y_232_);
v_env_246_ = lean_ctor_get(v___x_245_, 0);
v_messages_247_ = lean_ctor_get(v___x_245_, 1);
v_scopes_248_ = lean_ctor_get(v___x_245_, 2);
v_usedQuotCtxts_249_ = lean_ctor_get(v___x_245_, 3);
v_nextMacroScope_250_ = lean_ctor_get(v___x_245_, 4);
v_maxRecDepth_251_ = lean_ctor_get(v___x_245_, 5);
v_ngen_252_ = lean_ctor_get(v___x_245_, 6);
v_auxDeclNGen_253_ = lean_ctor_get(v___x_245_, 7);
v_infoState_254_ = lean_ctor_get(v___x_245_, 8);
v_traceState_255_ = lean_ctor_get(v___x_245_, 9);
v_snapshotTasks_256_ = lean_ctor_get(v___x_245_, 10);
v_prevLinterStates_257_ = lean_ctor_get(v___x_245_, 11);
v_codeQualityEntryTasks_258_ = lean_ctor_get(v___x_245_, 12);
v_isSharedCheck_271_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_271_ == 0)
{
v___x_260_ = v___x_245_;
v_isShared_261_ = v_isSharedCheck_271_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_codeQualityEntryTasks_258_);
lean_inc(v_prevLinterStates_257_);
lean_inc(v_snapshotTasks_256_);
lean_inc(v_traceState_255_);
lean_inc(v_infoState_254_);
lean_inc(v_auxDeclNGen_253_);
lean_inc(v_ngen_252_);
lean_inc(v_maxRecDepth_251_);
lean_inc(v_nextMacroScope_250_);
lean_inc(v_usedQuotCtxts_249_);
lean_inc(v_scopes_248_);
lean_inc(v_messages_247_);
lean_inc(v_env_246_);
lean_dec(v___x_245_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_271_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_265_; 
v___x_262_ = lean_box(0);
v___x_263_ = l_Lean_MessageLog_add(v___x_244_, v_messages_247_);
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 1, v___x_263_);
v___x_265_ = v___x_260_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_env_246_);
lean_ctor_set(v_reuseFailAlloc_270_, 1, v___x_263_);
lean_ctor_set(v_reuseFailAlloc_270_, 2, v_scopes_248_);
lean_ctor_set(v_reuseFailAlloc_270_, 3, v_usedQuotCtxts_249_);
lean_ctor_set(v_reuseFailAlloc_270_, 4, v_nextMacroScope_250_);
lean_ctor_set(v_reuseFailAlloc_270_, 5, v_maxRecDepth_251_);
lean_ctor_set(v_reuseFailAlloc_270_, 6, v_ngen_252_);
lean_ctor_set(v_reuseFailAlloc_270_, 7, v_auxDeclNGen_253_);
lean_ctor_set(v_reuseFailAlloc_270_, 8, v_infoState_254_);
lean_ctor_set(v_reuseFailAlloc_270_, 9, v_traceState_255_);
lean_ctor_set(v_reuseFailAlloc_270_, 10, v_snapshotTasks_256_);
lean_ctor_set(v_reuseFailAlloc_270_, 11, v_prevLinterStates_257_);
lean_ctor_set(v_reuseFailAlloc_270_, 12, v_codeQualityEntryTasks_258_);
v___x_265_ = v_reuseFailAlloc_270_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
lean_object* v___x_266_; lean_object* v___x_268_; 
v___x_266_ = lean_st_ref_put(v___y_232_, v___x_265_);
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 0, v___x_262_);
v___x_268_ = v___x_239_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v___x_262_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
}
else
{
lean_object* v_a_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_280_; 
lean_dec(v_currNamespace_235_);
lean_dec_ref(v___y_230_);
lean_dec(v___y_228_);
lean_dec_ref(v___y_226_);
v_a_273_ = lean_ctor_get(v___x_236_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_280_ == 0)
{
v___x_275_ = v___x_236_;
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_a_273_);
lean_dec(v___x_236_);
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
else
{
lean_object* v_a_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_288_; 
lean_dec_ref(v___y_230_);
lean_dec(v___y_228_);
lean_dec_ref(v___y_226_);
v_a_281_ = lean_ctor_get(v___x_233_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_288_ == 0)
{
v___x_283_ = v___x_233_;
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v___x_233_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_286_; 
if (v_isShared_284_ == 0)
{
v___x_286_ = v___x_283_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_a_281_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
}
v___jp_289_:
{
lean_object* v_fileName_294_; lean_object* v_fileMap_295_; uint8_t v_suppressElabErrors_296_; lean_object* v___x_297_; lean_object* v___f_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v_a_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_314_; 
v_fileName_294_ = lean_ctor_get(v___y_221_, 0);
v_fileMap_295_ = lean_ctor_get(v___y_221_, 1);
v_suppressElabErrors_296_ = lean_ctor_get_uint8(v___y_221_, sizeof(void*)*10);
v___x_297_ = lean_box(v_suppressElabErrors_296_);
v___f_298_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0___boxed), 2, 1);
lean_closure_set(v___f_298_, 0, v___x_297_);
v___x_299_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_218_);
v___x_300_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg(v___x_299_, v___y_222_);
v_a_301_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_314_ == 0)
{
v___x_303_ = v___x_300_;
v_isShared_304_ = v_isSharedCheck_314_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_a_301_);
lean_dec(v___x_300_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_314_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
lean_inc_ref_n(v_fileMap_295_, 2);
v___x_305_ = l_Lean_FileMap_toPosition(v_fileMap_295_, v___y_291_);
lean_dec(v___y_291_);
v___x_306_ = l_Lean_FileMap_toPosition(v_fileMap_295_, v___y_293_);
lean_dec(v___y_293_);
v___x_307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
v___x_308_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___closed__0));
if (v_suppressElabErrors_296_ == 0)
{
lean_del_object(v___x_303_);
lean_dec_ref(v___f_298_);
v___y_225_ = v___y_290_;
v___y_226_ = v_a_301_;
v___y_227_ = v_fileName_294_;
v___y_228_ = v___x_307_;
v___y_229_ = v___x_308_;
v___y_230_ = v___x_305_;
v___y_231_ = v___y_292_;
v___y_232_ = v___y_222_;
goto v___jp_224_;
}
else
{
uint8_t v___x_309_; 
lean_inc(v_a_301_);
v___x_309_ = l_Lean_MessageData_hasTag(v___f_298_, v_a_301_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; lean_object* v___x_312_; 
lean_dec_ref_known(v___x_307_, 1);
lean_dec_ref(v___x_305_);
lean_dec(v_a_301_);
v___x_310_ = lean_box(0);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 0, v___x_310_);
v___x_312_ = v___x_303_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_310_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
else
{
lean_del_object(v___x_303_);
v___y_225_ = v___y_290_;
v___y_226_ = v_a_301_;
v___y_227_ = v_fileName_294_;
v___y_228_ = v___x_307_;
v___y_229_ = v___x_308_;
v___y_230_ = v___x_305_;
v___y_231_ = v___y_292_;
v___y_232_ = v___y_222_;
goto v___jp_224_;
}
}
}
}
v___jp_315_:
{
lean_object* v___x_320_; 
v___x_320_ = l_Lean_Syntax_getTailPos_x3f(v___y_316_, v___y_318_);
lean_dec(v___y_316_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_inc(v___y_319_);
v___y_290_ = v___y_317_;
v___y_291_ = v___y_319_;
v___y_292_ = v___y_318_;
v___y_293_ = v___y_319_;
goto v___jp_289_;
}
else
{
lean_object* v_val_321_; 
v_val_321_ = lean_ctor_get(v___x_320_, 0);
lean_inc(v_val_321_);
lean_dec_ref_known(v___x_320_, 1);
v___y_290_ = v___y_317_;
v___y_291_ = v___y_319_;
v___y_292_ = v___y_318_;
v___y_293_ = v_val_321_;
goto v___jp_289_;
}
}
v___jp_322_:
{
lean_object* v___x_325_; 
v___x_325_ = l_Lean_Elab_Command_getRef___redArg(v___y_221_);
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v_a_326_; lean_object* v_ref_327_; lean_object* v___x_328_; 
v_a_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_a_326_);
lean_dec_ref_known(v___x_325_, 1);
v_ref_327_ = l_Lean_replaceRef(v_ref_217_, v_a_326_);
lean_dec(v_a_326_);
v___x_328_ = l_Lean_Syntax_getPos_x3f(v_ref_327_, v___y_323_);
if (lean_obj_tag(v___x_328_) == 0)
{
lean_object* v___x_329_; 
v___x_329_ = lean_unsigned_to_nat(0u);
v___y_316_ = v_ref_327_;
v___y_317_ = v___y_324_;
v___y_318_ = v___y_323_;
v___y_319_ = v___x_329_;
goto v___jp_315_;
}
else
{
lean_object* v_val_330_; 
v_val_330_ = lean_ctor_get(v___x_328_, 0);
lean_inc(v_val_330_);
lean_dec_ref_known(v___x_328_, 1);
v___y_316_ = v_ref_327_;
v___y_317_ = v___y_324_;
v___y_318_ = v___y_323_;
v___y_319_ = v_val_330_;
goto v___jp_315_;
}
}
else
{
lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_338_; 
lean_dec_ref(v_msgData_218_);
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
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v_scopes_344_; lean_object* v___x_345_; lean_object* v_opts_346_; uint8_t v___x_347_; uint8_t v___x_348_; 
v___x_342_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_343_ = lean_st_ref_get(v___y_222_);
v_scopes_344_ = lean_ctor_get(v___x_343_, 2);
lean_inc(v_scopes_344_);
lean_dec(v___x_343_);
v___x_345_ = l_List_head_x21___redArg(v___x_342_, v_scopes_344_);
lean_dec(v_scopes_344_);
v_opts_346_ = lean_ctor_get(v___x_345_, 1);
lean_inc_ref(v_opts_346_);
lean_dec(v___x_345_);
v___x_347_ = 1;
v___x_348_ = l_Lean_instBEqMessageSeverity_beq(v_severity_219_, v___x_347_);
if (v___x_348_ == 0)
{
lean_dec_ref(v_opts_346_);
v___y_323_ = v___y_341_;
v___y_324_ = v_severity_219_;
goto v___jp_322_;
}
else
{
lean_object* v___x_349_; uint8_t v___x_350_; 
v___x_349_ = l_Lean_warningAsError;
v___x_350_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__10(v_opts_346_, v___x_349_);
lean_dec_ref(v_opts_346_);
if (v___x_350_ == 0)
{
v___y_323_ = v___y_341_;
v___y_324_ = v_severity_219_;
goto v___jp_322_;
}
else
{
v___y_323_ = v___y_341_;
v___y_324_ = v___x_339_;
goto v___jp_322_;
}
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
lean_dec_ref(v___y_359_);
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
lean_object* v_name_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_409_; 
v_name_391_ = lean_ctor_get(v_linterOption_385_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v_linterOption_385_);
if (v_isSharedCheck_409_ == 0)
{
lean_object* v_unused_410_; 
v_unused_410_ = lean_ctor_get(v_linterOption_385_, 1);
lean_dec(v_unused_410_);
v___x_393_ = v_linterOption_385_;
v_isShared_394_ = v_isSharedCheck_409_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_name_391_);
lean_dec(v_linterOption_385_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_409_;
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
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_395_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v___x_396_);
v___x_398_ = v_reuseFailAlloc_408_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v_disable_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_399_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__3);
v___x_400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_400_, 0, v___x_398_);
lean_ctor_set(v___x_400_, 1, v___x_399_);
v_disable_401_ = l_Lean_MessageData_note(v___x_400_);
v___x_402_ = l_Lean_Linter_linterMessageTag;
v___x_403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_403_, 0, v_msg_387_);
lean_ctor_set(v___x_403_, 1, v_disable_401_);
v___x_404_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_402_);
lean_ctor_set(v___x_404_, 1, v___x_403_);
v___x_405_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_405_, 0, v_name_391_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
lean_inc(v_stx_386_);
v___x_406_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_406_, 0, v_stx_386_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
v___x_407_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5(v_stx_386_, v___x_406_, v___y_388_, v___y_389_);
lean_dec(v_stx_386_);
return v___x_407_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___boxed(lean_object* v_linterOption_411_, lean_object* v_stx_412_, lean_object* v_msg_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4(v_linterOption_411_, v_stx_412_, v_msg_413_, v___y_414_, v___y_415_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
return v_res_417_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__2(void){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__1));
v___x_422_ = l_Lean_MessageData_ofFormat(v___x_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5(lean_object* v_as_438_, size_t v_sz_439_, size_t v_i_440_, lean_object* v_b_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
lean_object* v_a_446_; uint8_t v___x_450_; 
v___x_450_ = lean_usize_dec_lt(v_i_440_, v_sz_439_);
if (v___x_450_ == 0)
{
lean_object* v___x_451_; 
v___x_451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_451_, 0, v_b_441_);
return v___x_451_;
}
else
{
lean_object* v___x_452_; lean_object* v_patHead_454_; lean_object* v___y_455_; lean_object* v___y_456_; lean_object* v_a_460_; lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_452_ = lean_box(0);
v_a_460_ = lean_array_uget_borrowed(v_as_438_, v_i_440_);
v___x_461_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__4));
lean_inc(v_a_460_);
v___x_462_ = l_Lean_Syntax_isOfKind(v_a_460_, v___x_461_);
if (v___x_462_ == 0)
{
v_a_446_ = v___x_452_;
goto v___jp_445_;
}
else
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; uint8_t v___x_466_; 
v___x_463_ = lean_unsigned_to_nat(1u);
v___x_464_ = l_Lean_Syntax_getArg(v_a_460_, v___x_463_);
v___x_465_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__6));
lean_inc(v___x_464_);
v___x_466_ = l_Lean_Syntax_isOfKind(v___x_464_, v___x_465_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; uint8_t v___x_468_; 
v___x_467_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__8));
lean_inc(v___x_464_);
v___x_468_ = l_Lean_Syntax_isOfKind(v___x_464_, v___x_467_);
if (v___x_468_ == 0)
{
lean_dec(v___x_464_);
v_a_446_ = v___x_452_;
goto v___jp_445_;
}
else
{
v_patHead_454_ = v___x_464_;
v___y_455_ = v___y_442_;
v___y_456_ = v___y_443_;
goto v___jp_453_;
}
}
else
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; uint8_t v___x_472_; 
v___x_469_ = lean_unsigned_to_nat(0u);
v___x_470_ = l_Lean_Syntax_getArg(v___x_464_, v___x_469_);
lean_dec(v___x_464_);
v___x_471_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__8));
lean_inc(v___x_470_);
v___x_472_ = l_Lean_Syntax_isOfKind(v___x_470_, v___x_471_);
if (v___x_472_ == 0)
{
lean_dec(v___x_470_);
v_a_446_ = v___x_452_;
goto v___jp_445_;
}
else
{
v_patHead_454_ = v___x_470_;
v___y_455_ = v___y_442_;
v___y_456_ = v___y_443_;
goto v___jp_453_;
}
}
}
v___jp_453_:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_457_ = l_Lean_Linter_linter_suspiciousUnexpanderPatterns;
v___x_458_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__2);
v___x_459_ = l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4(v___x_457_, v_patHead_454_, v___x_458_, v___y_455_, v___y_456_);
if (lean_obj_tag(v___x_459_) == 0)
{
lean_dec_ref_known(v___x_459_, 1);
v_a_446_ = v___x_452_;
goto v___jp_445_;
}
else
{
return v___x_459_;
}
}
}
v___jp_445_:
{
size_t v___x_447_; size_t v___x_448_; 
v___x_447_ = ((size_t)1ULL);
v___x_448_ = lean_usize_add(v_i_440_, v___x_447_);
v_i_440_ = v___x_448_;
v_b_441_ = v_a_446_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___boxed(lean_object* v_as_473_, lean_object* v_sz_474_, lean_object* v_i_475_, lean_object* v_b_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
size_t v_sz_boxed_480_; size_t v_i_boxed_481_; lean_object* v_res_482_; 
v_sz_boxed_480_ = lean_unbox_usize(v_sz_474_);
lean_dec(v_sz_474_);
v_i_boxed_481_ = lean_unbox_usize(v_i_475_);
lean_dec(v_i_475_);
v_res_482_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5(v_as_473_, v_sz_boxed_480_, v_i_boxed_481_, v_b_476_, v___y_477_, v___y_478_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
lean_dec_ref(v_as_473_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2(size_t v_sz_489_, size_t v_i_490_, lean_object* v_bs_491_){
_start:
{
uint8_t v___x_492_; 
v___x_492_ = lean_usize_dec_lt(v_i_490_, v_sz_489_);
if (v___x_492_ == 0)
{
lean_object* v___x_493_; 
v___x_493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_493_, 0, v_bs_491_);
return v___x_493_;
}
else
{
lean_object* v_v_494_; lean_object* v___x_495_; uint8_t v___x_496_; 
v_v_494_ = lean_array_uget_borrowed(v_bs_491_, v_i_490_);
v___x_495_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__1));
lean_inc(v_v_494_);
v___x_496_ = l_Lean_Syntax_isOfKind(v_v_494_, v___x_495_);
if (v___x_496_ == 0)
{
lean_object* v___x_497_; 
lean_dec_ref(v_bs_491_);
v___x_497_ = lean_box(0);
return v___x_497_;
}
else
{
lean_object* v___x_498_; lean_object* v___x_499_; uint8_t v___x_500_; 
v___x_498_ = lean_unsigned_to_nat(1u);
v___x_499_ = l_Lean_Syntax_getArg(v_v_494_, v___x_498_);
lean_inc(v___x_499_);
v___x_500_ = l_Lean_Syntax_matchesNull(v___x_499_, v___x_498_);
if (v___x_500_ == 0)
{
lean_object* v___x_501_; 
lean_dec(v___x_499_);
lean_dec_ref(v_bs_491_);
v___x_501_ = lean_box(0);
return v___x_501_;
}
else
{
lean_object* v___x_502_; lean_object* v___x_503_; uint8_t v___x_504_; 
v___x_502_ = lean_unsigned_to_nat(0u);
v___x_503_ = l_Lean_Syntax_getArg(v___x_499_, v___x_502_);
lean_dec(v___x_499_);
lean_inc(v___x_503_);
v___x_504_ = l_Lean_Syntax_matchesNull(v___x_503_, v___x_498_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; 
lean_dec(v___x_503_);
lean_dec_ref(v_bs_491_);
v___x_505_ = lean_box(0);
return v___x_505_;
}
else
{
lean_object* v_bs_x27_506_; lean_object* v___x_507_; size_t v___x_508_; size_t v___x_509_; lean_object* v___x_510_; 
v_bs_x27_506_ = lean_array_uset(v_bs_491_, v_i_490_, v___x_502_);
v___x_507_ = l_Lean_Syntax_getArg(v___x_503_, v___x_502_);
lean_dec(v___x_503_);
v___x_508_ = ((size_t)1ULL);
v___x_509_ = lean_usize_add(v_i_490_, v___x_508_);
v___x_510_ = lean_array_uset(v_bs_x27_506_, v_i_490_, v___x_507_);
v_i_490_ = v___x_509_;
v_bs_491_ = v___x_510_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___boxed(lean_object* v_sz_512_, lean_object* v_i_513_, lean_object* v_bs_514_){
_start:
{
size_t v_sz_boxed_515_; size_t v_i_boxed_516_; lean_object* v_res_517_; 
v_sz_boxed_515_ = lean_unbox_usize(v_sz_512_);
lean_dec(v_sz_512_);
v_i_boxed_516_ = lean_unbox_usize(v_i_513_);
lean_dec(v_i_513_);
v_res_517_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2(v_sz_boxed_515_, v_i_boxed_516_, v_bs_514_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__6(uint8_t v___x_518_, lean_object* v_as_519_, size_t v_i_520_, size_t v_stop_521_, lean_object* v_b_522_){
_start:
{
lean_object* v___y_524_; uint8_t v___x_528_; 
v___x_528_ = lean_usize_dec_eq(v_i_520_, v_stop_521_);
if (v___x_528_ == 0)
{
lean_object* v_fst_529_; uint8_t v___x_530_; 
v_fst_529_ = lean_ctor_get(v_b_522_, 0);
v___x_530_ = lean_unbox(v_fst_529_);
if (v___x_530_ == 0)
{
lean_object* v_snd_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_539_; 
v_snd_531_ = lean_ctor_get(v_b_522_, 1);
v_isSharedCheck_539_ = !lean_is_exclusive(v_b_522_);
if (v_isSharedCheck_539_ == 0)
{
lean_object* v_unused_540_; 
v_unused_540_ = lean_ctor_get(v_b_522_, 0);
lean_dec(v_unused_540_);
v___x_533_ = v_b_522_;
v_isShared_534_ = v_isSharedCheck_539_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_snd_531_);
lean_dec(v_b_522_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_539_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_535_; lean_object* v___x_537_; 
v___x_535_ = lean_box(v___x_518_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 0, v___x_535_);
v___x_537_ = v___x_533_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_535_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v_snd_531_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
v___y_524_ = v___x_537_;
goto v___jp_523_;
}
}
}
else
{
lean_object* v_snd_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_551_; 
v_snd_541_ = lean_ctor_get(v_b_522_, 1);
v_isSharedCheck_551_ = !lean_is_exclusive(v_b_522_);
if (v_isSharedCheck_551_ == 0)
{
lean_object* v_unused_552_; 
v_unused_552_ = lean_ctor_get(v_b_522_, 0);
lean_dec(v_unused_552_);
v___x_543_ = v_b_522_;
v_isShared_544_ = v_isSharedCheck_551_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_snd_541_);
lean_dec(v_b_522_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_551_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_549_; 
v___x_545_ = lean_array_uget_borrowed(v_as_519_, v_i_520_);
lean_inc(v___x_545_);
v___x_546_ = lean_array_push(v_snd_541_, v___x_545_);
v___x_547_ = lean_box(v___x_528_);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 1, v___x_546_);
lean_ctor_set(v___x_543_, 0, v___x_547_);
v___x_549_ = v___x_543_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_547_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v___x_546_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
v___y_524_ = v___x_549_;
goto v___jp_523_;
}
}
}
}
else
{
return v_b_522_;
}
v___jp_523_:
{
size_t v___x_525_; size_t v___x_526_; 
v___x_525_ = ((size_t)1ULL);
v___x_526_ = lean_usize_add(v_i_520_, v___x_525_);
v_i_520_ = v___x_526_;
v_b_522_ = v___y_524_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__6___boxed(lean_object* v___x_553_, lean_object* v_as_554_, lean_object* v_i_555_, lean_object* v_stop_556_, lean_object* v_b_557_){
_start:
{
uint8_t v___x_10836__boxed_558_; size_t v_i_boxed_559_; size_t v_stop_boxed_560_; lean_object* v_res_561_; 
v___x_10836__boxed_558_ = lean_unbox(v___x_553_);
v_i_boxed_559_ = lean_unbox_usize(v_i_555_);
lean_dec(v_i_555_);
v_stop_boxed_560_ = lean_unbox_usize(v_stop_556_);
lean_dec(v_stop_556_);
v_res_561_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__6(v___x_10836__boxed_558_, v_as_554_, v_i_boxed_559_, v_stop_boxed_560_, v_b_557_);
lean_dec_ref(v_as_554_);
return v_res_561_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3(uint8_t v___x_572_, lean_object* v_as_573_, size_t v_i_574_, size_t v_stop_575_){
_start:
{
uint8_t v___x_580_; 
v___x_580_ = lean_usize_dec_eq(v_i_574_, v_stop_575_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; lean_object* v___x_582_; uint8_t v___x_583_; 
v___x_581_ = lean_array_uget_borrowed(v_as_573_, v_i_574_);
v___x_582_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__2));
lean_inc(v___x_581_);
v___x_583_ = l_Lean_Syntax_isOfKind(v___x_581_, v___x_582_);
if (v___x_583_ == 0)
{
goto v___jp_576_;
}
else
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; uint8_t v___x_587_; 
v___x_584_ = lean_unsigned_to_nat(0u);
v___x_585_ = l_Lean_Syntax_getArg(v___x_581_, v___x_584_);
v___x_586_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__4));
v___x_587_ = l_Lean_Syntax_matchesIdent(v___x_585_, v___x_586_);
lean_dec(v___x_585_);
if (v___x_587_ == 0)
{
goto v___jp_576_;
}
else
{
lean_object* v___x_588_; lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_588_ = lean_unsigned_to_nat(1u);
v___x_589_ = l_Lean_Syntax_getArg(v___x_581_, v___x_588_);
v___x_590_ = l_Lean_Syntax_matchesNull(v___x_589_, v___x_588_);
if (v___x_590_ == 0)
{
goto v___jp_576_;
}
else
{
if (v___x_572_ == 0)
{
goto v___jp_576_;
}
else
{
return v___x_572_;
}
}
}
}
}
else
{
uint8_t v___x_591_; 
v___x_591_ = 0;
return v___x_591_;
}
v___jp_576_:
{
size_t v___x_577_; size_t v___x_578_; 
v___x_577_ = ((size_t)1ULL);
v___x_578_ = lean_usize_add(v_i_574_, v___x_577_);
v_i_574_ = v___x_578_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___boxed(lean_object* v___x_592_, lean_object* v_as_593_, lean_object* v_i_594_, lean_object* v_stop_595_){
_start:
{
uint8_t v___x_10921__boxed_596_; size_t v_i_boxed_597_; size_t v_stop_boxed_598_; uint8_t v_res_599_; lean_object* v_r_600_; 
v___x_10921__boxed_596_ = lean_unbox(v___x_592_);
v_i_boxed_597_ = lean_unbox_usize(v_i_594_);
lean_dec(v_i_594_);
v_stop_boxed_598_ = lean_unbox_usize(v_stop_595_);
lean_dec(v_stop_595_);
v_res_599_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3(v___x_10921__boxed_596_, v_as_593_, v_i_boxed_597_, v_stop_boxed_598_);
lean_dec_ref(v_as_593_);
v_r_600_ = lean_box(v_res_599_);
return v_r_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0(lean_object* v_cmdStx_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
lean_object* v___x_663_; lean_object* v_a_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_878_; 
v___x_663_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0(v___y_657_, v___y_658_);
v_a_664_ = lean_ctor_get(v___x_663_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_878_ == 0)
{
v___x_666_ = v___x_663_;
v_isShared_667_ = v_isSharedCheck_878_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_a_664_);
lean_dec(v___x_663_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_878_;
goto v_resetjp_665_;
}
v___jp_660_:
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = lean_box(0);
v___x_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_662_, 0, v___x_661_);
return v___x_662_;
}
v_resetjp_665_:
{
uint8_t v___x_668_; 
v___x_668_ = l_Lean_Linter_getLinterSuspiciousUnexpanderPatterns(v_a_664_);
lean_dec(v_a_664_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; lean_object* v___x_671_; 
lean_dec(v_cmdStx_656_);
v___x_669_ = lean_box(0);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 0, v___x_669_);
v___x_671_ = v___x_666_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v___x_669_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
else
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_673_ = ((lean_object*)(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_));
v___x_674_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0));
v___x_675_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__2));
lean_inc(v_cmdStx_656_);
v___x_676_ = l_Lean_Syntax_isOfKind(v_cmdStx_656_, v___x_675_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; lean_object* v___x_679_; 
lean_dec(v_cmdStx_656_);
v___x_677_ = lean_box(0);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 0, v___x_677_);
v___x_679_ = v___x_666_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_677_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
else
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; uint8_t v___x_684_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_841_; lean_object* v___y_842_; 
v___x_681_ = lean_unsigned_to_nat(0u);
v___x_682_ = l_Lean_Syntax_getArg(v_cmdStx_656_, v___x_681_);
v___x_683_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__4));
lean_inc(v___x_682_);
v___x_684_ = l_Lean_Syntax_isOfKind(v___x_682_, v___x_683_);
if (v___x_684_ == 0)
{
lean_object* v___x_865_; lean_object* v___x_866_; 
lean_dec(v___x_682_);
lean_del_object(v___x_666_);
lean_dec(v_cmdStx_656_);
v___x_865_ = lean_box(0);
v___x_866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_866_, 0, v___x_865_);
return v___x_866_;
}
else
{
lean_object* v___x_867_; uint8_t v___x_868_; 
v___x_867_ = l_Lean_Syntax_getArg(v___x_682_, v___x_681_);
v___x_868_ = l_Lean_Syntax_isNone(v___x_867_);
if (v___x_868_ == 0)
{
lean_object* v___x_869_; uint8_t v___x_870_; 
v___x_869_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_867_);
v___x_870_ = l_Lean_Syntax_matchesNull(v___x_867_, v___x_869_);
if (v___x_870_ == 0)
{
lean_object* v___x_871_; lean_object* v___x_872_; 
lean_dec(v___x_867_);
lean_dec(v___x_682_);
lean_del_object(v___x_666_);
lean_dec(v_cmdStx_656_);
v___x_871_ = lean_box(0);
v___x_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
return v___x_872_;
}
else
{
lean_object* v___x_873_; lean_object* v___x_874_; uint8_t v___x_875_; 
v___x_873_ = l_Lean_Syntax_getArg(v___x_867_, v___x_681_);
lean_dec(v___x_867_);
v___x_874_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__21));
v___x_875_ = l_Lean_Syntax_isOfKind(v___x_873_, v___x_874_);
if (v___x_875_ == 0)
{
lean_object* v___x_876_; lean_object* v___x_877_; 
lean_dec(v___x_682_);
lean_del_object(v___x_666_);
lean_dec(v_cmdStx_656_);
v___x_876_ = lean_box(0);
v___x_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_877_, 0, v___x_876_);
return v___x_877_;
}
else
{
v___y_841_ = v___y_657_;
v___y_842_ = v___y_658_;
goto v___jp_840_;
}
}
}
else
{
lean_dec(v___x_867_);
v___y_841_ = v___y_657_;
v___y_842_ = v___y_658_;
goto v___jp_840_;
}
}
v___jp_685_:
{
size_t v_sz_691_; size_t v___x_692_; lean_object* v___x_693_; 
v_sz_691_ = lean_array_size(v___y_690_);
v___x_692_ = ((size_t)0ULL);
v___x_693_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1(v_sz_691_, v___x_692_, v___y_690_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v___x_694_; lean_object* v___x_696_; 
lean_dec(v___x_682_);
lean_dec(v_cmdStx_656_);
v___x_694_ = lean_box(0);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 0, v___x_694_);
v___x_696_ = v___x_666_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v___x_694_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
else
{
lean_object* v_val_698_; lean_object* v___x_699_; lean_object* v___x_700_; uint8_t v___x_701_; 
v_val_698_ = lean_ctor_get(v___x_693_, 0);
lean_inc(v_val_698_);
lean_dec_ref_known(v___x_693_, 1);
v___x_699_ = lean_unsigned_to_nat(3u);
v___x_700_ = l_Lean_Syntax_getArg(v___x_682_, v___x_699_);
v___x_701_ = l_Lean_Syntax_matchesNull(v___x_700_, v___x_681_);
if (v___x_701_ == 0)
{
lean_object* v___x_702_; lean_object* v___x_704_; 
lean_dec(v_val_698_);
lean_dec(v___x_682_);
lean_dec(v_cmdStx_656_);
v___x_702_ = lean_box(0);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 0, v___x_702_);
v___x_704_ = v___x_666_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_702_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
else
{
lean_object* v___x_706_; lean_object* v___x_707_; uint8_t v___x_708_; 
v___x_706_ = lean_unsigned_to_nat(4u);
v___x_707_ = l_Lean_Syntax_getArg(v___x_682_, v___x_706_);
v___x_708_ = l_Lean_Syntax_matchesNull(v___x_707_, v___x_681_);
if (v___x_708_ == 0)
{
lean_object* v___x_709_; lean_object* v___x_711_; 
lean_dec(v_val_698_);
lean_dec(v___x_682_);
lean_dec(v_cmdStx_656_);
v___x_709_ = lean_box(0);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 0, v___x_709_);
v___x_711_ = v___x_666_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v___x_709_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
else
{
lean_object* v___x_713_; lean_object* v___x_714_; uint8_t v___x_715_; 
v___x_713_ = lean_unsigned_to_nat(5u);
v___x_714_ = l_Lean_Syntax_getArg(v___x_682_, v___x_713_);
v___x_715_ = l_Lean_Syntax_matchesNull(v___x_714_, v___x_681_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; lean_object* v___x_718_; 
lean_dec(v_val_698_);
lean_dec(v___x_682_);
lean_dec(v_cmdStx_656_);
v___x_716_ = lean_box(0);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 0, v___x_716_);
v___x_718_ = v___x_666_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_716_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
else
{
lean_object* v___x_720_; lean_object* v___x_721_; uint8_t v___x_722_; 
v___x_720_ = lean_unsigned_to_nat(6u);
v___x_721_ = l_Lean_Syntax_getArg(v___x_682_, v___x_720_);
lean_dec(v___x_682_);
v___x_722_ = l_Lean_Syntax_matchesNull(v___x_721_, v___x_681_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; lean_object* v___x_725_; 
lean_dec(v_val_698_);
lean_dec(v_cmdStx_656_);
v___x_723_ = lean_box(0);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 0, v___x_723_);
v___x_725_ = v___x_666_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_723_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
else
{
lean_object* v___x_727_; lean_object* v___x_728_; uint8_t v___x_729_; 
v___x_727_ = l_Lean_Syntax_getArg(v_cmdStx_656_, v___y_686_);
lean_dec(v_cmdStx_656_);
v___x_728_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__6));
lean_inc(v___x_727_);
v___x_729_ = l_Lean_Syntax_isOfKind(v___x_727_, v___x_728_);
if (v___x_729_ == 0)
{
lean_object* v___x_730_; lean_object* v___x_732_; 
lean_dec(v___x_727_);
lean_dec(v_val_698_);
v___x_730_ = lean_box(0);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 0, v___x_730_);
v___x_732_ = v___x_666_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_730_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
else
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; uint8_t v___x_737_; 
v___x_734_ = lean_unsigned_to_nat(2u);
v___x_735_ = l_Lean_Syntax_getArg(v___x_727_, v___x_734_);
v___x_736_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__8));
lean_inc(v___x_735_);
v___x_737_ = l_Lean_Syntax_isOfKind(v___x_735_, v___x_736_);
if (v___x_737_ == 0)
{
lean_object* v___x_738_; lean_object* v___x_740_; 
lean_dec(v___x_735_);
lean_dec(v___x_727_);
lean_dec(v_val_698_);
v___x_738_ = lean_box(0);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 0, v___x_738_);
v___x_740_ = v___x_666_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v___x_738_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
else
{
lean_object* v___x_742_; uint8_t v___x_743_; 
v___x_742_ = l_Lean_Syntax_getArg(v___x_735_, v___x_681_);
v___x_743_ = l_Lean_Syntax_matchesNull(v___x_742_, v___x_681_);
if (v___x_743_ == 0)
{
lean_object* v___x_744_; lean_object* v___x_746_; 
lean_dec(v___x_735_);
lean_dec(v___x_727_);
lean_dec(v_val_698_);
v___x_744_ = lean_box(0);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 0, v___x_744_);
v___x_746_ = v___x_666_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_744_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
else
{
lean_object* v___x_748_; uint8_t v___x_749_; 
v___x_748_ = l_Lean_Syntax_getArg(v___x_735_, v___y_686_);
lean_dec(v___x_735_);
lean_inc(v___x_748_);
v___x_749_ = l_Lean_Syntax_matchesNull(v___x_748_, v___y_686_);
if (v___x_749_ == 0)
{
lean_object* v___x_750_; lean_object* v___x_752_; 
lean_dec(v___x_748_);
lean_dec(v___x_727_);
lean_dec(v_val_698_);
v___x_750_ = lean_box(0);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 0, v___x_750_);
v___x_752_ = v___x_666_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_750_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
else
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; uint8_t v___x_757_; 
v___x_754_ = l_Lean_Syntax_getArg(v___x_748_, v___x_681_);
lean_dec(v___x_748_);
v___x_755_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__9));
lean_inc_ref(v___y_689_);
v___x_756_ = l_Lean_Name_mkStr4(v___x_673_, v___x_674_, v___y_689_, v___x_755_);
v___x_757_ = l_Lean_Syntax_isOfKind(v___x_754_, v___x_756_);
lean_dec(v___x_756_);
if (v___x_757_ == 0)
{
lean_object* v___x_758_; lean_object* v___x_760_; 
lean_dec(v___x_727_);
lean_dec(v_val_698_);
v___x_758_ = lean_box(0);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 0, v___x_758_);
v___x_760_ = v___x_666_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_758_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
else
{
lean_object* v___x_762_; lean_object* v___x_763_; uint8_t v___x_764_; 
v___x_762_ = l_Lean_Syntax_getArg(v___x_727_, v___x_699_);
v___x_763_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__11));
lean_inc(v___x_762_);
v___x_764_ = l_Lean_Syntax_isOfKind(v___x_762_, v___x_763_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; lean_object* v___x_767_; 
lean_dec(v___x_762_);
lean_dec(v___x_727_);
lean_dec(v_val_698_);
v___x_765_ = lean_box(0);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 0, v___x_765_);
v___x_767_ = v___x_666_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v___x_765_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
else
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; uint8_t v___x_772_; 
v___x_769_ = l_Lean_Syntax_getArg(v___x_762_, v___x_681_);
lean_dec(v___x_762_);
v___x_770_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__12));
lean_inc_ref(v___y_689_);
v___x_771_ = l_Lean_Name_mkStr4(v___x_673_, v___x_674_, v___y_689_, v___x_770_);
lean_inc(v___x_769_);
v___x_772_ = l_Lean_Syntax_isOfKind(v___x_769_, v___x_771_);
lean_dec(v___x_771_);
if (v___x_772_ == 0)
{
lean_object* v___x_773_; lean_object* v___x_775_; 
lean_dec(v___x_769_);
lean_dec(v___x_727_);
lean_dec(v_val_698_);
v___x_773_ = lean_box(0);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 0, v___x_773_);
v___x_775_ = v___x_666_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_773_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
else
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; uint8_t v___x_780_; 
v___x_777_ = l_Lean_Syntax_getArg(v___x_769_, v___x_681_);
v___x_778_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__13));
lean_inc_ref(v___y_689_);
v___x_779_ = l_Lean_Name_mkStr4(v___x_673_, v___x_674_, v___y_689_, v___x_778_);
lean_inc(v___x_777_);
v___x_780_ = l_Lean_Syntax_isOfKind(v___x_777_, v___x_779_);
lean_dec(v___x_779_);
if (v___x_780_ == 0)
{
lean_object* v___x_781_; lean_object* v___x_783_; 
lean_dec(v___x_777_);
lean_dec(v___x_769_);
lean_dec(v___x_727_);
lean_dec(v_val_698_);
v___x_781_ = lean_box(0);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 0, v___x_781_);
v___x_783_ = v___x_666_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_781_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
else
{
lean_object* v___x_785_; lean_object* v___x_786_; size_t v_sz_787_; lean_object* v___x_788_; 
v___x_785_ = l_Lean_Syntax_getArg(v___x_777_, v___x_681_);
lean_dec(v___x_777_);
v___x_786_ = l_Lean_Syntax_getArgs(v___x_785_);
lean_dec(v___x_785_);
v_sz_787_ = lean_array_size(v___x_786_);
v___x_788_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2(v_sz_787_, v___x_692_, v___x_786_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v___x_789_; lean_object* v___x_791_; 
lean_dec(v___x_769_);
lean_dec(v___x_727_);
lean_dec(v_val_698_);
v___x_789_ = lean_box(0);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 0, v___x_789_);
v___x_791_ = v___x_666_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_789_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
else
{
lean_object* v_val_793_; lean_object* v___x_794_; lean_object* v___x_795_; uint8_t v___x_796_; 
v_val_793_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_val_793_);
lean_dec_ref_known(v___x_788_, 1);
v___x_794_ = l_Lean_Syntax_getArg(v___x_769_, v___y_686_);
v___x_795_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__16));
lean_inc(v___x_794_);
v___x_796_ = l_Lean_Syntax_isOfKind(v___x_794_, v___x_795_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; lean_object* v___x_799_; 
lean_dec(v___x_794_);
lean_dec(v_val_793_);
lean_dec(v___x_769_);
lean_dec(v___x_727_);
lean_dec(v_val_698_);
v___x_797_ = lean_box(0);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 0, v___x_797_);
v___x_799_ = v___x_666_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_797_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
else
{
lean_object* v___x_801_; uint8_t v___x_802_; 
v___x_801_ = l_Lean_Syntax_getArg(v___x_794_, v___x_681_);
v___x_802_ = l_Lean_Syntax_matchesNull(v___x_801_, v___x_681_);
if (v___x_802_ == 0)
{
lean_object* v___x_803_; lean_object* v___x_805_; 
lean_dec(v___x_794_);
lean_dec(v_val_793_);
lean_dec(v___x_769_);
lean_dec(v___x_727_);
lean_dec(v_val_698_);
v___x_803_ = lean_box(0);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 0, v___x_803_);
v___x_805_ = v___x_666_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_803_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
else
{
lean_object* v___x_807_; uint8_t v___x_808_; 
v___x_807_ = l_Lean_Syntax_getArg(v___x_794_, v___y_686_);
lean_dec(v___x_794_);
v___x_808_ = l_Lean_Syntax_matchesNull(v___x_807_, v___x_681_);
if (v___x_808_ == 0)
{
lean_object* v___x_809_; lean_object* v___x_811_; 
lean_dec(v_val_793_);
lean_dec(v___x_769_);
lean_dec(v___x_727_);
lean_dec(v_val_698_);
v___x_809_ = lean_box(0);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 0, v___x_809_);
v___x_811_ = v___x_666_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_809_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
else
{
lean_object* v___x_813_; uint8_t v___x_814_; 
v___x_813_ = l_Lean_Syntax_getArg(v___x_769_, v___x_734_);
lean_dec(v___x_769_);
v___x_814_ = l_Lean_Syntax_matchesNull(v___x_813_, v___x_681_);
if (v___x_814_ == 0)
{
lean_object* v___x_815_; lean_object* v___x_817_; 
lean_dec(v_val_793_);
lean_dec(v___x_727_);
lean_dec(v_val_698_);
v___x_815_ = lean_box(0);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 0, v___x_815_);
v___x_817_ = v___x_666_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_815_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
else
{
lean_object* v___x_819_; uint8_t v___x_820_; 
v___x_819_ = l_Lean_Syntax_getArg(v___x_727_, v___x_706_);
lean_dec(v___x_727_);
v___x_820_ = l_Lean_Syntax_matchesNull(v___x_819_, v___x_681_);
if (v___x_820_ == 0)
{
lean_object* v___x_821_; lean_object* v___x_823_; 
lean_dec(v_val_793_);
lean_dec(v_val_698_);
v___x_821_ = lean_box(0);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 0, v___x_821_);
v___x_823_ = v___x_666_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_821_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
else
{
lean_object* v___x_825_; uint8_t v___x_826_; 
lean_del_object(v___x_666_);
v___x_825_ = lean_array_get_size(v_val_698_);
v___x_826_ = lean_nat_dec_lt(v___x_681_, v___x_825_);
if (v___x_826_ == 0)
{
lean_dec(v_val_793_);
lean_dec(v_val_698_);
goto v___jp_660_;
}
else
{
if (v___x_826_ == 0)
{
lean_dec(v_val_793_);
lean_dec(v_val_698_);
goto v___jp_660_;
}
else
{
size_t v___x_827_; uint8_t v___x_828_; 
v___x_827_ = lean_usize_of_nat(v___x_825_);
v___x_828_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3(v___x_684_, v_val_698_, v___x_692_, v___x_827_);
lean_dec(v_val_698_);
if (v___x_828_ == 0)
{
lean_dec(v_val_793_);
goto v___jp_660_;
}
else
{
lean_object* v___x_829_; size_t v_sz_830_; lean_object* v___x_831_; 
v___x_829_ = lean_box(0);
v_sz_830_ = lean_array_size(v_val_793_);
v___x_831_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5(v_val_793_, v_sz_830_, v___x_692_, v___x_829_, v___y_687_, v___y_688_);
lean_dec(v_val_793_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_838_ == 0)
{
lean_object* v_unused_839_; 
v_unused_839_ = lean_ctor_get(v___x_831_, 0);
lean_dec(v_unused_839_);
v___x_833_ = v___x_831_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_dec(v___x_831_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 0, v___x_829_);
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v___x_829_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
else
{
return v___x_831_;
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
v___jp_840_:
{
lean_object* v___x_843_; lean_object* v___x_844_; uint8_t v___x_845_; 
v___x_843_ = lean_unsigned_to_nat(1u);
v___x_844_ = l_Lean_Syntax_getArg(v___x_682_, v___x_843_);
lean_inc(v___x_844_);
v___x_845_ = l_Lean_Syntax_matchesNull(v___x_844_, v___x_843_);
if (v___x_845_ == 0)
{
lean_object* v___x_846_; lean_object* v___x_847_; 
lean_dec(v___x_844_);
lean_dec(v___x_682_);
lean_del_object(v___x_666_);
lean_dec(v_cmdStx_656_);
v___x_846_ = lean_box(0);
v___x_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
return v___x_847_;
}
else
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; uint8_t v___x_851_; 
v___x_848_ = l_Lean_Syntax_getArg(v___x_844_, v___x_681_);
lean_dec(v___x_844_);
v___x_849_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__1));
v___x_850_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__18));
lean_inc(v___x_848_);
v___x_851_ = l_Lean_Syntax_isOfKind(v___x_848_, v___x_850_);
if (v___x_851_ == 0)
{
lean_object* v___x_852_; lean_object* v___x_853_; 
lean_dec(v___x_848_);
lean_dec(v___x_682_);
lean_del_object(v___x_666_);
lean_dec(v_cmdStx_656_);
v___x_852_ = lean_box(0);
v___x_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
return v___x_853_;
}
else
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; uint8_t v___x_858_; 
v___x_854_ = l_Lean_Syntax_getArg(v___x_848_, v___x_843_);
lean_dec(v___x_848_);
v___x_855_ = l_Lean_Syntax_getArgs(v___x_854_);
lean_dec(v___x_854_);
v___x_856_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__19));
v___x_857_ = lean_array_get_size(v___x_855_);
v___x_858_ = lean_nat_dec_lt(v___x_681_, v___x_857_);
if (v___x_858_ == 0)
{
lean_dec_ref(v___x_855_);
v___y_686_ = v___x_843_;
v___y_687_ = v___y_841_;
v___y_688_ = v___y_842_;
v___y_689_ = v___x_849_;
v___y_690_ = v___x_856_;
goto v___jp_685_;
}
else
{
lean_object* v___x_859_; lean_object* v___x_860_; size_t v___x_861_; size_t v___x_862_; lean_object* v___x_863_; lean_object* v_snd_864_; 
v___x_859_ = lean_box(v___x_858_);
v___x_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_860_, 0, v___x_859_);
lean_ctor_set(v___x_860_, 1, v___x_856_);
v___x_861_ = ((size_t)0ULL);
v___x_862_ = lean_usize_of_nat(v___x_857_);
v___x_863_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__6(v___x_851_, v___x_855_, v___x_861_, v___x_862_, v___x_860_);
lean_dec_ref(v___x_855_);
v_snd_864_ = lean_ctor_get(v___x_863_, 1);
lean_inc(v_snd_864_);
lean_dec_ref(v___x_863_);
v___y_686_ = v___x_843_;
v___y_687_ = v___y_841_;
v___y_688_ = v___y_842_;
v___y_689_ = v___x_849_;
v___y_690_ = v_snd_864_;
goto v___jp_685_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___boxed(lean_object* v_cmdStx_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0(v_cmdStx_879_, v___y_880_, v___y_881_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0(lean_object* v_o_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
lean_object* v___x_897_; 
v___x_897_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0___redArg(v_o_893_, v___y_895_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0___boxed(lean_object* v_o_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0(v_o_898_, v___y_899_, v___y_900_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9(lean_object* v_msgData_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg(v_msgData_903_, v___y_905_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___boxed(lean_object* v_msgData_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9(v_msgData_908_, v___y_909_, v___y_910_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1774244096____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_914_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns));
v___x_915_ = l_Lean_Elab_Command_addLinter(v___x_914_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1774244096____hygCtx___hyg_2____boxed(lean_object* v_a_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1774244096____hygCtx___hyg_2_();
return v_res_917_;
}
}
lean_object* runtime_initialize_Lean_Linter_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_Builtin(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
