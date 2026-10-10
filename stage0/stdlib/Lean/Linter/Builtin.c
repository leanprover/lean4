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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1_ = stack[0].m_obj;
lean_object* v_decl_2_ = stack[1].m_obj;
lean_object* v_ref_3_ = stack[2].m_obj;
lean_object* v_res_29_;
v_res_29_ = l_Lean_Option_register___at___00__private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__spec__0(v_name_1_, v_decl_2_, v_ref_3_);
stack->m_obj
 = v_res_29_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_30_, lean_object* v_decl_31_, lean_object* v_ref_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Option_register___at___00__private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__spec__0(v_name_30_, v_decl_31_, v_ref_32_);
lean_dec_ref(v_decl_31_);
return v_res_34_;
}
}
lean_object* l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_54_ = ((lean_object*)(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_));
v___x_55_ = ((lean_object*)(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_));
v___x_56_ = ((lean_object*)(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_));
v___x_57_ = l_Lean_Option_register___at___00__private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__spec__0(v___x_54_, v___x_55_, v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT void l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_58_;
v_res_58_ = l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_();
stack->m_obj
 = v_res_58_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4____boxed(lean_object* v_a_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_();
return v_res_60_;
}
}
uint8_t l_Lean_Linter_getLinterSuspiciousUnexpanderPatterns(lean_object* v_o_61_){
_start:
{
lean_object* v___x_62_; uint8_t v___x_63_; 
v___x_62_ = l_Lean_Linter_linter_suspiciousUnexpanderPatterns;
v___x_63_ = l_Lean_Linter_getLinterValue(v___x_62_, v_o_61_);
return v___x_63_;
}
}
LEAN_EXPORT void l_Lean_Linter_getLinterSuspiciousUnexpanderPatterns_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_61_ = stack[0].m_obj;
uint8_t v_res_64_;
v_res_64_ = l_Lean_Linter_getLinterSuspiciousUnexpanderPatterns(v_o_61_);
stack->m_num = v_res_64_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterSuspiciousUnexpanderPatterns___boxed(lean_object* v_o_65_){
_start:
{
uint8_t v_res_66_; lean_object* v_r_67_; 
v_res_66_ = l_Lean_Linter_getLinterSuspiciousUnexpanderPatterns(v_o_65_);
lean_dec_ref(v_o_65_);
v_r_67_ = lean_box(v_res_66_);
return v_r_67_;
}
}
lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0___redArg(lean_object* v_o_68_, lean_object* v___y_69_){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v_env_73_; lean_object* v___x_74_; lean_object* v_toEnvExtension_75_; lean_object* v_asyncMode_76_; lean_object* v___x_77_; uint8_t v___x_78_; lean_object* v___x_79_; lean_object* v_merged_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_88_; 
v___x_71_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_72_ = lean_st_ref_get(v___y_69_);
v_env_73_ = lean_ctor_get(v___x_72_, 0);
lean_inc_ref(v_env_73_);
lean_dec(v___x_72_);
v___x_74_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_75_ = lean_ctor_get(v___x_74_, 0);
v_asyncMode_76_ = lean_ctor_get(v_toEnvExtension_75_, 2);
v___x_77_ = lean_box(0);
v___x_78_ = 0;
v___x_79_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_71_, v___x_74_, v_env_73_, v_asyncMode_76_, v___x_77_, v___x_78_);
v_merged_80_ = lean_ctor_get(v___x_79_, 0);
v_isSharedCheck_88_ = !lean_is_exclusive(v___x_79_);
if (v_isSharedCheck_88_ == 0)
{
lean_object* v_unused_89_; 
v_unused_89_ = lean_ctor_get(v___x_79_, 1);
lean_dec(v_unused_89_);
v___x_82_ = v___x_79_;
v_isShared_83_ = v_isSharedCheck_88_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_merged_80_);
lean_dec(v___x_79_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_88_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v___x_85_; 
if (v_isShared_83_ == 0)
{
lean_ctor_set(v___x_82_, 1, v_merged_80_);
lean_ctor_set(v___x_82_, 0, v_o_68_);
v___x_85_ = v___x_82_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v_o_68_);
lean_ctor_set(v_reuseFailAlloc_87_, 1, v_merged_80_);
v___x_85_ = v_reuseFailAlloc_87_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
lean_object* v___x_86_; 
v___x_86_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
return v___x_86_;
}
}
}
}
LEAN_EXPORT void l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_68_ = stack[0].m_obj;
lean_object* v___y_69_ = stack[1].m_obj;
lean_object* v_res_90_;
v_res_90_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0___redArg(v_o_68_, v___y_69_);
stack->m_obj
 = v_res_90_;
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0___redArg___boxed(lean_object* v_o_91_, lean_object* v___y_92_, lean_object* v___y_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0___redArg(v_o_91_, v___y_92_);
lean_dec(v___y_92_);
return v_res_94_;
}
}
lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0(lean_object* v___y_95_, lean_object* v___y_96_){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v_scopes_100_; lean_object* v___x_101_; lean_object* v_opts_102_; lean_object* v___x_103_; 
v___x_98_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_99_ = lean_st_ref_get(v___y_96_);
v_scopes_100_ = lean_ctor_get(v___x_99_, 2);
lean_inc(v_scopes_100_);
lean_dec(v___x_99_);
v___x_101_ = l_List_head_x21___redArg(v___x_98_, v_scopes_100_);
lean_dec(v_scopes_100_);
v_opts_102_ = lean_ctor_get(v___x_101_, 1);
lean_inc_ref(v_opts_102_);
lean_dec(v___x_101_);
v___x_103_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0___redArg(v_opts_102_, v___y_96_);
return v___x_103_;
}
}
LEAN_EXPORT void l_Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_95_ = stack[0].m_obj;
lean_object* v___y_96_ = stack[1].m_obj;
lean_object* v_res_104_;
v_res_104_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0(v___y_95_, v___y_96_);
stack->m_obj
 = v_res_104_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0___boxed(lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0(v___y_105_, v___y_106_);
lean_dec(v___y_106_);
lean_dec_ref(v___y_105_);
return v_res_108_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1(size_t v_sz_123_, size_t v_i_124_, lean_object* v_bs_125_){
_start:
{
uint8_t v___x_126_; 
v___x_126_ = lean_usize_dec_lt(v_i_124_, v_sz_123_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; 
v___x_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_127_, 0, v_bs_125_);
return v___x_127_;
}
else
{
lean_object* v_v_128_; lean_object* v___x_129_; uint8_t v___x_130_; 
v_v_128_ = lean_array_uget(v_bs_125_, v_i_124_);
v___x_129_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__3));
lean_inc(v_v_128_);
v___x_130_ = l_Lean_Syntax_isOfKind(v_v_128_, v___x_129_);
if (v___x_130_ == 0)
{
lean_object* v___x_131_; 
lean_dec(v_v_128_);
lean_dec_ref(v_bs_125_);
v___x_131_ = lean_box(0);
return v___x_131_;
}
else
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; uint8_t v___x_135_; 
v___x_132_ = lean_unsigned_to_nat(0u);
v___x_133_ = l_Lean_Syntax_getArg(v_v_128_, v___x_132_);
v___x_134_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__5));
lean_inc(v___x_133_);
v___x_135_ = l_Lean_Syntax_isOfKind(v___x_133_, v___x_134_);
if (v___x_135_ == 0)
{
lean_object* v___x_136_; 
lean_dec(v___x_133_);
lean_dec(v_v_128_);
lean_dec_ref(v_bs_125_);
v___x_136_ = lean_box(0);
return v___x_136_;
}
else
{
lean_object* v___x_137_; uint8_t v___x_138_; 
v___x_137_ = l_Lean_Syntax_getArg(v___x_133_, v___x_132_);
lean_dec(v___x_133_);
v___x_138_ = l_Lean_Syntax_matchesNull(v___x_137_, v___x_132_);
if (v___x_138_ == 0)
{
lean_object* v___x_139_; 
lean_dec(v_v_128_);
lean_dec_ref(v_bs_125_);
v___x_139_ = lean_box(0);
return v___x_139_;
}
else
{
lean_object* v___x_140_; lean_object* v_bs_x27_141_; lean_object* v___x_142_; size_t v___x_143_; size_t v___x_144_; lean_object* v___x_145_; 
v___x_140_ = lean_unsigned_to_nat(1u);
v_bs_x27_141_ = lean_array_uset(v_bs_125_, v_i_124_, v___x_132_);
v___x_142_ = l_Lean_Syntax_getArg(v_v_128_, v___x_140_);
lean_dec(v_v_128_);
v___x_143_ = ((size_t)1ULL);
v___x_144_ = lean_usize_add(v_i_124_, v___x_143_);
v___x_145_ = lean_array_uset(v_bs_x27_141_, v_i_124_, v___x_142_);
v_i_124_ = v___x_144_;
v_bs_125_ = v___x_145_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_123_ = stack[0].m_num;
size_t v_i_124_ = stack[1].m_num;
lean_object* v_bs_125_ = stack[2].m_obj;
lean_object* v_res_147_;
v_res_147_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1(v_sz_123_, v_i_124_, v_bs_125_);
stack->m_obj
 = v_res_147_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___boxed(lean_object* v_sz_148_, lean_object* v_i_149_, lean_object* v_bs_150_){
_start:
{
size_t v_sz_boxed_151_; size_t v_i_boxed_152_; lean_object* v_res_153_; 
v_sz_boxed_151_ = lean_unbox_usize(v_sz_148_);
lean_dec(v_sz_148_);
v_i_boxed_152_ = lean_unbox_usize(v_i_149_);
lean_dec(v_i_149_);
v_res_153_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1(v_sz_boxed_151_, v_i_boxed_152_, v_bs_150_);
return v_res_153_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__10(lean_object* v_opts_154_, lean_object* v_opt_155_){
_start:
{
lean_object* v_name_156_; lean_object* v_defValue_157_; lean_object* v_map_158_; lean_object* v___x_159_; 
v_name_156_ = lean_ctor_get(v_opt_155_, 0);
v_defValue_157_ = lean_ctor_get(v_opt_155_, 1);
v_map_158_ = lean_ctor_get(v_opts_154_, 0);
v___x_159_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_158_, v_name_156_);
if (lean_obj_tag(v___x_159_) == 0)
{
uint8_t v___x_160_; 
v___x_160_ = lean_unbox(v_defValue_157_);
return v___x_160_;
}
else
{
lean_object* v_val_161_; 
v_val_161_ = lean_ctor_get(v___x_159_, 0);
lean_inc(v_val_161_);
lean_dec_ref_known(v___x_159_, 1);
if (lean_obj_tag(v_val_161_) == 1)
{
uint8_t v_v_162_; 
v_v_162_ = lean_ctor_get_uint8(v_val_161_, 0);
lean_dec_ref_known(v_val_161_, 0);
return v_v_162_;
}
else
{
uint8_t v___x_163_; 
lean_dec(v_val_161_);
v___x_163_ = lean_unbox(v_defValue_157_);
return v___x_163_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_154_ = stack[0].m_obj;
lean_object* v_opt_155_ = stack[1].m_obj;
uint8_t v_res_164_;
v_res_164_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__10(v_opts_154_, v_opt_155_);
stack->m_num = v_res_164_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__10___boxed(lean_object* v_opts_165_, lean_object* v_opt_166_){
_start:
{
uint8_t v_res_167_; lean_object* v_r_168_; 
v_res_167_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__10(v_opts_165_, v_opt_166_);
lean_dec_ref(v_opt_166_);
lean_dec_ref(v_opts_165_);
v_r_168_ = lean_box(v_res_167_);
return v_r_168_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_169_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__0);
v___x_171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
return v___x_171_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_172_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_173_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1);
v___x_174_ = lean_unsigned_to_nat(0u);
v___x_175_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
lean_ctor_set(v___x_175_, 1, v___x_174_);
lean_ctor_set(v___x_175_, 2, v___x_174_);
lean_ctor_set(v___x_175_, 3, v___x_174_);
lean_ctor_set(v___x_175_, 4, v___x_173_);
lean_ctor_set(v___x_175_, 5, v___x_173_);
lean_ctor_set(v___x_175_, 6, v___x_173_);
lean_ctor_set(v___x_175_, 7, v___x_173_);
lean_ctor_set(v___x_175_, 8, v___x_173_);
lean_ctor_set(v___x_175_, 9, v___x_173_);
lean_ctor_set(v___x_175_, 10, v___x_173_);
lean_ctor_set(v___x_175_, 11, v___x_172_);
return v___x_175_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_176_ = lean_unsigned_to_nat(32u);
v___x_177_ = lean_mk_empty_array_with_capacity(v___x_176_);
v___x_178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
return v___x_178_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__4(void){
_start:
{
size_t v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_179_ = ((size_t)5ULL);
v___x_180_ = lean_unsigned_to_nat(0u);
v___x_181_ = lean_unsigned_to_nat(32u);
v___x_182_ = lean_mk_empty_array_with_capacity(v___x_181_);
v___x_183_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__3);
v___x_184_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_184_, 0, v___x_183_);
lean_ctor_set(v___x_184_, 1, v___x_182_);
lean_ctor_set(v___x_184_, 2, v___x_180_);
lean_ctor_set(v___x_184_, 3, v___x_180_);
lean_ctor_set_usize(v___x_184_, 4, v___x_179_);
return v___x_184_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_185_ = lean_box(1);
v___x_186_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__4);
v___x_187_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1);
v___x_188_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
lean_ctor_set(v___x_188_, 1, v___x_186_);
lean_ctor_set(v___x_188_, 2, v___x_185_);
return v___x_188_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg(lean_object* v_msgData_189_, lean_object* v___y_190_){
_start:
{
lean_object* v___x_192_; lean_object* v_env_193_; uint8_t v___x_194_; lean_object* v_env_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v_scopes_198_; lean_object* v___x_199_; lean_object* v_opts_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_192_ = lean_st_ref_get(v___y_190_);
v_env_193_ = lean_ctor_get(v___x_192_, 0);
lean_inc_ref(v_env_193_);
lean_dec(v___x_192_);
v___x_194_ = 0;
v_env_195_ = l_Lean_Environment_setRecordingDeps(v_env_193_, v___x_194_);
v___x_196_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_197_ = lean_st_ref_get(v___y_190_);
v_scopes_198_ = lean_ctor_get(v___x_197_, 2);
lean_inc(v_scopes_198_);
lean_dec(v___x_197_);
v___x_199_ = l_List_head_x21___redArg(v___x_196_, v_scopes_198_);
lean_dec(v_scopes_198_);
v_opts_200_ = lean_ctor_get(v___x_199_, 1);
lean_inc_ref(v_opts_200_);
lean_dec(v___x_199_);
v___x_201_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__2);
v___x_202_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__5);
v___x_203_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_203_, 0, v_env_195_);
lean_ctor_set(v___x_203_, 1, v___x_201_);
lean_ctor_set(v___x_203_, 2, v___x_202_);
lean_ctor_set(v___x_203_, 3, v_opts_200_);
v___x_204_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
lean_ctor_set(v___x_204_, 1, v_msgData_189_);
v___x_205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
return v___x_205_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_189_ = stack[0].m_obj;
lean_object* v___y_190_ = stack[1].m_obj;
lean_object* v_res_206_;
v_res_206_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg(v_msgData_189_, v___y_190_);
stack->m_obj
 = v_res_206_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___boxed(lean_object* v_msgData_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg(v_msgData_207_, v___y_208_);
lean_dec(v___y_208_);
return v_res_210_;
}
}
uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0(uint8_t v_suppressElabErrors_212_, uint8_t v___y_213_, lean_object* v_x_214_){
_start:
{
if (lean_obj_tag(v_x_214_) == 1)
{
lean_object* v_pre_215_; 
v_pre_215_ = lean_ctor_get(v_x_214_, 0);
if (lean_obj_tag(v_pre_215_) == 0)
{
lean_object* v_str_216_; lean_object* v___x_217_; uint8_t v___x_218_; 
v_str_216_ = lean_ctor_get(v_x_214_, 1);
v___x_217_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0___closed__0));
v___x_218_ = lean_string_dec_eq(v_str_216_, v___x_217_);
if (v___x_218_ == 0)
{
return v___x_218_;
}
else
{
return v_suppressElabErrors_212_;
}
}
else
{
return v___y_213_;
}
}
else
{
return v___y_213_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_212_ = stack[0].m_num;
uint8_t v___y_213_ = stack[1].m_num;
lean_object* v_x_214_ = stack[2].m_obj;
uint8_t v_res_219_;
v_res_219_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0(v_suppressElabErrors_212_, v___y_213_, v_x_214_);
stack->m_num = v_res_219_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0___boxed(lean_object* v_suppressElabErrors_220_, lean_object* v___y_221_, lean_object* v_x_222_){
_start:
{
uint8_t v_suppressElabErrors_boxed_223_; uint8_t v___y_10345__boxed_224_; uint8_t v_res_225_; lean_object* v_r_226_; 
v_suppressElabErrors_boxed_223_ = lean_unbox(v_suppressElabErrors_220_);
v___y_10345__boxed_224_ = lean_unbox(v___y_221_);
v_res_225_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0(v_suppressElabErrors_boxed_223_, v___y_10345__boxed_224_, v_x_222_);
lean_dec(v_x_222_);
v_r_226_ = lean_box(v_res_225_);
return v_r_226_;
}
}
lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6(lean_object* v_ref_228_, lean_object* v_msgData_229_, uint8_t v_severity_230_, uint8_t v_isSilent_231_, lean_object* v___y_232_, lean_object* v___y_233_){
_start:
{
uint8_t v___y_236_; lean_object* v___y_237_; lean_object* v___y_238_; lean_object* v___y_239_; lean_object* v___y_240_; lean_object* v___y_241_; uint8_t v___y_242_; lean_object* v___y_243_; uint8_t v___y_301_; uint8_t v___y_302_; lean_object* v___y_303_; uint8_t v___y_304_; lean_object* v___y_305_; uint8_t v___y_329_; uint8_t v___y_330_; lean_object* v___y_331_; uint8_t v___y_332_; lean_object* v___y_333_; uint8_t v___y_337_; uint8_t v___y_338_; uint8_t v___y_339_; uint8_t v___x_354_; uint8_t v___y_356_; uint8_t v___y_357_; uint8_t v___y_358_; uint8_t v___y_360_; uint8_t v___x_372_; 
v___x_354_ = 2;
v___x_372_ = l_Lean_instBEqMessageSeverity_beq(v_severity_230_, v___x_354_);
if (v___x_372_ == 0)
{
v___y_360_ = v___x_372_;
goto v___jp_359_;
}
else
{
uint8_t v___x_373_; 
lean_inc_ref(v_msgData_229_);
v___x_373_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_229_);
v___y_360_ = v___x_373_;
goto v___jp_359_;
}
v___jp_235_:
{
lean_object* v___x_244_; 
v___x_244_ = l_Lean_Elab_Command_getScope___redArg(v___y_243_);
if (lean_obj_tag(v___x_244_) == 0)
{
lean_object* v_a_245_; lean_object* v_currNamespace_246_; lean_object* v___x_247_; 
v_a_245_ = lean_ctor_get(v___x_244_, 0);
lean_inc(v_a_245_);
lean_dec_ref_known(v___x_244_, 1);
v_currNamespace_246_ = lean_ctor_get(v_a_245_, 2);
lean_inc(v_currNamespace_246_);
lean_dec(v_a_245_);
v___x_247_ = l_Lean_Elab_Command_getScope___redArg(v___y_243_);
if (lean_obj_tag(v___x_247_) == 0)
{
lean_object* v_a_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_283_; 
v_a_248_ = lean_ctor_get(v___x_247_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_283_ == 0)
{
v___x_250_ = v___x_247_;
v_isShared_251_ = v_isSharedCheck_283_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_a_248_);
lean_dec(v___x_247_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_283_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v_openDecls_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v_env_257_; lean_object* v_messages_258_; lean_object* v_scopes_259_; lean_object* v_usedQuotCtxts_260_; lean_object* v_nextMacroScope_261_; lean_object* v_maxRecDepth_262_; lean_object* v_ngen_263_; lean_object* v_auxDeclNGen_264_; lean_object* v_infoState_265_; lean_object* v_traceState_266_; lean_object* v_snapshotTasks_267_; lean_object* v_prevLinterStates_268_; lean_object* v_codeQualityEntryTasks_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_282_; 
v_openDecls_252_ = lean_ctor_get(v_a_248_, 3);
lean_inc(v_openDecls_252_);
lean_dec(v_a_248_);
v___x_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_253_, 0, v_currNamespace_246_);
lean_ctor_set(v___x_253_, 1, v_openDecls_252_);
v___x_254_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
lean_ctor_set(v___x_254_, 1, v___y_241_);
lean_inc_ref(v___y_240_);
lean_inc_ref(v___y_238_);
v___x_255_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_255_, 0, v___y_238_);
lean_ctor_set(v___x_255_, 1, v___y_239_);
lean_ctor_set(v___x_255_, 2, v___y_237_);
lean_ctor_set(v___x_255_, 3, v___y_240_);
lean_ctor_set(v___x_255_, 4, v___x_254_);
lean_ctor_set_uint8(v___x_255_, sizeof(void*)*5, v___y_242_);
lean_ctor_set_uint8(v___x_255_, sizeof(void*)*5 + 1, v___y_236_);
lean_ctor_set_uint8(v___x_255_, sizeof(void*)*5 + 2, v_isSilent_231_);
v___x_256_ = lean_st_ref_take(v___y_243_);
v_env_257_ = lean_ctor_get(v___x_256_, 0);
v_messages_258_ = lean_ctor_get(v___x_256_, 1);
v_scopes_259_ = lean_ctor_get(v___x_256_, 2);
v_usedQuotCtxts_260_ = lean_ctor_get(v___x_256_, 3);
v_nextMacroScope_261_ = lean_ctor_get(v___x_256_, 4);
v_maxRecDepth_262_ = lean_ctor_get(v___x_256_, 5);
v_ngen_263_ = lean_ctor_get(v___x_256_, 6);
v_auxDeclNGen_264_ = lean_ctor_get(v___x_256_, 7);
v_infoState_265_ = lean_ctor_get(v___x_256_, 8);
v_traceState_266_ = lean_ctor_get(v___x_256_, 9);
v_snapshotTasks_267_ = lean_ctor_get(v___x_256_, 10);
v_prevLinterStates_268_ = lean_ctor_get(v___x_256_, 11);
v_codeQualityEntryTasks_269_ = lean_ctor_get(v___x_256_, 12);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_282_ == 0)
{
v___x_271_ = v___x_256_;
v_isShared_272_ = v_isSharedCheck_282_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_codeQualityEntryTasks_269_);
lean_inc(v_prevLinterStates_268_);
lean_inc(v_snapshotTasks_267_);
lean_inc(v_traceState_266_);
lean_inc(v_infoState_265_);
lean_inc(v_auxDeclNGen_264_);
lean_inc(v_ngen_263_);
lean_inc(v_maxRecDepth_262_);
lean_inc(v_nextMacroScope_261_);
lean_inc(v_usedQuotCtxts_260_);
lean_inc(v_scopes_259_);
lean_inc(v_messages_258_);
lean_inc(v_env_257_);
lean_dec(v___x_256_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_282_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_276_; 
v___x_273_ = lean_box(0);
v___x_274_ = l_Lean_MessageLog_add(v___x_255_, v_messages_258_);
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 1, v___x_274_);
v___x_276_ = v___x_271_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_env_257_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v___x_274_);
lean_ctor_set(v_reuseFailAlloc_281_, 2, v_scopes_259_);
lean_ctor_set(v_reuseFailAlloc_281_, 3, v_usedQuotCtxts_260_);
lean_ctor_set(v_reuseFailAlloc_281_, 4, v_nextMacroScope_261_);
lean_ctor_set(v_reuseFailAlloc_281_, 5, v_maxRecDepth_262_);
lean_ctor_set(v_reuseFailAlloc_281_, 6, v_ngen_263_);
lean_ctor_set(v_reuseFailAlloc_281_, 7, v_auxDeclNGen_264_);
lean_ctor_set(v_reuseFailAlloc_281_, 8, v_infoState_265_);
lean_ctor_set(v_reuseFailAlloc_281_, 9, v_traceState_266_);
lean_ctor_set(v_reuseFailAlloc_281_, 10, v_snapshotTasks_267_);
lean_ctor_set(v_reuseFailAlloc_281_, 11, v_prevLinterStates_268_);
lean_ctor_set(v_reuseFailAlloc_281_, 12, v_codeQualityEntryTasks_269_);
v___x_276_ = v_reuseFailAlloc_281_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
lean_object* v___x_277_; lean_object* v___x_279_; 
v___x_277_ = lean_st_ref_put(v___y_243_, v___x_276_);
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 0, v___x_273_);
v___x_279_ = v___x_250_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_273_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
}
else
{
lean_object* v_a_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_291_; 
lean_dec(v_currNamespace_246_);
lean_dec_ref(v___y_241_);
lean_dec_ref(v___y_239_);
lean_dec(v___y_237_);
v_a_284_ = lean_ctor_get(v___x_247_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_291_ == 0)
{
v___x_286_ = v___x_247_;
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_a_284_);
lean_dec(v___x_247_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_289_; 
if (v_isShared_287_ == 0)
{
v___x_289_ = v___x_286_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_a_284_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
}
else
{
lean_object* v_a_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_299_; 
lean_dec_ref(v___y_241_);
lean_dec_ref(v___y_239_);
lean_dec(v___y_237_);
v_a_292_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_299_ == 0)
{
v___x_294_ = v___x_244_;
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_a_292_);
lean_dec(v___x_244_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_297_; 
if (v_isShared_295_ == 0)
{
v___x_297_ = v___x_294_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_a_292_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
}
v___jp_300_:
{
lean_object* v_fileName_306_; lean_object* v_fileMap_307_; uint8_t v_suppressElabErrors_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___f_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v_a_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_327_; 
v_fileName_306_ = lean_ctor_get(v___y_232_, 0);
v_fileMap_307_ = lean_ctor_get(v___y_232_, 1);
v_suppressElabErrors_308_ = lean_ctor_get_uint8(v___y_232_, sizeof(void*)*10);
v___x_309_ = lean_box(v_suppressElabErrors_308_);
v___x_310_ = lean_box(v___y_301_);
v___f_311_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0___boxed), 3, 2);
lean_closure_set(v___f_311_, 0, v___x_309_);
lean_closure_set(v___f_311_, 1, v___x_310_);
v___x_312_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_229_);
v___x_313_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg(v___x_312_, v___y_233_);
v_a_314_ = lean_ctor_get(v___x_313_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_313_);
if (v_isSharedCheck_327_ == 0)
{
v___x_316_ = v___x_313_;
v_isShared_317_ = v_isSharedCheck_327_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_a_314_);
lean_dec(v___x_313_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_327_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
lean_inc_ref_n(v_fileMap_307_, 2);
v___x_318_ = l_Lean_FileMap_toPosition(v_fileMap_307_, v___y_303_);
lean_dec(v___y_303_);
v___x_319_ = l_Lean_FileMap_toPosition(v_fileMap_307_, v___y_305_);
lean_dec(v___y_305_);
v___x_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
v___x_321_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___closed__0));
if (v_suppressElabErrors_308_ == 0)
{
lean_del_object(v___x_316_);
lean_dec_ref(v___f_311_);
v___y_236_ = v___y_302_;
v___y_237_ = v___x_320_;
v___y_238_ = v_fileName_306_;
v___y_239_ = v___x_318_;
v___y_240_ = v___x_321_;
v___y_241_ = v_a_314_;
v___y_242_ = v___y_304_;
v___y_243_ = v___y_233_;
goto v___jp_235_;
}
else
{
uint8_t v___x_322_; 
lean_inc(v_a_314_);
v___x_322_ = l_Lean_MessageData_hasTag(v___f_311_, v_a_314_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; lean_object* v___x_325_; 
lean_dec_ref_known(v___x_320_, 1);
lean_dec_ref(v___x_318_);
lean_dec(v_a_314_);
v___x_323_ = lean_box(0);
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 0, v___x_323_);
v___x_325_ = v___x_316_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_323_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
else
{
lean_del_object(v___x_316_);
v___y_236_ = v___y_302_;
v___y_237_ = v___x_320_;
v___y_238_ = v_fileName_306_;
v___y_239_ = v___x_318_;
v___y_240_ = v___x_321_;
v___y_241_ = v_a_314_;
v___y_242_ = v___y_304_;
v___y_243_ = v___y_233_;
goto v___jp_235_;
}
}
}
}
v___jp_328_:
{
lean_object* v___x_334_; 
v___x_334_ = l_Lean_Syntax_getTailPos_x3f(v___y_331_, v___y_332_);
lean_dec(v___y_331_);
if (lean_obj_tag(v___x_334_) == 0)
{
lean_inc(v___y_333_);
v___y_301_ = v___y_329_;
v___y_302_ = v___y_330_;
v___y_303_ = v___y_333_;
v___y_304_ = v___y_332_;
v___y_305_ = v___y_333_;
goto v___jp_300_;
}
else
{
lean_object* v_val_335_; 
v_val_335_ = lean_ctor_get(v___x_334_, 0);
lean_inc(v_val_335_);
lean_dec_ref_known(v___x_334_, 1);
v___y_301_ = v___y_329_;
v___y_302_ = v___y_330_;
v___y_303_ = v___y_333_;
v___y_304_ = v___y_332_;
v___y_305_ = v_val_335_;
goto v___jp_300_;
}
}
v___jp_336_:
{
lean_object* v___x_340_; 
v___x_340_ = l_Lean_Elab_Command_getRef___redArg(v___y_232_);
if (lean_obj_tag(v___x_340_) == 0)
{
lean_object* v_a_341_; lean_object* v_ref_342_; lean_object* v___x_343_; 
v_a_341_ = lean_ctor_get(v___x_340_, 0);
lean_inc(v_a_341_);
lean_dec_ref_known(v___x_340_, 1);
v_ref_342_ = l_Lean_replaceRef(v_ref_228_, v_a_341_);
lean_dec(v_a_341_);
v___x_343_ = l_Lean_Syntax_getPos_x3f(v_ref_342_, v___y_338_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v___x_344_; 
v___x_344_ = lean_unsigned_to_nat(0u);
v___y_329_ = v___y_337_;
v___y_330_ = v___y_339_;
v___y_331_ = v_ref_342_;
v___y_332_ = v___y_338_;
v___y_333_ = v___x_344_;
goto v___jp_328_;
}
else
{
lean_object* v_val_345_; 
v_val_345_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_val_345_);
lean_dec_ref_known(v___x_343_, 1);
v___y_329_ = v___y_337_;
v___y_330_ = v___y_339_;
v___y_331_ = v_ref_342_;
v___y_332_ = v___y_338_;
v___y_333_ = v_val_345_;
goto v___jp_328_;
}
}
else
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_353_; 
lean_dec_ref(v_msgData_229_);
v_a_346_ = lean_ctor_get(v___x_340_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_353_ == 0)
{
v___x_348_ = v___x_340_;
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_340_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_351_; 
if (v_isShared_349_ == 0)
{
v___x_351_ = v___x_348_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_a_346_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
}
v___jp_355_:
{
if (v___y_358_ == 0)
{
v___y_337_ = v___y_356_;
v___y_338_ = v___y_357_;
v___y_339_ = v_severity_230_;
goto v___jp_336_;
}
else
{
v___y_337_ = v___y_356_;
v___y_338_ = v___y_357_;
v___y_339_ = v___x_354_;
goto v___jp_336_;
}
}
v___jp_359_:
{
if (v___y_360_ == 0)
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v_scopes_363_; lean_object* v___x_364_; lean_object* v_opts_365_; uint8_t v___x_366_; uint8_t v___x_367_; 
v___x_361_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_362_ = lean_st_ref_get(v___y_233_);
v_scopes_363_ = lean_ctor_get(v___x_362_, 2);
lean_inc(v_scopes_363_);
lean_dec(v___x_362_);
v___x_364_ = l_List_head_x21___redArg(v___x_361_, v_scopes_363_);
lean_dec(v_scopes_363_);
v_opts_365_ = lean_ctor_get(v___x_364_, 1);
lean_inc_ref(v_opts_365_);
lean_dec(v___x_364_);
v___x_366_ = 1;
v___x_367_ = l_Lean_instBEqMessageSeverity_beq(v_severity_230_, v___x_366_);
if (v___x_367_ == 0)
{
lean_dec_ref(v_opts_365_);
v___y_356_ = v___y_360_;
v___y_357_ = v___y_360_;
v___y_358_ = v___x_367_;
goto v___jp_355_;
}
else
{
lean_object* v___x_368_; uint8_t v___x_369_; 
v___x_368_ = l_Lean_warningAsError;
v___x_369_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__10(v_opts_365_, v___x_368_);
lean_dec_ref(v_opts_365_);
v___y_356_ = v___y_360_;
v___y_357_ = v___y_360_;
v___y_358_ = v___x_369_;
goto v___jp_355_;
}
}
else
{
lean_object* v___x_370_; lean_object* v___x_371_; 
lean_dec_ref(v_msgData_229_);
v___x_370_ = lean_box(0);
v___x_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
return v___x_371_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_228_ = stack[0].m_obj;
lean_object* v_msgData_229_ = stack[1].m_obj;
uint8_t v_severity_230_ = stack[2].m_num;
uint8_t v_isSilent_231_ = stack[3].m_num;
lean_object* v___y_232_ = stack[4].m_obj;
lean_object* v___y_233_ = stack[5].m_obj;
lean_object* v_res_374_;
v_res_374_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6(v_ref_228_, v_msgData_229_, v_severity_230_, v_isSilent_231_, v___y_232_, v___y_233_);
stack->m_obj
 = v_res_374_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___boxed(lean_object* v_ref_375_, lean_object* v_msgData_376_, lean_object* v_severity_377_, lean_object* v_isSilent_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
uint8_t v_severity_boxed_382_; uint8_t v_isSilent_boxed_383_; lean_object* v_res_384_; 
v_severity_boxed_382_ = lean_unbox(v_severity_377_);
v_isSilent_boxed_383_ = lean_unbox(v_isSilent_378_);
v_res_384_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6(v_ref_375_, v_msgData_376_, v_severity_boxed_382_, v_isSilent_boxed_383_, v___y_379_, v___y_380_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec(v_ref_375_);
return v_res_384_;
}
}
lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5(lean_object* v_ref_385_, lean_object* v_msgData_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
uint8_t v___x_390_; uint8_t v___x_391_; lean_object* v___x_392_; 
v___x_390_ = 1;
v___x_391_ = 0;
v___x_392_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6(v_ref_385_, v_msgData_386_, v___x_390_, v___x_391_, v___y_387_, v___y_388_);
return v___x_392_;
}
}
LEAN_EXPORT void l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_385_ = stack[0].m_obj;
lean_object* v_msgData_386_ = stack[1].m_obj;
lean_object* v___y_387_ = stack[2].m_obj;
lean_object* v___y_388_ = stack[3].m_obj;
lean_object* v_res_393_;
v_res_393_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5(v_ref_385_, v_msgData_386_, v___y_387_, v___y_388_);
stack->m_obj
 = v_res_393_;
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5___boxed(lean_object* v_ref_394_, lean_object* v_msgData_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5(v_ref_394_, v_msgData_395_, v___y_396_, v___y_397_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
lean_dec(v_ref_394_);
return v_res_399_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__1(void){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__0));
v___x_402_ = l_Lean_stringToMessageData(v___x_401_);
return v___x_402_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__3(void){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__2));
v___x_405_ = l_Lean_stringToMessageData(v___x_404_);
return v___x_405_;
}
}
lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4(lean_object* v_linterOption_406_, lean_object* v_stx_407_, lean_object* v_msg_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
lean_object* v_name_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_430_; 
v_name_412_ = lean_ctor_get(v_linterOption_406_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v_linterOption_406_);
if (v_isSharedCheck_430_ == 0)
{
lean_object* v_unused_431_; 
v_unused_431_ = lean_ctor_get(v_linterOption_406_, 1);
lean_dec(v_unused_431_);
v___x_414_ = v_linterOption_406_;
v_isShared_415_ = v_isSharedCheck_430_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_name_412_);
lean_dec(v_linterOption_406_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_430_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_419_; 
v___x_416_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__1);
lean_inc(v_name_412_);
v___x_417_ = l_Lean_MessageData_ofName(v_name_412_);
if (v_isShared_415_ == 0)
{
lean_ctor_set_tag(v___x_414_, 7);
lean_ctor_set(v___x_414_, 1, v___x_417_);
lean_ctor_set(v___x_414_, 0, v___x_416_);
v___x_419_ = v___x_414_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_416_);
lean_ctor_set(v_reuseFailAlloc_429_, 1, v___x_417_);
v___x_419_ = v_reuseFailAlloc_429_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v_disable_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_420_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__3);
v___x_421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_421_, 0, v___x_419_);
lean_ctor_set(v___x_421_, 1, v___x_420_);
v_disable_422_ = l_Lean_MessageData_note(v___x_421_);
v___x_423_ = l_Lean_Linter_linterMessageTag;
v___x_424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_424_, 0, v_msg_408_);
lean_ctor_set(v___x_424_, 1, v_disable_422_);
v___x_425_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_423_);
lean_ctor_set(v___x_425_, 1, v___x_424_);
v___x_426_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_426_, 0, v_name_412_);
lean_ctor_set(v___x_426_, 1, v___x_425_);
lean_inc(v_stx_407_);
v___x_427_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_427_, 0, v_stx_407_);
lean_ctor_set(v___x_427_, 1, v___x_426_);
v___x_428_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5(v_stx_407_, v___x_427_, v___y_409_, v___y_410_);
lean_dec(v_stx_407_);
return v___x_428_;
}
}
}
}
LEAN_EXPORT void l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_linterOption_406_ = stack[0].m_obj;
lean_object* v_stx_407_ = stack[1].m_obj;
lean_object* v_msg_408_ = stack[2].m_obj;
lean_object* v___y_409_ = stack[3].m_obj;
lean_object* v___y_410_ = stack[4].m_obj;
lean_object* v_res_432_;
v_res_432_ = l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4(v_linterOption_406_, v_stx_407_, v_msg_408_, v___y_409_, v___y_410_);
stack->m_obj
 = v_res_432_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___boxed(lean_object* v_linterOption_433_, lean_object* v_stx_434_, lean_object* v_msg_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4(v_linterOption_433_, v_stx_434_, v_msg_435_, v___y_436_, v___y_437_);
lean_dec(v___y_437_);
lean_dec_ref(v___y_436_);
return v_res_439_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__2(void){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_443_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__1));
v___x_444_ = l_Lean_MessageData_ofFormat(v___x_443_);
return v___x_444_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5(lean_object* v_as_460_, size_t v_sz_461_, size_t v_i_462_, lean_object* v_b_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
lean_object* v_a_468_; uint8_t v___x_472_; 
v___x_472_ = lean_usize_dec_lt(v_i_462_, v_sz_461_);
if (v___x_472_ == 0)
{
lean_object* v___x_473_; 
v___x_473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_473_, 0, v_b_463_);
return v___x_473_;
}
else
{
lean_object* v___x_474_; lean_object* v_patHead_476_; lean_object* v___y_477_; lean_object* v___y_478_; lean_object* v_a_482_; lean_object* v___x_483_; uint8_t v___x_484_; 
v___x_474_ = lean_box(0);
v_a_482_ = lean_array_uget_borrowed(v_as_460_, v_i_462_);
v___x_483_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__4));
lean_inc(v_a_482_);
v___x_484_ = l_Lean_Syntax_isOfKind(v_a_482_, v___x_483_);
if (v___x_484_ == 0)
{
v_a_468_ = v___x_474_;
goto v___jp_467_;
}
else
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; uint8_t v___x_488_; 
v___x_485_ = lean_unsigned_to_nat(1u);
v___x_486_ = l_Lean_Syntax_getArg(v_a_482_, v___x_485_);
v___x_487_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__6));
lean_inc(v___x_486_);
v___x_488_ = l_Lean_Syntax_isOfKind(v___x_486_, v___x_487_);
if (v___x_488_ == 0)
{
if (v___x_488_ == 0)
{
lean_object* v___x_489_; uint8_t v___x_490_; 
v___x_489_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__8));
lean_inc(v___x_486_);
v___x_490_ = l_Lean_Syntax_isOfKind(v___x_486_, v___x_489_);
if (v___x_490_ == 0)
{
lean_dec(v___x_486_);
v_a_468_ = v___x_474_;
goto v___jp_467_;
}
else
{
v_patHead_476_ = v___x_486_;
v___y_477_ = v___y_464_;
v___y_478_ = v___y_465_;
goto v___jp_475_;
}
}
else
{
v_patHead_476_ = v___x_486_;
v___y_477_ = v___y_464_;
v___y_478_ = v___y_465_;
goto v___jp_475_;
}
}
else
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; uint8_t v___x_494_; 
v___x_491_ = lean_unsigned_to_nat(0u);
v___x_492_ = l_Lean_Syntax_getArg(v___x_486_, v___x_491_);
lean_dec(v___x_486_);
v___x_493_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__8));
lean_inc(v___x_492_);
v___x_494_ = l_Lean_Syntax_isOfKind(v___x_492_, v___x_493_);
if (v___x_494_ == 0)
{
lean_dec(v___x_492_);
v_a_468_ = v___x_474_;
goto v___jp_467_;
}
else
{
v_patHead_476_ = v___x_492_;
v___y_477_ = v___y_464_;
v___y_478_ = v___y_465_;
goto v___jp_475_;
}
}
}
v___jp_475_:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_479_ = l_Lean_Linter_linter_suspiciousUnexpanderPatterns;
v___x_480_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__2);
v___x_481_ = l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4(v___x_479_, v_patHead_476_, v___x_480_, v___y_477_, v___y_478_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_dec_ref_known(v___x_481_, 1);
v_a_468_ = v___x_474_;
goto v___jp_467_;
}
else
{
return v___x_481_;
}
}
}
v___jp_467_:
{
size_t v___x_469_; size_t v___x_470_; 
v___x_469_ = ((size_t)1ULL);
v___x_470_ = lean_usize_add(v_i_462_, v___x_469_);
v_i_462_ = v___x_470_;
v_b_463_ = v_a_468_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_460_ = stack[0].m_obj;
size_t v_sz_461_ = stack[1].m_num;
size_t v_i_462_ = stack[2].m_num;
lean_object* v_b_463_ = stack[3].m_obj;
lean_object* v___y_464_ = stack[4].m_obj;
lean_object* v___y_465_ = stack[5].m_obj;
lean_object* v_res_495_;
v_res_495_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5(v_as_460_, v_sz_461_, v_i_462_, v_b_463_, v___y_464_, v___y_465_);
stack->m_obj
 = v_res_495_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___boxed(lean_object* v_as_496_, lean_object* v_sz_497_, lean_object* v_i_498_, lean_object* v_b_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
size_t v_sz_boxed_503_; size_t v_i_boxed_504_; lean_object* v_res_505_; 
v_sz_boxed_503_ = lean_unbox_usize(v_sz_497_);
lean_dec(v_sz_497_);
v_i_boxed_504_ = lean_unbox_usize(v_i_498_);
lean_dec(v_i_498_);
v_res_505_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5(v_as_496_, v_sz_boxed_503_, v_i_boxed_504_, v_b_499_, v___y_500_, v___y_501_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec_ref(v_as_496_);
return v_res_505_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2(size_t v_sz_512_, size_t v_i_513_, lean_object* v_bs_514_){
_start:
{
uint8_t v___x_515_; 
v___x_515_ = lean_usize_dec_lt(v_i_513_, v_sz_512_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; 
v___x_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_516_, 0, v_bs_514_);
return v___x_516_;
}
else
{
lean_object* v_v_517_; lean_object* v___x_518_; uint8_t v___x_519_; 
v_v_517_ = lean_array_uget_borrowed(v_bs_514_, v_i_513_);
v___x_518_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__1));
lean_inc(v_v_517_);
v___x_519_ = l_Lean_Syntax_isOfKind(v_v_517_, v___x_518_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; 
lean_dec_ref(v_bs_514_);
v___x_520_ = lean_box(0);
return v___x_520_;
}
else
{
lean_object* v___x_521_; lean_object* v___x_522_; uint8_t v___x_523_; 
v___x_521_ = lean_unsigned_to_nat(1u);
v___x_522_ = l_Lean_Syntax_getArg(v_v_517_, v___x_521_);
lean_inc(v___x_522_);
v___x_523_ = l_Lean_Syntax_matchesNull(v___x_522_, v___x_521_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; 
lean_dec(v___x_522_);
lean_dec_ref(v_bs_514_);
v___x_524_ = lean_box(0);
return v___x_524_;
}
else
{
lean_object* v___x_525_; lean_object* v___x_526_; uint8_t v___x_527_; 
v___x_525_ = lean_unsigned_to_nat(0u);
v___x_526_ = l_Lean_Syntax_getArg(v___x_522_, v___x_525_);
lean_dec(v___x_522_);
lean_inc(v___x_526_);
v___x_527_ = l_Lean_Syntax_matchesNull(v___x_526_, v___x_521_);
if (v___x_527_ == 0)
{
lean_object* v___x_528_; 
lean_dec(v___x_526_);
lean_dec_ref(v_bs_514_);
v___x_528_ = lean_box(0);
return v___x_528_;
}
else
{
lean_object* v_bs_x27_529_; lean_object* v___x_530_; size_t v___x_531_; size_t v___x_532_; lean_object* v___x_533_; 
v_bs_x27_529_ = lean_array_uset(v_bs_514_, v_i_513_, v___x_525_);
v___x_530_ = l_Lean_Syntax_getArg(v___x_526_, v___x_525_);
lean_dec(v___x_526_);
v___x_531_ = ((size_t)1ULL);
v___x_532_ = lean_usize_add(v_i_513_, v___x_531_);
v___x_533_ = lean_array_uset(v_bs_x27_529_, v_i_513_, v___x_530_);
v_i_513_ = v___x_532_;
v_bs_514_ = v___x_533_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_512_ = stack[0].m_num;
size_t v_i_513_ = stack[1].m_num;
lean_object* v_bs_514_ = stack[2].m_obj;
lean_object* v_res_535_;
v_res_535_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2(v_sz_512_, v_i_513_, v_bs_514_);
stack->m_obj
 = v_res_535_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___boxed(lean_object* v_sz_536_, lean_object* v_i_537_, lean_object* v_bs_538_){
_start:
{
size_t v_sz_boxed_539_; size_t v_i_boxed_540_; lean_object* v_res_541_; 
v_sz_boxed_539_ = lean_unbox_usize(v_sz_536_);
lean_dec(v_sz_536_);
v_i_boxed_540_ = lean_unbox_usize(v_i_537_);
lean_dec(v_i_537_);
v_res_541_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2(v_sz_boxed_539_, v_i_boxed_540_, v_bs_538_);
return v_res_541_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__6(uint8_t v___x_542_, lean_object* v_as_543_, size_t v_i_544_, size_t v_stop_545_, lean_object* v_b_546_){
_start:
{
lean_object* v___y_548_; uint8_t v___x_552_; 
v___x_552_ = lean_usize_dec_eq(v_i_544_, v_stop_545_);
if (v___x_552_ == 0)
{
lean_object* v_fst_553_; uint8_t v___x_554_; 
v_fst_553_ = lean_ctor_get(v_b_546_, 0);
v___x_554_ = lean_unbox(v_fst_553_);
if (v___x_554_ == 0)
{
lean_object* v_snd_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_563_; 
v_snd_555_ = lean_ctor_get(v_b_546_, 1);
v_isSharedCheck_563_ = !lean_is_exclusive(v_b_546_);
if (v_isSharedCheck_563_ == 0)
{
lean_object* v_unused_564_; 
v_unused_564_ = lean_ctor_get(v_b_546_, 0);
lean_dec(v_unused_564_);
v___x_557_ = v_b_546_;
v_isShared_558_ = v_isSharedCheck_563_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_snd_555_);
lean_dec(v_b_546_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_563_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_559_; lean_object* v___x_561_; 
v___x_559_ = lean_box(v___x_542_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v___x_559_);
v___x_561_ = v___x_557_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_559_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v_snd_555_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
v___y_548_ = v___x_561_;
goto v___jp_547_;
}
}
}
else
{
lean_object* v_snd_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_575_; 
v_snd_565_ = lean_ctor_get(v_b_546_, 1);
v_isSharedCheck_575_ = !lean_is_exclusive(v_b_546_);
if (v_isSharedCheck_575_ == 0)
{
lean_object* v_unused_576_; 
v_unused_576_ = lean_ctor_get(v_b_546_, 0);
lean_dec(v_unused_576_);
v___x_567_ = v_b_546_;
v_isShared_568_ = v_isSharedCheck_575_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_snd_565_);
lean_dec(v_b_546_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_575_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_573_; 
v___x_569_ = lean_array_uget_borrowed(v_as_543_, v_i_544_);
lean_inc(v___x_569_);
v___x_570_ = lean_array_push(v_snd_565_, v___x_569_);
v___x_571_ = lean_box(v___x_552_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 1, v___x_570_);
lean_ctor_set(v___x_567_, 0, v___x_571_);
v___x_573_ = v___x_567_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_571_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v___x_570_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
v___y_548_ = v___x_573_;
goto v___jp_547_;
}
}
}
}
else
{
return v_b_546_;
}
v___jp_547_:
{
size_t v___x_549_; size_t v___x_550_; 
v___x_549_ = ((size_t)1ULL);
v___x_550_ = lean_usize_add(v_i_544_, v___x_549_);
v_i_544_ = v___x_550_;
v_b_546_ = v___y_548_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__6_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_542_ = stack[0].m_num;
lean_object* v_as_543_ = stack[1].m_obj;
size_t v_i_544_ = stack[2].m_num;
size_t v_stop_545_ = stack[3].m_num;
lean_object* v_b_546_ = stack[4].m_obj;
lean_object* v_res_577_;
v_res_577_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__6(v___x_542_, v_as_543_, v_i_544_, v_stop_545_, v_b_546_);
stack->m_obj
 = v_res_577_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__6___boxed(lean_object* v___x_578_, lean_object* v_as_579_, lean_object* v_i_580_, lean_object* v_stop_581_, lean_object* v_b_582_){
_start:
{
uint8_t v___x_11126__boxed_583_; size_t v_i_boxed_584_; size_t v_stop_boxed_585_; lean_object* v_res_586_; 
v___x_11126__boxed_583_ = lean_unbox(v___x_578_);
v_i_boxed_584_ = lean_unbox_usize(v_i_580_);
lean_dec(v_i_580_);
v_stop_boxed_585_ = lean_unbox_usize(v_stop_581_);
lean_dec(v_stop_581_);
v_res_586_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__6(v___x_11126__boxed_583_, v_as_579_, v_i_boxed_584_, v_stop_boxed_585_, v_b_582_);
lean_dec_ref(v_as_579_);
return v_res_586_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3(uint8_t v___x_597_, lean_object* v_as_598_, size_t v_i_599_, size_t v_stop_600_){
_start:
{
uint8_t v___x_601_; 
v___x_601_ = lean_usize_dec_eq(v_i_599_, v_stop_600_);
if (v___x_601_ == 0)
{
uint8_t v___x_602_; uint8_t v___y_604_; lean_object* v___x_608_; lean_object* v___x_609_; uint8_t v___x_610_; 
v___x_602_ = 1;
v___x_608_ = lean_array_uget_borrowed(v_as_598_, v_i_599_);
v___x_609_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__2));
lean_inc(v___x_608_);
v___x_610_ = l_Lean_Syntax_isOfKind(v___x_608_, v___x_609_);
if (v___x_610_ == 0)
{
v___y_604_ = v___x_610_;
goto v___jp_603_;
}
else
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_611_ = lean_unsigned_to_nat(0u);
v___x_612_ = l_Lean_Syntax_getArg(v___x_608_, v___x_611_);
v___x_613_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__4));
v___x_614_ = l_Lean_Syntax_matchesIdent(v___x_612_, v___x_613_);
lean_dec(v___x_612_);
if (v___x_614_ == 0)
{
v___y_604_ = v___x_614_;
goto v___jp_603_;
}
else
{
lean_object* v___x_615_; lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_615_ = lean_unsigned_to_nat(1u);
v___x_616_ = l_Lean_Syntax_getArg(v___x_608_, v___x_615_);
v___x_617_ = l_Lean_Syntax_matchesNull(v___x_616_, v___x_615_);
if (v___x_617_ == 0)
{
v___y_604_ = v___x_617_;
goto v___jp_603_;
}
else
{
v___y_604_ = v___x_597_;
goto v___jp_603_;
}
}
}
v___jp_603_:
{
if (v___y_604_ == 0)
{
size_t v___x_605_; size_t v___x_606_; 
v___x_605_ = ((size_t)1ULL);
v___x_606_ = lean_usize_add(v_i_599_, v___x_605_);
v_i_599_ = v___x_606_;
goto _start;
}
else
{
return v___x_602_;
}
}
}
else
{
uint8_t v___x_618_; 
v___x_618_ = 0;
return v___x_618_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_597_ = stack[0].m_num;
lean_object* v_as_598_ = stack[1].m_obj;
size_t v_i_599_ = stack[2].m_num;
size_t v_stop_600_ = stack[3].m_num;
uint8_t v_res_619_;
v_res_619_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3(v___x_597_, v_as_598_, v_i_599_, v_stop_600_);
stack->m_num = v_res_619_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___boxed(lean_object* v___x_620_, lean_object* v_as_621_, lean_object* v_i_622_, lean_object* v_stop_623_){
_start:
{
uint8_t v___x_11243__boxed_624_; size_t v_i_boxed_625_; size_t v_stop_boxed_626_; uint8_t v_res_627_; lean_object* v_r_628_; 
v___x_11243__boxed_624_ = lean_unbox(v___x_620_);
v_i_boxed_625_ = lean_unbox_usize(v_i_622_);
lean_dec(v_i_622_);
v_stop_boxed_626_ = lean_unbox_usize(v_stop_623_);
lean_dec(v_stop_623_);
v_res_627_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3(v___x_11243__boxed_624_, v_as_621_, v_i_boxed_625_, v_stop_boxed_626_);
lean_dec_ref(v_as_621_);
v_r_628_ = lean_box(v_res_627_);
return v_r_628_;
}
}
lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0(lean_object* v_cmdStx_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
lean_object* v___x_691_; lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_906_; 
v___x_691_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0(v___y_685_, v___y_686_);
v_a_692_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_906_ == 0)
{
v___x_694_ = v___x_691_;
v_isShared_695_ = v_isSharedCheck_906_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_dec(v___x_691_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_906_;
goto v_resetjp_693_;
}
v___jp_688_:
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = lean_box(0);
v___x_690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
return v___x_690_;
}
v_resetjp_693_:
{
uint8_t v___x_696_; 
v___x_696_ = l_Lean_Linter_getLinterSuspiciousUnexpanderPatterns(v_a_692_);
lean_dec(v_a_692_);
if (v___x_696_ == 0)
{
lean_object* v___x_697_; lean_object* v___x_699_; 
lean_dec(v_cmdStx_684_);
v___x_697_ = lean_box(0);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v___x_697_);
v___x_699_ = v___x_694_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_697_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
else
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; uint8_t v___x_704_; 
v___x_701_ = ((lean_object*)(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_));
v___x_702_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0));
v___x_703_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__2));
lean_inc(v_cmdStx_684_);
v___x_704_ = l_Lean_Syntax_isOfKind(v_cmdStx_684_, v___x_703_);
if (v___x_704_ == 0)
{
lean_object* v___x_705_; lean_object* v___x_707_; 
lean_dec(v_cmdStx_684_);
v___x_705_ = lean_box(0);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v___x_705_);
v___x_707_ = v___x_694_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v___x_705_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
else
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; uint8_t v___x_712_; lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v___y_717_; lean_object* v___y_718_; lean_object* v___y_869_; lean_object* v___y_870_; 
v___x_709_ = lean_unsigned_to_nat(0u);
v___x_710_ = l_Lean_Syntax_getArg(v_cmdStx_684_, v___x_709_);
v___x_711_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__4));
lean_inc(v___x_710_);
v___x_712_ = l_Lean_Syntax_isOfKind(v___x_710_, v___x_711_);
if (v___x_712_ == 0)
{
lean_object* v___x_893_; lean_object* v___x_894_; 
lean_dec(v___x_710_);
lean_del_object(v___x_694_);
lean_dec(v_cmdStx_684_);
v___x_893_ = lean_box(0);
v___x_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_894_, 0, v___x_893_);
return v___x_894_;
}
else
{
lean_object* v___x_895_; uint8_t v___x_896_; 
v___x_895_ = l_Lean_Syntax_getArg(v___x_710_, v___x_709_);
v___x_896_ = l_Lean_Syntax_isNone(v___x_895_);
if (v___x_896_ == 0)
{
lean_object* v___x_897_; uint8_t v___x_898_; 
v___x_897_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_895_);
v___x_898_ = l_Lean_Syntax_matchesNull(v___x_895_, v___x_897_);
if (v___x_898_ == 0)
{
lean_object* v___x_899_; lean_object* v___x_900_; 
lean_dec(v___x_895_);
lean_dec(v___x_710_);
lean_del_object(v___x_694_);
lean_dec(v_cmdStx_684_);
v___x_899_ = lean_box(0);
v___x_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
return v___x_900_;
}
else
{
if (v___x_896_ == 0)
{
lean_object* v___x_901_; lean_object* v___x_902_; uint8_t v___x_903_; 
v___x_901_ = l_Lean_Syntax_getArg(v___x_895_, v___x_709_);
lean_dec(v___x_895_);
v___x_902_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__21));
v___x_903_ = l_Lean_Syntax_isOfKind(v___x_901_, v___x_902_);
if (v___x_903_ == 0)
{
lean_object* v___x_904_; lean_object* v___x_905_; 
lean_dec(v___x_710_);
lean_del_object(v___x_694_);
lean_dec(v_cmdStx_684_);
v___x_904_ = lean_box(0);
v___x_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
return v___x_905_;
}
else
{
v___y_869_ = v___y_685_;
v___y_870_ = v___y_686_;
goto v___jp_868_;
}
}
else
{
lean_dec(v___x_895_);
v___y_869_ = v___y_685_;
v___y_870_ = v___y_686_;
goto v___jp_868_;
}
}
}
else
{
lean_dec(v___x_895_);
v___y_869_ = v___y_685_;
v___y_870_ = v___y_686_;
goto v___jp_868_;
}
}
v___jp_713_:
{
size_t v_sz_719_; size_t v___x_720_; lean_object* v___x_721_; 
v_sz_719_ = lean_array_size(v___y_718_);
v___x_720_ = ((size_t)0ULL);
v___x_721_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1(v_sz_719_, v___x_720_, v___y_718_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v___x_722_; lean_object* v___x_724_; 
lean_dec(v___x_710_);
lean_dec(v_cmdStx_684_);
v___x_722_ = lean_box(0);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v___x_722_);
v___x_724_ = v___x_694_;
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
lean_object* v_val_726_; lean_object* v___x_727_; lean_object* v___x_728_; uint8_t v___x_729_; 
v_val_726_ = lean_ctor_get(v___x_721_, 0);
lean_inc(v_val_726_);
lean_dec_ref_known(v___x_721_, 1);
v___x_727_ = lean_unsigned_to_nat(3u);
v___x_728_ = l_Lean_Syntax_getArg(v___x_710_, v___x_727_);
v___x_729_ = l_Lean_Syntax_matchesNull(v___x_728_, v___x_709_);
if (v___x_729_ == 0)
{
lean_object* v___x_730_; lean_object* v___x_732_; 
lean_dec(v_val_726_);
lean_dec(v___x_710_);
lean_dec(v_cmdStx_684_);
v___x_730_ = lean_box(0);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v___x_730_);
v___x_732_ = v___x_694_;
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
lean_object* v___x_734_; lean_object* v___x_735_; uint8_t v___x_736_; 
v___x_734_ = lean_unsigned_to_nat(4u);
v___x_735_ = l_Lean_Syntax_getArg(v___x_710_, v___x_734_);
v___x_736_ = l_Lean_Syntax_matchesNull(v___x_735_, v___x_709_);
if (v___x_736_ == 0)
{
lean_object* v___x_737_; lean_object* v___x_739_; 
lean_dec(v_val_726_);
lean_dec(v___x_710_);
lean_dec(v_cmdStx_684_);
v___x_737_ = lean_box(0);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v___x_737_);
v___x_739_ = v___x_694_;
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
lean_object* v___x_741_; lean_object* v___x_742_; uint8_t v___x_743_; 
v___x_741_ = lean_unsigned_to_nat(5u);
v___x_742_ = l_Lean_Syntax_getArg(v___x_710_, v___x_741_);
v___x_743_ = l_Lean_Syntax_matchesNull(v___x_742_, v___x_709_);
if (v___x_743_ == 0)
{
lean_object* v___x_744_; lean_object* v___x_746_; 
lean_dec(v_val_726_);
lean_dec(v___x_710_);
lean_dec(v_cmdStx_684_);
v___x_744_ = lean_box(0);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v___x_744_);
v___x_746_ = v___x_694_;
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
lean_object* v___x_748_; lean_object* v___x_749_; uint8_t v___x_750_; 
v___x_748_ = lean_unsigned_to_nat(6u);
v___x_749_ = l_Lean_Syntax_getArg(v___x_710_, v___x_748_);
lean_dec(v___x_710_);
v___x_750_ = l_Lean_Syntax_matchesNull(v___x_749_, v___x_709_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; lean_object* v___x_753_; 
lean_dec(v_val_726_);
lean_dec(v_cmdStx_684_);
v___x_751_ = lean_box(0);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v___x_751_);
v___x_753_ = v___x_694_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_751_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
else
{
lean_object* v___x_755_; lean_object* v___x_756_; uint8_t v___x_757_; 
v___x_755_ = l_Lean_Syntax_getArg(v_cmdStx_684_, v___y_715_);
lean_dec(v_cmdStx_684_);
v___x_756_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__6));
lean_inc(v___x_755_);
v___x_757_ = l_Lean_Syntax_isOfKind(v___x_755_, v___x_756_);
if (v___x_757_ == 0)
{
lean_object* v___x_758_; lean_object* v___x_760_; 
lean_dec(v___x_755_);
lean_dec(v_val_726_);
v___x_758_ = lean_box(0);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v___x_758_);
v___x_760_ = v___x_694_;
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
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; uint8_t v___x_765_; 
v___x_762_ = lean_unsigned_to_nat(2u);
v___x_763_ = l_Lean_Syntax_getArg(v___x_755_, v___x_762_);
v___x_764_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__8));
lean_inc(v___x_763_);
v___x_765_ = l_Lean_Syntax_isOfKind(v___x_763_, v___x_764_);
if (v___x_765_ == 0)
{
lean_object* v___x_766_; lean_object* v___x_768_; 
lean_dec(v___x_763_);
lean_dec(v___x_755_);
lean_dec(v_val_726_);
v___x_766_ = lean_box(0);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v___x_766_);
v___x_768_ = v___x_694_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_766_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
else
{
lean_object* v___x_770_; uint8_t v___x_771_; 
v___x_770_ = l_Lean_Syntax_getArg(v___x_763_, v___x_709_);
v___x_771_ = l_Lean_Syntax_matchesNull(v___x_770_, v___x_709_);
if (v___x_771_ == 0)
{
lean_object* v___x_772_; lean_object* v___x_774_; 
lean_dec(v___x_763_);
lean_dec(v___x_755_);
lean_dec(v_val_726_);
v___x_772_ = lean_box(0);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v___x_772_);
v___x_774_ = v___x_694_;
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
lean_object* v___x_776_; uint8_t v___x_777_; 
v___x_776_ = l_Lean_Syntax_getArg(v___x_763_, v___y_715_);
lean_dec(v___x_763_);
lean_inc(v___x_776_);
v___x_777_ = l_Lean_Syntax_matchesNull(v___x_776_, v___y_715_);
if (v___x_777_ == 0)
{
lean_object* v___x_778_; lean_object* v___x_780_; 
lean_dec(v___x_776_);
lean_dec(v___x_755_);
lean_dec(v_val_726_);
v___x_778_ = lean_box(0);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v___x_778_);
v___x_780_ = v___x_694_;
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
v___x_782_ = l_Lean_Syntax_getArg(v___x_776_, v___x_709_);
lean_dec(v___x_776_);
v___x_783_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__9));
lean_inc_ref(v___y_716_);
v___x_784_ = l_Lean_Name_mkStr4(v___x_701_, v___x_702_, v___y_716_, v___x_783_);
v___x_785_ = l_Lean_Syntax_isOfKind(v___x_782_, v___x_784_);
lean_dec(v___x_784_);
if (v___x_785_ == 0)
{
lean_object* v___x_786_; lean_object* v___x_788_; 
lean_dec(v___x_755_);
lean_dec(v_val_726_);
v___x_786_ = lean_box(0);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v___x_786_);
v___x_788_ = v___x_694_;
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
lean_object* v___x_790_; lean_object* v___x_791_; uint8_t v___x_792_; 
v___x_790_ = l_Lean_Syntax_getArg(v___x_755_, v___x_727_);
v___x_791_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__11));
lean_inc(v___x_790_);
v___x_792_ = l_Lean_Syntax_isOfKind(v___x_790_, v___x_791_);
if (v___x_792_ == 0)
{
lean_object* v___x_793_; lean_object* v___x_795_; 
lean_dec(v___x_790_);
lean_dec(v___x_755_);
lean_dec(v_val_726_);
v___x_793_ = lean_box(0);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v___x_793_);
v___x_795_ = v___x_694_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_793_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
else
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; uint8_t v___x_800_; 
v___x_797_ = l_Lean_Syntax_getArg(v___x_790_, v___x_709_);
lean_dec(v___x_790_);
v___x_798_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__12));
lean_inc_ref(v___y_716_);
v___x_799_ = l_Lean_Name_mkStr4(v___x_701_, v___x_702_, v___y_716_, v___x_798_);
lean_inc(v___x_797_);
v___x_800_ = l_Lean_Syntax_isOfKind(v___x_797_, v___x_799_);
lean_dec(v___x_799_);
if (v___x_800_ == 0)
{
lean_object* v___x_801_; lean_object* v___x_803_; 
lean_dec(v___x_797_);
lean_dec(v___x_755_);
lean_dec(v_val_726_);
v___x_801_ = lean_box(0);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v___x_801_);
v___x_803_ = v___x_694_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_801_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
else
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; uint8_t v___x_808_; 
v___x_805_ = l_Lean_Syntax_getArg(v___x_797_, v___x_709_);
v___x_806_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__13));
lean_inc_ref(v___y_716_);
v___x_807_ = l_Lean_Name_mkStr4(v___x_701_, v___x_702_, v___y_716_, v___x_806_);
lean_inc(v___x_805_);
v___x_808_ = l_Lean_Syntax_isOfKind(v___x_805_, v___x_807_);
lean_dec(v___x_807_);
if (v___x_808_ == 0)
{
lean_object* v___x_809_; lean_object* v___x_811_; 
lean_dec(v___x_805_);
lean_dec(v___x_797_);
lean_dec(v___x_755_);
lean_dec(v_val_726_);
v___x_809_ = lean_box(0);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v___x_809_);
v___x_811_ = v___x_694_;
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
lean_object* v___x_813_; lean_object* v___x_814_; size_t v_sz_815_; lean_object* v___x_816_; 
v___x_813_ = l_Lean_Syntax_getArg(v___x_805_, v___x_709_);
lean_dec(v___x_805_);
v___x_814_ = l_Lean_Syntax_getArgs(v___x_813_);
lean_dec(v___x_813_);
v_sz_815_ = lean_array_size(v___x_814_);
v___x_816_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2(v_sz_815_, v___x_720_, v___x_814_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v___x_817_; lean_object* v___x_819_; 
lean_dec(v___x_797_);
lean_dec(v___x_755_);
lean_dec(v_val_726_);
v___x_817_ = lean_box(0);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v___x_817_);
v___x_819_ = v___x_694_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_817_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
else
{
lean_object* v_val_821_; lean_object* v___x_822_; lean_object* v___x_823_; uint8_t v___x_824_; 
v_val_821_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_val_821_);
lean_dec_ref_known(v___x_816_, 1);
v___x_822_ = l_Lean_Syntax_getArg(v___x_797_, v___y_715_);
v___x_823_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__16));
lean_inc(v___x_822_);
v___x_824_ = l_Lean_Syntax_isOfKind(v___x_822_, v___x_823_);
if (v___x_824_ == 0)
{
lean_object* v___x_825_; lean_object* v___x_827_; 
lean_dec(v___x_822_);
lean_dec(v_val_821_);
lean_dec(v___x_797_);
lean_dec(v___x_755_);
lean_dec(v_val_726_);
v___x_825_ = lean_box(0);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v___x_825_);
v___x_827_ = v___x_694_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v___x_825_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
else
{
lean_object* v___x_829_; uint8_t v___x_830_; 
v___x_829_ = l_Lean_Syntax_getArg(v___x_822_, v___x_709_);
v___x_830_ = l_Lean_Syntax_matchesNull(v___x_829_, v___x_709_);
if (v___x_830_ == 0)
{
lean_object* v___x_831_; lean_object* v___x_833_; 
lean_dec(v___x_822_);
lean_dec(v_val_821_);
lean_dec(v___x_797_);
lean_dec(v___x_755_);
lean_dec(v_val_726_);
v___x_831_ = lean_box(0);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v___x_831_);
v___x_833_ = v___x_694_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v___x_831_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
else
{
lean_object* v___x_835_; uint8_t v___x_836_; 
v___x_835_ = l_Lean_Syntax_getArg(v___x_822_, v___y_715_);
lean_dec(v___x_822_);
v___x_836_ = l_Lean_Syntax_matchesNull(v___x_835_, v___x_709_);
if (v___x_836_ == 0)
{
lean_object* v___x_837_; lean_object* v___x_839_; 
lean_dec(v_val_821_);
lean_dec(v___x_797_);
lean_dec(v___x_755_);
lean_dec(v_val_726_);
v___x_837_ = lean_box(0);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v___x_837_);
v___x_839_ = v___x_694_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_837_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
else
{
lean_object* v___x_841_; uint8_t v___x_842_; 
v___x_841_ = l_Lean_Syntax_getArg(v___x_797_, v___x_762_);
lean_dec(v___x_797_);
v___x_842_ = l_Lean_Syntax_matchesNull(v___x_841_, v___x_709_);
if (v___x_842_ == 0)
{
lean_object* v___x_843_; lean_object* v___x_845_; 
lean_dec(v_val_821_);
lean_dec(v___x_755_);
lean_dec(v_val_726_);
v___x_843_ = lean_box(0);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v___x_843_);
v___x_845_ = v___x_694_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_843_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
else
{
lean_object* v___x_847_; uint8_t v___x_848_; 
v___x_847_ = l_Lean_Syntax_getArg(v___x_755_, v___x_734_);
lean_dec(v___x_755_);
v___x_848_ = l_Lean_Syntax_matchesNull(v___x_847_, v___x_709_);
if (v___x_848_ == 0)
{
lean_object* v___x_849_; lean_object* v___x_851_; 
lean_dec(v_val_821_);
lean_dec(v_val_726_);
v___x_849_ = lean_box(0);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v___x_849_);
v___x_851_ = v___x_694_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_849_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
else
{
lean_object* v___x_853_; uint8_t v___x_854_; 
lean_del_object(v___x_694_);
v___x_853_ = lean_array_get_size(v_val_726_);
v___x_854_ = lean_nat_dec_lt(v___x_709_, v___x_853_);
if (v___x_854_ == 0)
{
lean_dec(v_val_821_);
lean_dec(v_val_726_);
goto v___jp_688_;
}
else
{
if (v___x_854_ == 0)
{
lean_dec(v_val_821_);
lean_dec(v_val_726_);
goto v___jp_688_;
}
else
{
size_t v___x_855_; uint8_t v___x_856_; 
v___x_855_ = lean_usize_of_nat(v___x_853_);
v___x_856_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3(v___x_712_, v_val_726_, v___x_720_, v___x_855_);
lean_dec(v_val_726_);
if (v___x_856_ == 0)
{
lean_dec(v_val_821_);
goto v___jp_688_;
}
else
{
lean_object* v___x_857_; size_t v_sz_858_; lean_object* v___x_859_; 
v___x_857_ = lean_box(0);
v_sz_858_ = lean_array_size(v_val_821_);
v___x_859_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5(v_val_821_, v_sz_858_, v___x_720_, v___x_857_, v___y_714_, v___y_717_);
lean_dec(v_val_821_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_866_; 
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_866_ == 0)
{
lean_object* v_unused_867_; 
v_unused_867_ = lean_ctor_get(v___x_859_, 0);
lean_dec(v_unused_867_);
v___x_861_ = v___x_859_;
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
else
{
lean_dec(v___x_859_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_864_; 
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 0, v___x_857_);
v___x_864_ = v___x_861_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_857_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
else
{
return v___x_859_;
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
v___jp_868_:
{
lean_object* v___x_871_; lean_object* v___x_872_; uint8_t v___x_873_; 
v___x_871_ = lean_unsigned_to_nat(1u);
v___x_872_ = l_Lean_Syntax_getArg(v___x_710_, v___x_871_);
lean_inc(v___x_872_);
v___x_873_ = l_Lean_Syntax_matchesNull(v___x_872_, v___x_871_);
if (v___x_873_ == 0)
{
lean_object* v___x_874_; lean_object* v___x_875_; 
lean_dec(v___x_872_);
lean_dec(v___x_710_);
lean_del_object(v___x_694_);
lean_dec(v_cmdStx_684_);
v___x_874_ = lean_box(0);
v___x_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_875_, 0, v___x_874_);
return v___x_875_;
}
else
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; uint8_t v___x_879_; 
v___x_876_ = l_Lean_Syntax_getArg(v___x_872_, v___x_709_);
lean_dec(v___x_872_);
v___x_877_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__1));
v___x_878_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__18));
lean_inc(v___x_876_);
v___x_879_ = l_Lean_Syntax_isOfKind(v___x_876_, v___x_878_);
if (v___x_879_ == 0)
{
lean_object* v___x_880_; lean_object* v___x_881_; 
lean_dec(v___x_876_);
lean_dec(v___x_710_);
lean_del_object(v___x_694_);
lean_dec(v_cmdStx_684_);
v___x_880_ = lean_box(0);
v___x_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_881_, 0, v___x_880_);
return v___x_881_;
}
else
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; uint8_t v___x_886_; 
v___x_882_ = l_Lean_Syntax_getArg(v___x_876_, v___x_871_);
lean_dec(v___x_876_);
v___x_883_ = l_Lean_Syntax_getArgs(v___x_882_);
lean_dec(v___x_882_);
v___x_884_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__19));
v___x_885_ = lean_array_get_size(v___x_883_);
v___x_886_ = lean_nat_dec_lt(v___x_709_, v___x_885_);
if (v___x_886_ == 0)
{
lean_dec_ref(v___x_883_);
v___y_714_ = v___y_869_;
v___y_715_ = v___x_871_;
v___y_716_ = v___x_877_;
v___y_717_ = v___y_870_;
v___y_718_ = v___x_884_;
goto v___jp_713_;
}
else
{
lean_object* v___x_887_; lean_object* v___x_888_; size_t v___x_889_; size_t v___x_890_; lean_object* v___x_891_; lean_object* v_snd_892_; 
v___x_887_ = lean_box(v___x_886_);
v___x_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
lean_ctor_set(v___x_888_, 1, v___x_884_);
v___x_889_ = ((size_t)0ULL);
v___x_890_ = lean_usize_of_nat(v___x_885_);
v___x_891_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__6(v___x_879_, v___x_883_, v___x_889_, v___x_890_, v___x_888_);
lean_dec_ref(v___x_883_);
v_snd_892_ = lean_ctor_get(v___x_891_, 1);
lean_inc(v_snd_892_);
lean_dec_ref(v___x_891_);
v___y_714_ = v___y_869_;
v___y_715_ = v___x_871_;
v___y_716_ = v___x_877_;
v___y_717_ = v___y_870_;
v___y_718_ = v_snd_892_;
goto v___jp_713_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmdStx_684_ = stack[0].m_obj;
lean_object* v___y_685_ = stack[1].m_obj;
lean_object* v___y_686_ = stack[2].m_obj;
lean_object* v_res_907_;
v_res_907_ = l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0(v_cmdStx_684_, v___y_685_, v___y_686_);
stack->m_obj
 = v_res_907_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___boxed(lean_object* v_cmdStx_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0(v_cmdStx_908_, v___y_909_, v___y_910_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
return v_res_912_;
}
}
lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0(lean_object* v_o_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v___x_926_; 
v___x_926_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0___redArg(v_o_922_, v___y_924_);
return v___x_926_;
}
}
LEAN_EXPORT void l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_922_ = stack[0].m_obj;
lean_object* v___y_923_ = stack[1].m_obj;
lean_object* v___y_924_ = stack[2].m_obj;
lean_object* v_res_927_;
v_res_927_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0(v_o_922_, v___y_923_, v___y_924_);
stack->m_obj
 = v_res_927_;
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0___boxed(lean_object* v_o_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0(v_o_928_, v___y_929_, v___y_930_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
return v_res_932_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9(lean_object* v_msgData_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg(v_msgData_933_, v___y_935_);
return v___x_937_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_933_ = stack[0].m_obj;
lean_object* v___y_934_ = stack[1].m_obj;
lean_object* v___y_935_ = stack[2].m_obj;
lean_object* v_res_938_;
v_res_938_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9(v_msgData_933_, v___y_934_, v___y_935_);
stack->m_obj
 = v_res_938_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___boxed(lean_object* v_msgData_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9(v_msgData_939_, v___y_940_, v___y_941_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
return v_res_943_;
}
}
lean_object* l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1774244096____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns));
v___x_946_ = l_Lean_Elab_Command_addLinter(v___x_945_);
return v___x_946_;
}
}
LEAN_EXPORT void l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1774244096____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_947_;
v_res_947_ = l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1774244096____hygCtx___hyg_2_();
stack->m_obj
 = v_res_947_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1774244096____hygCtx___hyg_2____boxed(lean_object* v_a_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1774244096____hygCtx___hyg_2_();
return v_res_949_;
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
