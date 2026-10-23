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
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_165_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_166_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1);
v___x_167_ = lean_unsigned_to_nat(0u);
v___x_168_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
lean_ctor_set(v___x_168_, 1, v___x_167_);
lean_ctor_set(v___x_168_, 2, v___x_167_);
lean_ctor_set(v___x_168_, 3, v___x_167_);
lean_ctor_set(v___x_168_, 4, v___x_166_);
lean_ctor_set(v___x_168_, 5, v___x_166_);
lean_ctor_set(v___x_168_, 6, v___x_166_);
lean_ctor_set(v___x_168_, 7, v___x_166_);
lean_ctor_set(v___x_168_, 8, v___x_166_);
lean_ctor_set(v___x_168_, 9, v___x_166_);
lean_ctor_set(v___x_168_, 10, v___x_166_);
lean_ctor_set(v___x_168_, 11, v___x_165_);
return v___x_168_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_169_ = lean_unsigned_to_nat(32u);
v___x_170_ = lean_mk_empty_array_with_capacity(v___x_169_);
v___x_171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
return v___x_171_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__4(void){
_start:
{
size_t v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_172_ = ((size_t)5ULL);
v___x_173_ = lean_unsigned_to_nat(0u);
v___x_174_ = lean_unsigned_to_nat(32u);
v___x_175_ = lean_mk_empty_array_with_capacity(v___x_174_);
v___x_176_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__3);
v___x_177_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_177_, 0, v___x_176_);
lean_ctor_set(v___x_177_, 1, v___x_175_);
lean_ctor_set(v___x_177_, 2, v___x_173_);
lean_ctor_set(v___x_177_, 3, v___x_173_);
lean_ctor_set_usize(v___x_177_, 4, v___x_172_);
return v___x_177_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_178_ = lean_box(1);
v___x_179_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__4);
v___x_180_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1);
v___x_181_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
lean_ctor_set(v___x_181_, 1, v___x_179_);
lean_ctor_set(v___x_181_, 2, v___x_178_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg(lean_object* v_msgData_182_, lean_object* v___y_183_){
_start:
{
lean_object* v___x_185_; lean_object* v_env_186_; uint8_t v___x_187_; lean_object* v_env_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v_scopes_191_; lean_object* v___x_192_; lean_object* v_opts_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_185_ = lean_st_ref_get(v___y_183_);
v_env_186_ = lean_ctor_get(v___x_185_, 0);
lean_inc_ref(v_env_186_);
lean_dec(v___x_185_);
v___x_187_ = 0;
v_env_188_ = l_Lean_Environment_setRecordingDeps(v_env_186_, v___x_187_);
v___x_189_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_190_ = lean_st_ref_get(v___y_183_);
v_scopes_191_ = lean_ctor_get(v___x_190_, 2);
lean_inc(v_scopes_191_);
lean_dec(v___x_190_);
v___x_192_ = l_List_head_x21___redArg(v___x_189_, v_scopes_191_);
lean_dec(v_scopes_191_);
v_opts_193_ = lean_ctor_get(v___x_192_, 1);
lean_inc_ref(v_opts_193_);
lean_dec(v___x_192_);
v___x_194_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__2);
v___x_195_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__5);
v___x_196_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_196_, 0, v_env_188_);
lean_ctor_set(v___x_196_, 1, v___x_194_);
lean_ctor_set(v___x_196_, 2, v___x_195_);
lean_ctor_set(v___x_196_, 3, v_opts_193_);
v___x_197_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_197_, 0, v___x_196_);
lean_ctor_set(v___x_197_, 1, v_msgData_182_);
v___x_198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___boxed(lean_object* v_msgData_199_, lean_object* v___y_200_, lean_object* v___y_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg(v_msgData_199_, v___y_200_);
lean_dec(v___y_200_);
return v_res_202_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0(uint8_t v_suppressElabErrors_204_, lean_object* v_x_205_){
_start:
{
if (lean_obj_tag(v_x_205_) == 1)
{
lean_object* v_pre_206_; 
v_pre_206_ = lean_ctor_get(v_x_205_, 0);
if (lean_obj_tag(v_pre_206_) == 0)
{
lean_object* v_str_207_; lean_object* v___x_208_; uint8_t v___x_209_; 
v_str_207_ = lean_ctor_get(v_x_205_, 1);
v___x_208_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0___closed__0));
v___x_209_ = lean_string_dec_eq(v_str_207_, v___x_208_);
if (v___x_209_ == 0)
{
return v___x_209_;
}
else
{
return v_suppressElabErrors_204_;
}
}
else
{
uint8_t v___x_210_; 
v___x_210_ = 0;
return v___x_210_;
}
}
else
{
uint8_t v___x_211_; 
v___x_211_ = 0;
return v___x_211_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0___boxed(lean_object* v_suppressElabErrors_212_, lean_object* v_x_213_){
_start:
{
uint8_t v_suppressElabErrors_boxed_214_; uint8_t v_res_215_; lean_object* v_r_216_; 
v_suppressElabErrors_boxed_214_ = lean_unbox(v_suppressElabErrors_212_);
v_res_215_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0(v_suppressElabErrors_boxed_214_, v_x_213_);
lean_dec(v_x_213_);
v_r_216_ = lean_box(v_res_215_);
return v_r_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6(lean_object* v_ref_218_, lean_object* v_msgData_219_, uint8_t v_severity_220_, uint8_t v_isSilent_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
uint8_t v___y_226_; lean_object* v___y_227_; lean_object* v___y_228_; lean_object* v___y_229_; uint8_t v___y_230_; lean_object* v___y_231_; lean_object* v___y_232_; lean_object* v___y_233_; uint8_t v___y_291_; uint8_t v___y_292_; lean_object* v___y_293_; lean_object* v___y_294_; uint8_t v___y_317_; uint8_t v___y_318_; lean_object* v___y_319_; lean_object* v___y_320_; uint8_t v___y_324_; uint8_t v___y_325_; uint8_t v___x_340_; uint8_t v___y_342_; uint8_t v___x_352_; 
v___x_340_ = 2;
v___x_352_ = l_Lean_instBEqMessageSeverity_beq(v_severity_220_, v___x_340_);
if (v___x_352_ == 0)
{
v___y_342_ = v___x_352_;
goto v___jp_341_;
}
else
{
uint8_t v___x_353_; 
lean_inc_ref(v_msgData_219_);
v___x_353_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_219_);
if (v___x_353_ == 0)
{
v___y_342_ = v___x_353_;
goto v___jp_341_;
}
else
{
lean_object* v___x_354_; lean_object* v___x_355_; 
lean_dec_ref(v_msgData_219_);
v___x_354_ = lean_box(0);
v___x_355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
return v___x_355_;
}
}
v___jp_225_:
{
lean_object* v___x_234_; 
v___x_234_ = l_Lean_Elab_Command_getScope___redArg(v___y_233_);
if (lean_obj_tag(v___x_234_) == 0)
{
lean_object* v_a_235_; lean_object* v_currNamespace_236_; lean_object* v___x_237_; 
v_a_235_ = lean_ctor_get(v___x_234_, 0);
lean_inc(v_a_235_);
lean_dec_ref_known(v___x_234_, 1);
v_currNamespace_236_ = lean_ctor_get(v_a_235_, 2);
lean_inc(v_currNamespace_236_);
lean_dec(v_a_235_);
v___x_237_ = l_Lean_Elab_Command_getScope___redArg(v___y_233_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_273_; 
v_a_238_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_273_ == 0)
{
v___x_240_ = v___x_237_;
v_isShared_241_ = v_isSharedCheck_273_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v___x_237_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_273_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v_openDecls_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v_env_247_; lean_object* v_messages_248_; lean_object* v_scopes_249_; lean_object* v_usedQuotCtxts_250_; lean_object* v_nextMacroScope_251_; lean_object* v_maxRecDepth_252_; lean_object* v_ngen_253_; lean_object* v_auxDeclNGen_254_; lean_object* v_infoState_255_; lean_object* v_traceState_256_; lean_object* v_snapshotTasks_257_; lean_object* v_prevLinterStates_258_; lean_object* v_codeQualityEntryTasks_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_272_; 
v_openDecls_242_ = lean_ctor_get(v_a_238_, 3);
lean_inc(v_openDecls_242_);
lean_dec(v_a_238_);
v___x_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_243_, 0, v_currNamespace_236_);
lean_ctor_set(v___x_243_, 1, v_openDecls_242_);
v___x_244_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
lean_ctor_set(v___x_244_, 1, v___y_228_);
lean_inc_ref(v___y_227_);
lean_inc_ref(v___y_229_);
v___x_245_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_245_, 0, v___y_229_);
lean_ctor_set(v___x_245_, 1, v___y_231_);
lean_ctor_set(v___x_245_, 2, v___y_232_);
lean_ctor_set(v___x_245_, 3, v___y_227_);
lean_ctor_set(v___x_245_, 4, v___x_244_);
lean_ctor_set_uint8(v___x_245_, sizeof(void*)*5, v___y_230_);
lean_ctor_set_uint8(v___x_245_, sizeof(void*)*5 + 1, v___y_226_);
lean_ctor_set_uint8(v___x_245_, sizeof(void*)*5 + 2, v_isSilent_221_);
v___x_246_ = lean_st_ref_take(v___y_233_);
v_env_247_ = lean_ctor_get(v___x_246_, 0);
v_messages_248_ = lean_ctor_get(v___x_246_, 1);
v_scopes_249_ = lean_ctor_get(v___x_246_, 2);
v_usedQuotCtxts_250_ = lean_ctor_get(v___x_246_, 3);
v_nextMacroScope_251_ = lean_ctor_get(v___x_246_, 4);
v_maxRecDepth_252_ = lean_ctor_get(v___x_246_, 5);
v_ngen_253_ = lean_ctor_get(v___x_246_, 6);
v_auxDeclNGen_254_ = lean_ctor_get(v___x_246_, 7);
v_infoState_255_ = lean_ctor_get(v___x_246_, 8);
v_traceState_256_ = lean_ctor_get(v___x_246_, 9);
v_snapshotTasks_257_ = lean_ctor_get(v___x_246_, 10);
v_prevLinterStates_258_ = lean_ctor_get(v___x_246_, 11);
v_codeQualityEntryTasks_259_ = lean_ctor_get(v___x_246_, 12);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_246_);
if (v_isSharedCheck_272_ == 0)
{
v___x_261_ = v___x_246_;
v_isShared_262_ = v_isSharedCheck_272_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_codeQualityEntryTasks_259_);
lean_inc(v_prevLinterStates_258_);
lean_inc(v_snapshotTasks_257_);
lean_inc(v_traceState_256_);
lean_inc(v_infoState_255_);
lean_inc(v_auxDeclNGen_254_);
lean_inc(v_ngen_253_);
lean_inc(v_maxRecDepth_252_);
lean_inc(v_nextMacroScope_251_);
lean_inc(v_usedQuotCtxts_250_);
lean_inc(v_scopes_249_);
lean_inc(v_messages_248_);
lean_inc(v_env_247_);
lean_dec(v___x_246_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_272_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_266_; 
v___x_263_ = lean_box(0);
v___x_264_ = l_Lean_MessageLog_add(v___x_245_, v_messages_248_);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 1, v___x_264_);
v___x_266_ = v___x_261_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_env_247_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v___x_264_);
lean_ctor_set(v_reuseFailAlloc_271_, 2, v_scopes_249_);
lean_ctor_set(v_reuseFailAlloc_271_, 3, v_usedQuotCtxts_250_);
lean_ctor_set(v_reuseFailAlloc_271_, 4, v_nextMacroScope_251_);
lean_ctor_set(v_reuseFailAlloc_271_, 5, v_maxRecDepth_252_);
lean_ctor_set(v_reuseFailAlloc_271_, 6, v_ngen_253_);
lean_ctor_set(v_reuseFailAlloc_271_, 7, v_auxDeclNGen_254_);
lean_ctor_set(v_reuseFailAlloc_271_, 8, v_infoState_255_);
lean_ctor_set(v_reuseFailAlloc_271_, 9, v_traceState_256_);
lean_ctor_set(v_reuseFailAlloc_271_, 10, v_snapshotTasks_257_);
lean_ctor_set(v_reuseFailAlloc_271_, 11, v_prevLinterStates_258_);
lean_ctor_set(v_reuseFailAlloc_271_, 12, v_codeQualityEntryTasks_259_);
v___x_266_ = v_reuseFailAlloc_271_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
lean_object* v___x_267_; lean_object* v___x_269_; 
v___x_267_ = lean_st_ref_put(v___y_233_, v___x_266_);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 0, v___x_263_);
v___x_269_ = v___x_240_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v___x_263_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
}
}
else
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_281_; 
lean_dec(v_currNamespace_236_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
lean_dec_ref(v___y_228_);
v_a_274_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_281_ == 0)
{
v___x_276_ = v___x_237_;
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_237_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_279_; 
if (v_isShared_277_ == 0)
{
v___x_279_ = v___x_276_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_a_274_);
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
else
{
lean_object* v_a_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_289_; 
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
lean_dec_ref(v___y_228_);
v_a_282_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_289_ == 0)
{
v___x_284_ = v___x_234_;
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_a_282_);
lean_dec(v___x_234_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_287_; 
if (v_isShared_285_ == 0)
{
v___x_287_ = v___x_284_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_a_282_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
}
v___jp_290_:
{
lean_object* v_fileName_295_; lean_object* v_fileMap_296_; uint8_t v_suppressElabErrors_297_; lean_object* v___x_298_; lean_object* v___f_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v_a_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_315_; 
v_fileName_295_ = lean_ctor_get(v___y_222_, 0);
v_fileMap_296_ = lean_ctor_get(v___y_222_, 1);
v_suppressElabErrors_297_ = lean_ctor_get_uint8(v___y_222_, sizeof(void*)*10);
v___x_298_ = lean_box(v_suppressElabErrors_297_);
v___f_299_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0___boxed), 2, 1);
lean_closure_set(v___f_299_, 0, v___x_298_);
v___x_300_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_219_);
v___x_301_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg(v___x_300_, v___y_223_);
v_a_302_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_315_ == 0)
{
v___x_304_ = v___x_301_;
v_isShared_305_ = v_isSharedCheck_315_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_a_302_);
lean_dec(v___x_301_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_315_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
lean_inc_ref_n(v_fileMap_296_, 2);
v___x_306_ = l_Lean_FileMap_toPosition(v_fileMap_296_, v___y_293_);
lean_dec(v___y_293_);
v___x_307_ = l_Lean_FileMap_toPosition(v_fileMap_296_, v___y_294_);
lean_dec(v___y_294_);
v___x_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
v___x_309_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___closed__0));
if (v_suppressElabErrors_297_ == 0)
{
lean_del_object(v___x_304_);
lean_dec_ref(v___f_299_);
v___y_226_ = v___y_291_;
v___y_227_ = v___x_309_;
v___y_228_ = v_a_302_;
v___y_229_ = v_fileName_295_;
v___y_230_ = v___y_292_;
v___y_231_ = v___x_306_;
v___y_232_ = v___x_308_;
v___y_233_ = v___y_223_;
goto v___jp_225_;
}
else
{
uint8_t v___x_310_; 
lean_inc(v_a_302_);
v___x_310_ = l_Lean_MessageData_hasTag(v___f_299_, v_a_302_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; lean_object* v___x_313_; 
lean_dec_ref_known(v___x_308_, 1);
lean_dec_ref(v___x_306_);
lean_dec(v_a_302_);
v___x_311_ = lean_box(0);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 0, v___x_311_);
v___x_313_ = v___x_304_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_311_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
else
{
lean_del_object(v___x_304_);
v___y_226_ = v___y_291_;
v___y_227_ = v___x_309_;
v___y_228_ = v_a_302_;
v___y_229_ = v_fileName_295_;
v___y_230_ = v___y_292_;
v___y_231_ = v___x_306_;
v___y_232_ = v___x_308_;
v___y_233_ = v___y_223_;
goto v___jp_225_;
}
}
}
}
v___jp_316_:
{
lean_object* v___x_321_; 
v___x_321_ = l_Lean_Syntax_getTailPos_x3f(v___y_319_, v___y_318_);
lean_dec(v___y_319_);
if (lean_obj_tag(v___x_321_) == 0)
{
lean_inc(v___y_320_);
v___y_291_ = v___y_317_;
v___y_292_ = v___y_318_;
v___y_293_ = v___y_320_;
v___y_294_ = v___y_320_;
goto v___jp_290_;
}
else
{
lean_object* v_val_322_; 
v_val_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_val_322_);
lean_dec_ref_known(v___x_321_, 1);
v___y_291_ = v___y_317_;
v___y_292_ = v___y_318_;
v___y_293_ = v___y_320_;
v___y_294_ = v_val_322_;
goto v___jp_290_;
}
}
v___jp_323_:
{
lean_object* v___x_326_; 
v___x_326_ = l_Lean_Elab_Command_getRef___redArg(v___y_222_);
if (lean_obj_tag(v___x_326_) == 0)
{
lean_object* v_a_327_; lean_object* v_ref_328_; lean_object* v___x_329_; 
v_a_327_ = lean_ctor_get(v___x_326_, 0);
lean_inc(v_a_327_);
lean_dec_ref_known(v___x_326_, 1);
v_ref_328_ = l_Lean_replaceRef(v_ref_218_, v_a_327_);
lean_dec(v_a_327_);
v___x_329_ = l_Lean_Syntax_getPos_x3f(v_ref_328_, v___y_324_);
if (lean_obj_tag(v___x_329_) == 0)
{
lean_object* v___x_330_; 
v___x_330_ = lean_unsigned_to_nat(0u);
v___y_317_ = v___y_325_;
v___y_318_ = v___y_324_;
v___y_319_ = v_ref_328_;
v___y_320_ = v___x_330_;
goto v___jp_316_;
}
else
{
lean_object* v_val_331_; 
v_val_331_ = lean_ctor_get(v___x_329_, 0);
lean_inc(v_val_331_);
lean_dec_ref_known(v___x_329_, 1);
v___y_317_ = v___y_325_;
v___y_318_ = v___y_324_;
v___y_319_ = v_ref_328_;
v___y_320_ = v_val_331_;
goto v___jp_316_;
}
}
else
{
lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_339_; 
lean_dec_ref(v_msgData_219_);
v_a_332_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_339_ == 0)
{
v___x_334_ = v___x_326_;
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v___x_326_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_337_; 
if (v_isShared_335_ == 0)
{
v___x_337_ = v___x_334_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_a_332_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
}
}
v___jp_341_:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v_scopes_345_; lean_object* v___x_346_; lean_object* v_opts_347_; uint8_t v___x_348_; uint8_t v___x_349_; 
v___x_343_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_344_ = lean_st_ref_get(v___y_223_);
v_scopes_345_ = lean_ctor_get(v___x_344_, 2);
lean_inc(v_scopes_345_);
lean_dec(v___x_344_);
v___x_346_ = l_List_head_x21___redArg(v___x_343_, v_scopes_345_);
lean_dec(v_scopes_345_);
v_opts_347_ = lean_ctor_get(v___x_346_, 1);
lean_inc_ref(v_opts_347_);
lean_dec(v___x_346_);
v___x_348_ = 1;
v___x_349_ = l_Lean_instBEqMessageSeverity_beq(v_severity_220_, v___x_348_);
if (v___x_349_ == 0)
{
lean_dec_ref(v_opts_347_);
v___y_324_ = v___y_342_;
v___y_325_ = v_severity_220_;
goto v___jp_323_;
}
else
{
lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_350_ = l_Lean_warningAsError;
v___x_351_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__10(v_opts_347_, v___x_350_);
lean_dec_ref(v_opts_347_);
if (v___x_351_ == 0)
{
v___y_324_ = v___y_342_;
v___y_325_ = v_severity_220_;
goto v___jp_323_;
}
else
{
v___y_324_ = v___y_342_;
v___y_325_ = v___x_340_;
goto v___jp_323_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___boxed(lean_object* v_ref_356_, lean_object* v_msgData_357_, lean_object* v_severity_358_, lean_object* v_isSilent_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_){
_start:
{
uint8_t v_severity_boxed_363_; uint8_t v_isSilent_boxed_364_; lean_object* v_res_365_; 
v_severity_boxed_363_ = lean_unbox(v_severity_358_);
v_isSilent_boxed_364_ = lean_unbox(v_isSilent_359_);
v_res_365_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6(v_ref_356_, v_msgData_357_, v_severity_boxed_363_, v_isSilent_boxed_364_, v___y_360_, v___y_361_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
lean_dec(v_ref_356_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5(lean_object* v_ref_366_, lean_object* v_msgData_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
uint8_t v___x_371_; uint8_t v___x_372_; lean_object* v___x_373_; 
v___x_371_ = 1;
v___x_372_ = 0;
v___x_373_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6(v_ref_366_, v_msgData_367_, v___x_371_, v___x_372_, v___y_368_, v___y_369_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5___boxed(lean_object* v_ref_374_, lean_object* v_msgData_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5(v_ref_374_, v_msgData_375_, v___y_376_, v___y_377_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec(v_ref_374_);
return v_res_379_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__1(void){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__0));
v___x_382_ = l_Lean_stringToMessageData(v___x_381_);
return v___x_382_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__3(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__2));
v___x_385_ = l_Lean_stringToMessageData(v___x_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4(lean_object* v_linterOption_386_, lean_object* v_stx_387_, lean_object* v_msg_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
lean_object* v_name_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_410_; 
v_name_392_ = lean_ctor_get(v_linterOption_386_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v_linterOption_386_);
if (v_isSharedCheck_410_ == 0)
{
lean_object* v_unused_411_; 
v_unused_411_ = lean_ctor_get(v_linterOption_386_, 1);
lean_dec(v_unused_411_);
v___x_394_ = v_linterOption_386_;
v_isShared_395_ = v_isSharedCheck_410_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_name_392_);
lean_dec(v_linterOption_386_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_410_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_399_; 
v___x_396_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__1);
lean_inc(v_name_392_);
v___x_397_ = l_Lean_MessageData_ofName(v_name_392_);
if (v_isShared_395_ == 0)
{
lean_ctor_set_tag(v___x_394_, 7);
lean_ctor_set(v___x_394_, 1, v___x_397_);
lean_ctor_set(v___x_394_, 0, v___x_396_);
v___x_399_ = v___x_394_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_396_);
lean_ctor_set(v_reuseFailAlloc_409_, 1, v___x_397_);
v___x_399_ = v_reuseFailAlloc_409_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v_disable_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_400_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__3);
v___x_401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_401_, 0, v___x_399_);
lean_ctor_set(v___x_401_, 1, v___x_400_);
v_disable_402_ = l_Lean_MessageData_note(v___x_401_);
v___x_403_ = l_Lean_Linter_linterMessageTag;
v___x_404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_404_, 0, v_msg_388_);
lean_ctor_set(v___x_404_, 1, v_disable_402_);
v___x_405_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_403_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
v___x_406_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_406_, 0, v_name_392_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
lean_inc(v_stx_387_);
v___x_407_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_407_, 0, v_stx_387_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
v___x_408_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5(v_stx_387_, v___x_407_, v___y_389_, v___y_390_);
lean_dec(v_stx_387_);
return v___x_408_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___boxed(lean_object* v_linterOption_412_, lean_object* v_stx_413_, lean_object* v_msg_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4(v_linterOption_412_, v_stx_413_, v_msg_414_, v___y_415_, v___y_416_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
return v_res_418_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__2(void){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__1));
v___x_423_ = l_Lean_MessageData_ofFormat(v___x_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5(lean_object* v_as_439_, size_t v_sz_440_, size_t v_i_441_, lean_object* v_b_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v_a_447_; uint8_t v___x_451_; 
v___x_451_ = lean_usize_dec_lt(v_i_441_, v_sz_440_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; 
v___x_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_452_, 0, v_b_442_);
return v___x_452_;
}
else
{
lean_object* v___x_453_; lean_object* v_patHead_455_; lean_object* v___y_456_; lean_object* v___y_457_; lean_object* v_a_461_; lean_object* v___x_462_; uint8_t v___x_463_; 
v___x_453_ = lean_box(0);
v_a_461_ = lean_array_uget_borrowed(v_as_439_, v_i_441_);
v___x_462_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__4));
lean_inc(v_a_461_);
v___x_463_ = l_Lean_Syntax_isOfKind(v_a_461_, v___x_462_);
if (v___x_463_ == 0)
{
v_a_447_ = v___x_453_;
goto v___jp_446_;
}
else
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; uint8_t v___x_467_; 
v___x_464_ = lean_unsigned_to_nat(1u);
v___x_465_ = l_Lean_Syntax_getArg(v_a_461_, v___x_464_);
v___x_466_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__6));
lean_inc(v___x_465_);
v___x_467_ = l_Lean_Syntax_isOfKind(v___x_465_, v___x_466_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; uint8_t v___x_469_; 
v___x_468_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__8));
lean_inc(v___x_465_);
v___x_469_ = l_Lean_Syntax_isOfKind(v___x_465_, v___x_468_);
if (v___x_469_ == 0)
{
lean_dec(v___x_465_);
v_a_447_ = v___x_453_;
goto v___jp_446_;
}
else
{
v_patHead_455_ = v___x_465_;
v___y_456_ = v___y_443_;
v___y_457_ = v___y_444_;
goto v___jp_454_;
}
}
else
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; uint8_t v___x_473_; 
v___x_470_ = lean_unsigned_to_nat(0u);
v___x_471_ = l_Lean_Syntax_getArg(v___x_465_, v___x_470_);
lean_dec(v___x_465_);
v___x_472_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__8));
lean_inc(v___x_471_);
v___x_473_ = l_Lean_Syntax_isOfKind(v___x_471_, v___x_472_);
if (v___x_473_ == 0)
{
lean_dec(v___x_471_);
v_a_447_ = v___x_453_;
goto v___jp_446_;
}
else
{
v_patHead_455_ = v___x_471_;
v___y_456_ = v___y_443_;
v___y_457_ = v___y_444_;
goto v___jp_454_;
}
}
}
v___jp_454_:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_458_ = l_Lean_Linter_linter_suspiciousUnexpanderPatterns;
v___x_459_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__2);
v___x_460_ = l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4(v___x_458_, v_patHead_455_, v___x_459_, v___y_456_, v___y_457_);
if (lean_obj_tag(v___x_460_) == 0)
{
lean_dec_ref_known(v___x_460_, 1);
v_a_447_ = v___x_453_;
goto v___jp_446_;
}
else
{
return v___x_460_;
}
}
}
v___jp_446_:
{
size_t v___x_448_; size_t v___x_449_; 
v___x_448_ = ((size_t)1ULL);
v___x_449_ = lean_usize_add(v_i_441_, v___x_448_);
v_i_441_ = v___x_449_;
v_b_442_ = v_a_447_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___boxed(lean_object* v_as_474_, lean_object* v_sz_475_, lean_object* v_i_476_, lean_object* v_b_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
size_t v_sz_boxed_481_; size_t v_i_boxed_482_; lean_object* v_res_483_; 
v_sz_boxed_481_ = lean_unbox_usize(v_sz_475_);
lean_dec(v_sz_475_);
v_i_boxed_482_ = lean_unbox_usize(v_i_476_);
lean_dec(v_i_476_);
v_res_483_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5(v_as_474_, v_sz_boxed_481_, v_i_boxed_482_, v_b_477_, v___y_478_, v___y_479_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec_ref(v_as_474_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2(size_t v_sz_490_, size_t v_i_491_, lean_object* v_bs_492_){
_start:
{
uint8_t v___x_493_; 
v___x_493_ = lean_usize_dec_lt(v_i_491_, v_sz_490_);
if (v___x_493_ == 0)
{
lean_object* v___x_494_; 
v___x_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_494_, 0, v_bs_492_);
return v___x_494_;
}
else
{
lean_object* v_v_495_; lean_object* v___x_496_; uint8_t v___x_497_; 
v_v_495_ = lean_array_uget_borrowed(v_bs_492_, v_i_491_);
v___x_496_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__1));
lean_inc(v_v_495_);
v___x_497_ = l_Lean_Syntax_isOfKind(v_v_495_, v___x_496_);
if (v___x_497_ == 0)
{
lean_object* v___x_498_; 
lean_dec_ref(v_bs_492_);
v___x_498_ = lean_box(0);
return v___x_498_;
}
else
{
lean_object* v___x_499_; lean_object* v___x_500_; uint8_t v___x_501_; 
v___x_499_ = lean_unsigned_to_nat(1u);
v___x_500_ = l_Lean_Syntax_getArg(v_v_495_, v___x_499_);
lean_inc(v___x_500_);
v___x_501_ = l_Lean_Syntax_matchesNull(v___x_500_, v___x_499_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; 
lean_dec(v___x_500_);
lean_dec_ref(v_bs_492_);
v___x_502_ = lean_box(0);
return v___x_502_;
}
else
{
lean_object* v___x_503_; lean_object* v___x_504_; uint8_t v___x_505_; 
v___x_503_ = lean_unsigned_to_nat(0u);
v___x_504_ = l_Lean_Syntax_getArg(v___x_500_, v___x_503_);
lean_dec(v___x_500_);
lean_inc(v___x_504_);
v___x_505_ = l_Lean_Syntax_matchesNull(v___x_504_, v___x_499_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; 
lean_dec(v___x_504_);
lean_dec_ref(v_bs_492_);
v___x_506_ = lean_box(0);
return v___x_506_;
}
else
{
lean_object* v_bs_x27_507_; lean_object* v___x_508_; size_t v___x_509_; size_t v___x_510_; lean_object* v___x_511_; 
v_bs_x27_507_ = lean_array_uset(v_bs_492_, v_i_491_, v___x_503_);
v___x_508_ = l_Lean_Syntax_getArg(v___x_504_, v___x_503_);
lean_dec(v___x_504_);
v___x_509_ = ((size_t)1ULL);
v___x_510_ = lean_usize_add(v_i_491_, v___x_509_);
v___x_511_ = lean_array_uset(v_bs_x27_507_, v_i_491_, v___x_508_);
v_i_491_ = v___x_510_;
v_bs_492_ = v___x_511_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___boxed(lean_object* v_sz_513_, lean_object* v_i_514_, lean_object* v_bs_515_){
_start:
{
size_t v_sz_boxed_516_; size_t v_i_boxed_517_; lean_object* v_res_518_; 
v_sz_boxed_516_ = lean_unbox_usize(v_sz_513_);
lean_dec(v_sz_513_);
v_i_boxed_517_ = lean_unbox_usize(v_i_514_);
lean_dec(v_i_514_);
v_res_518_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2(v_sz_boxed_516_, v_i_boxed_517_, v_bs_515_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__6(uint8_t v___x_519_, lean_object* v_as_520_, size_t v_i_521_, size_t v_stop_522_, lean_object* v_b_523_){
_start:
{
lean_object* v___y_525_; uint8_t v___x_529_; 
v___x_529_ = lean_usize_dec_eq(v_i_521_, v_stop_522_);
if (v___x_529_ == 0)
{
lean_object* v_fst_530_; uint8_t v___x_531_; 
v_fst_530_ = lean_ctor_get(v_b_523_, 0);
v___x_531_ = lean_unbox(v_fst_530_);
if (v___x_531_ == 0)
{
lean_object* v_snd_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_540_; 
v_snd_532_ = lean_ctor_get(v_b_523_, 1);
v_isSharedCheck_540_ = !lean_is_exclusive(v_b_523_);
if (v_isSharedCheck_540_ == 0)
{
lean_object* v_unused_541_; 
v_unused_541_ = lean_ctor_get(v_b_523_, 0);
lean_dec(v_unused_541_);
v___x_534_ = v_b_523_;
v_isShared_535_ = v_isSharedCheck_540_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_snd_532_);
lean_dec(v_b_523_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_540_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_536_; lean_object* v___x_538_; 
v___x_536_ = lean_box(v___x_519_);
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 0, v___x_536_);
v___x_538_ = v___x_534_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v___x_536_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v_snd_532_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
v___y_525_ = v___x_538_;
goto v___jp_524_;
}
}
}
else
{
lean_object* v_snd_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_552_; 
v_snd_542_ = lean_ctor_get(v_b_523_, 1);
v_isSharedCheck_552_ = !lean_is_exclusive(v_b_523_);
if (v_isSharedCheck_552_ == 0)
{
lean_object* v_unused_553_; 
v_unused_553_ = lean_ctor_get(v_b_523_, 0);
lean_dec(v_unused_553_);
v___x_544_ = v_b_523_;
v_isShared_545_ = v_isSharedCheck_552_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_snd_542_);
lean_dec(v_b_523_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_552_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_550_; 
v___x_546_ = lean_array_uget_borrowed(v_as_520_, v_i_521_);
lean_inc(v___x_546_);
v___x_547_ = lean_array_push(v_snd_542_, v___x_546_);
v___x_548_ = lean_box(v___x_529_);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 1, v___x_547_);
lean_ctor_set(v___x_544_, 0, v___x_548_);
v___x_550_ = v___x_544_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_548_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v___x_547_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
v___y_525_ = v___x_550_;
goto v___jp_524_;
}
}
}
}
else
{
return v_b_523_;
}
v___jp_524_:
{
size_t v___x_526_; size_t v___x_527_; 
v___x_526_ = ((size_t)1ULL);
v___x_527_ = lean_usize_add(v_i_521_, v___x_526_);
v_i_521_ = v___x_527_;
v_b_523_ = v___y_525_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__6___boxed(lean_object* v___x_554_, lean_object* v_as_555_, lean_object* v_i_556_, lean_object* v_stop_557_, lean_object* v_b_558_){
_start:
{
uint8_t v___x_10845__boxed_559_; size_t v_i_boxed_560_; size_t v_stop_boxed_561_; lean_object* v_res_562_; 
v___x_10845__boxed_559_ = lean_unbox(v___x_554_);
v_i_boxed_560_ = lean_unbox_usize(v_i_556_);
lean_dec(v_i_556_);
v_stop_boxed_561_ = lean_unbox_usize(v_stop_557_);
lean_dec(v_stop_557_);
v_res_562_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__6(v___x_10845__boxed_559_, v_as_555_, v_i_boxed_560_, v_stop_boxed_561_, v_b_558_);
lean_dec_ref(v_as_555_);
return v_res_562_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3(uint8_t v___x_573_, lean_object* v_as_574_, size_t v_i_575_, size_t v_stop_576_){
_start:
{
uint8_t v___x_581_; 
v___x_581_ = lean_usize_dec_eq(v_i_575_, v_stop_576_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; lean_object* v___x_583_; uint8_t v___x_584_; 
v___x_582_ = lean_array_uget_borrowed(v_as_574_, v_i_575_);
v___x_583_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__2));
lean_inc(v___x_582_);
v___x_584_ = l_Lean_Syntax_isOfKind(v___x_582_, v___x_583_);
if (v___x_584_ == 0)
{
goto v___jp_577_;
}
else
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; uint8_t v___x_588_; 
v___x_585_ = lean_unsigned_to_nat(0u);
v___x_586_ = l_Lean_Syntax_getArg(v___x_582_, v___x_585_);
v___x_587_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__4));
v___x_588_ = l_Lean_Syntax_matchesIdent(v___x_586_, v___x_587_);
lean_dec(v___x_586_);
if (v___x_588_ == 0)
{
goto v___jp_577_;
}
else
{
lean_object* v___x_589_; lean_object* v___x_590_; uint8_t v___x_591_; 
v___x_589_ = lean_unsigned_to_nat(1u);
v___x_590_ = l_Lean_Syntax_getArg(v___x_582_, v___x_589_);
v___x_591_ = l_Lean_Syntax_matchesNull(v___x_590_, v___x_589_);
if (v___x_591_ == 0)
{
goto v___jp_577_;
}
else
{
if (v___x_573_ == 0)
{
goto v___jp_577_;
}
else
{
return v___x_573_;
}
}
}
}
}
else
{
uint8_t v___x_592_; 
v___x_592_ = 0;
return v___x_592_;
}
v___jp_577_:
{
size_t v___x_578_; size_t v___x_579_; 
v___x_578_ = ((size_t)1ULL);
v___x_579_ = lean_usize_add(v_i_575_, v___x_578_);
v_i_575_ = v___x_579_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___boxed(lean_object* v___x_593_, lean_object* v_as_594_, lean_object* v_i_595_, lean_object* v_stop_596_){
_start:
{
uint8_t v___x_10930__boxed_597_; size_t v_i_boxed_598_; size_t v_stop_boxed_599_; uint8_t v_res_600_; lean_object* v_r_601_; 
v___x_10930__boxed_597_ = lean_unbox(v___x_593_);
v_i_boxed_598_ = lean_unbox_usize(v_i_595_);
lean_dec(v_i_595_);
v_stop_boxed_599_ = lean_unbox_usize(v_stop_596_);
lean_dec(v_stop_596_);
v_res_600_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3(v___x_10930__boxed_597_, v_as_594_, v_i_boxed_598_, v_stop_boxed_599_);
lean_dec_ref(v_as_594_);
v_r_601_ = lean_box(v_res_600_);
return v_r_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0(lean_object* v_cmdStx_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v___x_664_; lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_879_; 
v___x_664_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0(v___y_658_, v___y_659_);
v_a_665_ = lean_ctor_get(v___x_664_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_879_ == 0)
{
v___x_667_ = v___x_664_;
v_isShared_668_ = v_isSharedCheck_879_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_664_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_879_;
goto v_resetjp_666_;
}
v___jp_661_:
{
lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_662_ = lean_box(0);
v___x_663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_663_, 0, v___x_662_);
return v___x_663_;
}
v_resetjp_666_:
{
uint8_t v___x_669_; 
v___x_669_ = l_Lean_Linter_getLinterSuspiciousUnexpanderPatterns(v_a_665_);
lean_dec(v_a_665_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; lean_object* v___x_672_; 
lean_dec(v_cmdStx_657_);
v___x_670_ = lean_box(0);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_670_);
v___x_672_ = v___x_667_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_670_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
else
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; uint8_t v___x_677_; 
v___x_674_ = ((lean_object*)(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_));
v___x_675_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0));
v___x_676_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__2));
lean_inc(v_cmdStx_657_);
v___x_677_ = l_Lean_Syntax_isOfKind(v_cmdStx_657_, v___x_676_);
if (v___x_677_ == 0)
{
lean_object* v___x_678_; lean_object* v___x_680_; 
lean_dec(v_cmdStx_657_);
v___x_678_ = lean_box(0);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_678_);
v___x_680_ = v___x_667_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_678_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
else
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; uint8_t v___x_685_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_842_; lean_object* v___y_843_; 
v___x_682_ = lean_unsigned_to_nat(0u);
v___x_683_ = l_Lean_Syntax_getArg(v_cmdStx_657_, v___x_682_);
v___x_684_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__4));
lean_inc(v___x_683_);
v___x_685_ = l_Lean_Syntax_isOfKind(v___x_683_, v___x_684_);
if (v___x_685_ == 0)
{
lean_object* v___x_866_; lean_object* v___x_867_; 
lean_dec(v___x_683_);
lean_del_object(v___x_667_);
lean_dec(v_cmdStx_657_);
v___x_866_ = lean_box(0);
v___x_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_867_, 0, v___x_866_);
return v___x_867_;
}
else
{
lean_object* v___x_868_; uint8_t v___x_869_; 
v___x_868_ = l_Lean_Syntax_getArg(v___x_683_, v___x_682_);
v___x_869_ = l_Lean_Syntax_isNone(v___x_868_);
if (v___x_869_ == 0)
{
lean_object* v___x_870_; uint8_t v___x_871_; 
v___x_870_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_868_);
v___x_871_ = l_Lean_Syntax_matchesNull(v___x_868_, v___x_870_);
if (v___x_871_ == 0)
{
lean_object* v___x_872_; lean_object* v___x_873_; 
lean_dec(v___x_868_);
lean_dec(v___x_683_);
lean_del_object(v___x_667_);
lean_dec(v_cmdStx_657_);
v___x_872_ = lean_box(0);
v___x_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_873_, 0, v___x_872_);
return v___x_873_;
}
else
{
lean_object* v___x_874_; lean_object* v___x_875_; uint8_t v___x_876_; 
v___x_874_ = l_Lean_Syntax_getArg(v___x_868_, v___x_682_);
lean_dec(v___x_868_);
v___x_875_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__21));
v___x_876_ = l_Lean_Syntax_isOfKind(v___x_874_, v___x_875_);
if (v___x_876_ == 0)
{
lean_object* v___x_877_; lean_object* v___x_878_; 
lean_dec(v___x_683_);
lean_del_object(v___x_667_);
lean_dec(v_cmdStx_657_);
v___x_877_ = lean_box(0);
v___x_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_878_, 0, v___x_877_);
return v___x_878_;
}
else
{
v___y_842_ = v___y_658_;
v___y_843_ = v___y_659_;
goto v___jp_841_;
}
}
}
else
{
lean_dec(v___x_868_);
v___y_842_ = v___y_658_;
v___y_843_ = v___y_659_;
goto v___jp_841_;
}
}
v___jp_686_:
{
size_t v_sz_692_; size_t v___x_693_; lean_object* v___x_694_; 
v_sz_692_ = lean_array_size(v___y_691_);
v___x_693_ = ((size_t)0ULL);
v___x_694_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1(v_sz_692_, v___x_693_, v___y_691_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v___x_695_; lean_object* v___x_697_; 
lean_dec(v___x_683_);
lean_dec(v_cmdStx_657_);
v___x_695_ = lean_box(0);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_695_);
v___x_697_ = v___x_667_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_695_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
else
{
lean_object* v_val_699_; lean_object* v___x_700_; lean_object* v___x_701_; uint8_t v___x_702_; 
v_val_699_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_val_699_);
lean_dec_ref_known(v___x_694_, 1);
v___x_700_ = lean_unsigned_to_nat(3u);
v___x_701_ = l_Lean_Syntax_getArg(v___x_683_, v___x_700_);
v___x_702_ = l_Lean_Syntax_matchesNull(v___x_701_, v___x_682_);
if (v___x_702_ == 0)
{
lean_object* v___x_703_; lean_object* v___x_705_; 
lean_dec(v_val_699_);
lean_dec(v___x_683_);
lean_dec(v_cmdStx_657_);
v___x_703_ = lean_box(0);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_703_);
v___x_705_ = v___x_667_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_703_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
else
{
lean_object* v___x_707_; lean_object* v___x_708_; uint8_t v___x_709_; 
v___x_707_ = lean_unsigned_to_nat(4u);
v___x_708_ = l_Lean_Syntax_getArg(v___x_683_, v___x_707_);
v___x_709_ = l_Lean_Syntax_matchesNull(v___x_708_, v___x_682_);
if (v___x_709_ == 0)
{
lean_object* v___x_710_; lean_object* v___x_712_; 
lean_dec(v_val_699_);
lean_dec(v___x_683_);
lean_dec(v_cmdStx_657_);
v___x_710_ = lean_box(0);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_710_);
v___x_712_ = v___x_667_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v___x_710_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
else
{
lean_object* v___x_714_; lean_object* v___x_715_; uint8_t v___x_716_; 
v___x_714_ = lean_unsigned_to_nat(5u);
v___x_715_ = l_Lean_Syntax_getArg(v___x_683_, v___x_714_);
v___x_716_ = l_Lean_Syntax_matchesNull(v___x_715_, v___x_682_);
if (v___x_716_ == 0)
{
lean_object* v___x_717_; lean_object* v___x_719_; 
lean_dec(v_val_699_);
lean_dec(v___x_683_);
lean_dec(v_cmdStx_657_);
v___x_717_ = lean_box(0);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_717_);
v___x_719_ = v___x_667_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_717_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
else
{
lean_object* v___x_721_; lean_object* v___x_722_; uint8_t v___x_723_; 
v___x_721_ = lean_unsigned_to_nat(6u);
v___x_722_ = l_Lean_Syntax_getArg(v___x_683_, v___x_721_);
lean_dec(v___x_683_);
v___x_723_ = l_Lean_Syntax_matchesNull(v___x_722_, v___x_682_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; lean_object* v___x_726_; 
lean_dec(v_val_699_);
lean_dec(v_cmdStx_657_);
v___x_724_ = lean_box(0);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_724_);
v___x_726_ = v___x_667_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v___x_724_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
else
{
lean_object* v___x_728_; lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_728_ = l_Lean_Syntax_getArg(v_cmdStx_657_, v___y_689_);
lean_dec(v_cmdStx_657_);
v___x_729_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__6));
lean_inc(v___x_728_);
v___x_730_ = l_Lean_Syntax_isOfKind(v___x_728_, v___x_729_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; lean_object* v___x_733_; 
lean_dec(v___x_728_);
lean_dec(v_val_699_);
v___x_731_ = lean_box(0);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_731_);
v___x_733_ = v___x_667_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_731_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
else
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; uint8_t v___x_738_; 
v___x_735_ = lean_unsigned_to_nat(2u);
v___x_736_ = l_Lean_Syntax_getArg(v___x_728_, v___x_735_);
v___x_737_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__8));
lean_inc(v___x_736_);
v___x_738_ = l_Lean_Syntax_isOfKind(v___x_736_, v___x_737_);
if (v___x_738_ == 0)
{
lean_object* v___x_739_; lean_object* v___x_741_; 
lean_dec(v___x_736_);
lean_dec(v___x_728_);
lean_dec(v_val_699_);
v___x_739_ = lean_box(0);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_739_);
v___x_741_ = v___x_667_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v___x_739_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
else
{
lean_object* v___x_743_; uint8_t v___x_744_; 
v___x_743_ = l_Lean_Syntax_getArg(v___x_736_, v___x_682_);
v___x_744_ = l_Lean_Syntax_matchesNull(v___x_743_, v___x_682_);
if (v___x_744_ == 0)
{
lean_object* v___x_745_; lean_object* v___x_747_; 
lean_dec(v___x_736_);
lean_dec(v___x_728_);
lean_dec(v_val_699_);
v___x_745_ = lean_box(0);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_745_);
v___x_747_ = v___x_667_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_745_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
else
{
lean_object* v___x_749_; uint8_t v___x_750_; 
v___x_749_ = l_Lean_Syntax_getArg(v___x_736_, v___y_689_);
lean_dec(v___x_736_);
lean_inc(v___x_749_);
v___x_750_ = l_Lean_Syntax_matchesNull(v___x_749_, v___y_689_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; lean_object* v___x_753_; 
lean_dec(v___x_749_);
lean_dec(v___x_728_);
lean_dec(v_val_699_);
v___x_751_ = lean_box(0);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_751_);
v___x_753_ = v___x_667_;
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
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; uint8_t v___x_758_; 
v___x_755_ = l_Lean_Syntax_getArg(v___x_749_, v___x_682_);
lean_dec(v___x_749_);
v___x_756_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__9));
lean_inc_ref(v___y_687_);
v___x_757_ = l_Lean_Name_mkStr4(v___x_674_, v___x_675_, v___y_687_, v___x_756_);
v___x_758_ = l_Lean_Syntax_isOfKind(v___x_755_, v___x_757_);
lean_dec(v___x_757_);
if (v___x_758_ == 0)
{
lean_object* v___x_759_; lean_object* v___x_761_; 
lean_dec(v___x_728_);
lean_dec(v_val_699_);
v___x_759_ = lean_box(0);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_759_);
v___x_761_ = v___x_667_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_759_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
else
{
lean_object* v___x_763_; lean_object* v___x_764_; uint8_t v___x_765_; 
v___x_763_ = l_Lean_Syntax_getArg(v___x_728_, v___x_700_);
v___x_764_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__11));
lean_inc(v___x_763_);
v___x_765_ = l_Lean_Syntax_isOfKind(v___x_763_, v___x_764_);
if (v___x_765_ == 0)
{
lean_object* v___x_766_; lean_object* v___x_768_; 
lean_dec(v___x_763_);
lean_dec(v___x_728_);
lean_dec(v_val_699_);
v___x_766_ = lean_box(0);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_766_);
v___x_768_ = v___x_667_;
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
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; uint8_t v___x_773_; 
v___x_770_ = l_Lean_Syntax_getArg(v___x_763_, v___x_682_);
lean_dec(v___x_763_);
v___x_771_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__12));
lean_inc_ref(v___y_687_);
v___x_772_ = l_Lean_Name_mkStr4(v___x_674_, v___x_675_, v___y_687_, v___x_771_);
lean_inc(v___x_770_);
v___x_773_ = l_Lean_Syntax_isOfKind(v___x_770_, v___x_772_);
lean_dec(v___x_772_);
if (v___x_773_ == 0)
{
lean_object* v___x_774_; lean_object* v___x_776_; 
lean_dec(v___x_770_);
lean_dec(v___x_728_);
lean_dec(v_val_699_);
v___x_774_ = lean_box(0);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_774_);
v___x_776_ = v___x_667_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_774_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
else
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; uint8_t v___x_781_; 
v___x_778_ = l_Lean_Syntax_getArg(v___x_770_, v___x_682_);
v___x_779_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__13));
lean_inc_ref(v___y_687_);
v___x_780_ = l_Lean_Name_mkStr4(v___x_674_, v___x_675_, v___y_687_, v___x_779_);
lean_inc(v___x_778_);
v___x_781_ = l_Lean_Syntax_isOfKind(v___x_778_, v___x_780_);
lean_dec(v___x_780_);
if (v___x_781_ == 0)
{
lean_object* v___x_782_; lean_object* v___x_784_; 
lean_dec(v___x_778_);
lean_dec(v___x_770_);
lean_dec(v___x_728_);
lean_dec(v_val_699_);
v___x_782_ = lean_box(0);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_782_);
v___x_784_ = v___x_667_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_782_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
else
{
lean_object* v___x_786_; lean_object* v___x_787_; size_t v_sz_788_; lean_object* v___x_789_; 
v___x_786_ = l_Lean_Syntax_getArg(v___x_778_, v___x_682_);
lean_dec(v___x_778_);
v___x_787_ = l_Lean_Syntax_getArgs(v___x_786_);
lean_dec(v___x_786_);
v_sz_788_ = lean_array_size(v___x_787_);
v___x_789_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2(v_sz_788_, v___x_693_, v___x_787_);
if (lean_obj_tag(v___x_789_) == 0)
{
lean_object* v___x_790_; lean_object* v___x_792_; 
lean_dec(v___x_770_);
lean_dec(v___x_728_);
lean_dec(v_val_699_);
v___x_790_ = lean_box(0);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_790_);
v___x_792_ = v___x_667_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_790_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
else
{
lean_object* v_val_794_; lean_object* v___x_795_; lean_object* v___x_796_; uint8_t v___x_797_; 
v_val_794_ = lean_ctor_get(v___x_789_, 0);
lean_inc(v_val_794_);
lean_dec_ref_known(v___x_789_, 1);
v___x_795_ = l_Lean_Syntax_getArg(v___x_770_, v___y_689_);
v___x_796_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__16));
lean_inc(v___x_795_);
v___x_797_ = l_Lean_Syntax_isOfKind(v___x_795_, v___x_796_);
if (v___x_797_ == 0)
{
lean_object* v___x_798_; lean_object* v___x_800_; 
lean_dec(v___x_795_);
lean_dec(v_val_794_);
lean_dec(v___x_770_);
lean_dec(v___x_728_);
lean_dec(v_val_699_);
v___x_798_ = lean_box(0);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_798_);
v___x_800_ = v___x_667_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v___x_798_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
else
{
lean_object* v___x_802_; uint8_t v___x_803_; 
v___x_802_ = l_Lean_Syntax_getArg(v___x_795_, v___x_682_);
v___x_803_ = l_Lean_Syntax_matchesNull(v___x_802_, v___x_682_);
if (v___x_803_ == 0)
{
lean_object* v___x_804_; lean_object* v___x_806_; 
lean_dec(v___x_795_);
lean_dec(v_val_794_);
lean_dec(v___x_770_);
lean_dec(v___x_728_);
lean_dec(v_val_699_);
v___x_804_ = lean_box(0);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_804_);
v___x_806_ = v___x_667_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_804_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
else
{
lean_object* v___x_808_; uint8_t v___x_809_; 
v___x_808_ = l_Lean_Syntax_getArg(v___x_795_, v___y_689_);
lean_dec(v___x_795_);
v___x_809_ = l_Lean_Syntax_matchesNull(v___x_808_, v___x_682_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; lean_object* v___x_812_; 
lean_dec(v_val_794_);
lean_dec(v___x_770_);
lean_dec(v___x_728_);
lean_dec(v_val_699_);
v___x_810_ = lean_box(0);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_810_);
v___x_812_ = v___x_667_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_810_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
else
{
lean_object* v___x_814_; uint8_t v___x_815_; 
v___x_814_ = l_Lean_Syntax_getArg(v___x_770_, v___x_735_);
lean_dec(v___x_770_);
v___x_815_ = l_Lean_Syntax_matchesNull(v___x_814_, v___x_682_);
if (v___x_815_ == 0)
{
lean_object* v___x_816_; lean_object* v___x_818_; 
lean_dec(v_val_794_);
lean_dec(v___x_728_);
lean_dec(v_val_699_);
v___x_816_ = lean_box(0);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_816_);
v___x_818_ = v___x_667_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_816_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
else
{
lean_object* v___x_820_; uint8_t v___x_821_; 
v___x_820_ = l_Lean_Syntax_getArg(v___x_728_, v___x_707_);
lean_dec(v___x_728_);
v___x_821_ = l_Lean_Syntax_matchesNull(v___x_820_, v___x_682_);
if (v___x_821_ == 0)
{
lean_object* v___x_822_; lean_object* v___x_824_; 
lean_dec(v_val_794_);
lean_dec(v_val_699_);
v___x_822_ = lean_box(0);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_822_);
v___x_824_ = v___x_667_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_822_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
else
{
lean_object* v___x_826_; uint8_t v___x_827_; 
lean_del_object(v___x_667_);
v___x_826_ = lean_array_get_size(v_val_699_);
v___x_827_ = lean_nat_dec_lt(v___x_682_, v___x_826_);
if (v___x_827_ == 0)
{
lean_dec(v_val_794_);
lean_dec(v_val_699_);
goto v___jp_661_;
}
else
{
if (v___x_827_ == 0)
{
lean_dec(v_val_794_);
lean_dec(v_val_699_);
goto v___jp_661_;
}
else
{
size_t v___x_828_; uint8_t v___x_829_; 
v___x_828_ = lean_usize_of_nat(v___x_826_);
v___x_829_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3(v___x_685_, v_val_699_, v___x_693_, v___x_828_);
lean_dec(v_val_699_);
if (v___x_829_ == 0)
{
lean_dec(v_val_794_);
goto v___jp_661_;
}
else
{
lean_object* v___x_830_; size_t v_sz_831_; lean_object* v___x_832_; 
v___x_830_ = lean_box(0);
v_sz_831_ = lean_array_size(v_val_794_);
v___x_832_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5(v_val_794_, v_sz_831_, v___x_693_, v___x_830_, v___y_688_, v___y_690_);
lean_dec(v_val_794_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_839_ == 0)
{
lean_object* v_unused_840_; 
v_unused_840_ = lean_ctor_get(v___x_832_, 0);
lean_dec(v_unused_840_);
v___x_834_ = v___x_832_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_dec(v___x_832_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 0, v___x_830_);
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_830_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
else
{
return v___x_832_;
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
v___jp_841_:
{
lean_object* v___x_844_; lean_object* v___x_845_; uint8_t v___x_846_; 
v___x_844_ = lean_unsigned_to_nat(1u);
v___x_845_ = l_Lean_Syntax_getArg(v___x_683_, v___x_844_);
lean_inc(v___x_845_);
v___x_846_ = l_Lean_Syntax_matchesNull(v___x_845_, v___x_844_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; lean_object* v___x_848_; 
lean_dec(v___x_845_);
lean_dec(v___x_683_);
lean_del_object(v___x_667_);
lean_dec(v_cmdStx_657_);
v___x_847_ = lean_box(0);
v___x_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
return v___x_848_;
}
else
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; uint8_t v___x_852_; 
v___x_849_ = l_Lean_Syntax_getArg(v___x_845_, v___x_682_);
lean_dec(v___x_845_);
v___x_850_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__1));
v___x_851_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__18));
lean_inc(v___x_849_);
v___x_852_ = l_Lean_Syntax_isOfKind(v___x_849_, v___x_851_);
if (v___x_852_ == 0)
{
lean_object* v___x_853_; lean_object* v___x_854_; 
lean_dec(v___x_849_);
lean_dec(v___x_683_);
lean_del_object(v___x_667_);
lean_dec(v_cmdStx_657_);
v___x_853_ = lean_box(0);
v___x_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_854_, 0, v___x_853_);
return v___x_854_;
}
else
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; uint8_t v___x_859_; 
v___x_855_ = l_Lean_Syntax_getArg(v___x_849_, v___x_844_);
lean_dec(v___x_849_);
v___x_856_ = l_Lean_Syntax_getArgs(v___x_855_);
lean_dec(v___x_855_);
v___x_857_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__19));
v___x_858_ = lean_array_get_size(v___x_856_);
v___x_859_ = lean_nat_dec_lt(v___x_682_, v___x_858_);
if (v___x_859_ == 0)
{
lean_dec_ref(v___x_856_);
v___y_687_ = v___x_850_;
v___y_688_ = v___y_842_;
v___y_689_ = v___x_844_;
v___y_690_ = v___y_843_;
v___y_691_ = v___x_857_;
goto v___jp_686_;
}
else
{
lean_object* v___x_860_; lean_object* v___x_861_; size_t v___x_862_; size_t v___x_863_; lean_object* v___x_864_; lean_object* v_snd_865_; 
v___x_860_ = lean_box(v___x_859_);
v___x_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_861_, 0, v___x_860_);
lean_ctor_set(v___x_861_, 1, v___x_857_);
v___x_862_ = ((size_t)0ULL);
v___x_863_ = lean_usize_of_nat(v___x_858_);
v___x_864_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__6(v___x_852_, v___x_856_, v___x_862_, v___x_863_, v___x_861_);
lean_dec_ref(v___x_856_);
v_snd_865_ = lean_ctor_get(v___x_864_, 1);
lean_inc(v_snd_865_);
lean_dec_ref(v___x_864_);
v___y_687_ = v___x_850_;
v___y_688_ = v___y_842_;
v___y_689_ = v___x_844_;
v___y_690_ = v___y_843_;
v___y_691_ = v_snd_865_;
goto v___jp_686_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___boxed(lean_object* v_cmdStx_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0(v_cmdStx_880_, v___y_881_, v___y_882_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0(lean_object* v_o_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0___redArg(v_o_894_, v___y_896_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0___boxed(lean_object* v_o_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0(v_o_899_, v___y_900_, v___y_901_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9(lean_object* v_msgData_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg(v_msgData_904_, v___y_906_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___boxed(lean_object* v_msgData_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9(v_msgData_909_, v___y_910_, v___y_911_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1774244096____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_915_ = ((lean_object*)(l_Lean_Linter_suspiciousUnexpanderPatterns));
v___x_916_ = l_Lean_Elab_Command_addLinter(v___x_915_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1774244096____hygCtx___hyg_2____boxed(lean_object* v_a_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1774244096____hygCtx___hyg_2_();
return v_res_918_;
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
