// Lean compiler output
// Module: Lean.Linter.Omit
// Imports: public import Lean.Elab.Command public import Lean.Linter.Util
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
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
extern lean_object* l_Lean_Linter_linterSetsExt;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_find_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
extern lean_object* l_Lean_Linter_linterMessageTag;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addLinter(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "omit"};
static const lean_object* l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(132, 183, 65, 118, 154, 36, 61, 16)}};
static const lean_object* l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "enable the 'avoid omit' linter"};
static const lean_object* l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(53, 243, 121, 207, 53, 172, 203, 87)}};
static const lean_ctor_object l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(23, 130, 79, 90, 33, 7, 55, 222)}};
static const lean_object* l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_linter_omit;
static const lean_string_object l_Lean_Linter_omit___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Linter_omit___lam__0___closed__0 = (const lean_object*)&l_Lean_Linter_omit___lam__0___closed__0_value;
static const lean_string_object l_Lean_Linter_omit___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Linter_omit___lam__0___closed__1 = (const lean_object*)&l_Lean_Linter_omit___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Linter_omit___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_omit___lam__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_omit___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_Linter_omit___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Linter_omit___lam__0___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_omit___lam__0___closed__2_value_aux_1),((lean_object*)&l_Lean_Linter_omit___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Linter_omit___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_omit___lam__0___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(248, 151, 249, 80, 160, 104, 42, 249)}};
static const lean_object* l_Lean_Linter_omit___lam__0___closed__2 = (const lean_object*)&l_Lean_Linter_omit___lam__0___closed__2_value;
LEAN_EXPORT uint8_t l_Lean_Linter_omit___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_omit___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "This linter can be disabled with `set_option "};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__0 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__0_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__1;
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " false`"};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__2 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__2_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_omit___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 80, .m_capacity = 80, .m_length = 79, .m_data = "`omit` should be avoided in favor of restructuring your `variable` declarations"};
static const lean_object* l_Lean_Linter_omit___lam__1___closed__0 = (const lean_object*)&l_Lean_Linter_omit___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Linter_omit___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_omit___lam__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Linter_omit___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_omit___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Linter_omit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_omit___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_omit___closed__0 = (const lean_object*)&l_Lean_Linter_omit___closed__0_value;
static const lean_closure_object l_Lean_Linter_omit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_omit___lam__1___boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Linter_omit___closed__0_value)} };
static const lean_object* l_Lean_Linter_omit___closed__1 = (const lean_object*)&l_Lean_Linter_omit___closed__1_value;
static const lean_ctor_object l_Lean_Linter_omit___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_omit___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_omit___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_Lean_Linter_omit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_omit___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(126, 195, 61, 10, 88, 123, 229, 39)}};
static const lean_object* l_Lean_Linter_omit___closed__2 = (const lean_object*)&l_Lean_Linter_omit___closed__2_value;
static const lean_ctor_object l_Lean_Linter_omit___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Linter_omit___closed__1_value),((lean_object*)&l_Lean_Linter_omit___closed__2_value)}};
static const lean_object* l_Lean_Linter_omit___closed__3 = (const lean_object*)&l_Lean_Linter_omit___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_omit = (const lean_object*)&l_Lean_Linter_omit___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3756037646____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3756037646____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_53_ = ((lean_object*)(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_));
v___x_54_ = ((lean_object*)(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_));
v___x_55_ = ((lean_object*)(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_));
v___x_56_ = l_Lean_Option_register___at___00__private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__spec__0(v___x_53_, v___x_54_, v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4____boxed(lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l___private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_();
return v_res_58_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_omit___lam__0(lean_object* v_x_66_){
_start:
{
lean_object* v___x_67_; uint8_t v___x_68_; 
v___x_67_ = ((lean_object*)(l_Lean_Linter_omit___lam__0___closed__2));
v___x_68_ = l_Lean_Syntax_isOfKind(v_x_66_, v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_omit___lam__0___boxed(lean_object* v_x_69_){
_start:
{
uint8_t v_res_70_; lean_object* v_r_71_; 
v_res_70_ = l_Lean_Linter_omit___lam__0(v_x_69_);
v_r_71_ = lean_box(v_res_70_);
return v_r_71_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__5(lean_object* v_opts_72_, lean_object* v_opt_73_){
_start:
{
lean_object* v_name_74_; lean_object* v_defValue_75_; lean_object* v_map_76_; lean_object* v___x_77_; 
v_name_74_ = lean_ctor_get(v_opt_73_, 0);
v_defValue_75_ = lean_ctor_get(v_opt_73_, 1);
v_map_76_ = lean_ctor_get(v_opts_72_, 0);
v___x_77_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_76_, v_name_74_);
if (lean_obj_tag(v___x_77_) == 0)
{
uint8_t v___x_78_; 
v___x_78_ = lean_unbox(v_defValue_75_);
return v___x_78_;
}
else
{
lean_object* v_val_79_; 
v_val_79_ = lean_ctor_get(v___x_77_, 0);
lean_inc(v_val_79_);
lean_dec_ref_known(v___x_77_, 1);
if (lean_obj_tag(v_val_79_) == 1)
{
uint8_t v_v_80_; 
v_v_80_ = lean_ctor_get_uint8(v_val_79_, 0);
lean_dec_ref_known(v_val_79_, 0);
return v_v_80_;
}
else
{
uint8_t v___x_81_; 
lean_dec(v_val_79_);
v___x_81_ = lean_unbox(v_defValue_75_);
return v___x_81_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_opts_82_, lean_object* v_opt_83_){
_start:
{
uint8_t v_res_84_; lean_object* v_r_85_; 
v_res_84_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__5(v_opts_82_, v_opt_83_);
lean_dec_ref(v_opt_83_);
lean_dec_ref(v_opts_82_);
v_r_85_ = lean_box(v_res_84_);
return v_r_85_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_86_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_88_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
return v___x_88_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_89_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_90_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_91_ = lean_unsigned_to_nat(0u);
v___x_92_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
lean_ctor_set(v___x_92_, 1, v___x_91_);
lean_ctor_set(v___x_92_, 2, v___x_91_);
lean_ctor_set(v___x_92_, 3, v___x_91_);
lean_ctor_set(v___x_92_, 4, v___x_90_);
lean_ctor_set(v___x_92_, 5, v___x_90_);
lean_ctor_set(v___x_92_, 6, v___x_90_);
lean_ctor_set(v___x_92_, 7, v___x_90_);
lean_ctor_set(v___x_92_, 8, v___x_90_);
lean_ctor_set(v___x_92_, 9, v___x_90_);
lean_ctor_set(v___x_92_, 10, v___x_90_);
lean_ctor_set(v___x_92_, 11, v___x_89_);
return v___x_92_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_93_ = lean_unsigned_to_nat(32u);
v___x_94_ = lean_mk_empty_array_with_capacity(v___x_93_);
v___x_95_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
return v___x_95_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_96_ = ((size_t)5ULL);
v___x_97_ = lean_unsigned_to_nat(0u);
v___x_98_ = lean_unsigned_to_nat(32u);
v___x_99_ = lean_mk_empty_array_with_capacity(v___x_98_);
v___x_100_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_101_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set(v___x_101_, 1, v___x_99_);
lean_ctor_set(v___x_101_, 2, v___x_97_);
lean_ctor_set(v___x_101_, 3, v___x_97_);
lean_ctor_set_usize(v___x_101_, 4, v___x_96_);
return v___x_101_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_102_ = lean_box(1);
v___x_103_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_104_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_105_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
lean_ctor_set(v___x_105_, 1, v___x_103_);
lean_ctor_set(v___x_105_, 2, v___x_102_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msgData_106_, lean_object* v___y_107_){
_start:
{
lean_object* v___x_109_; lean_object* v_env_110_; uint8_t v___x_111_; lean_object* v_env_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v_scopes_115_; lean_object* v___x_116_; lean_object* v_opts_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_109_ = lean_st_ref_get(v___y_107_);
v_env_110_ = lean_ctor_get(v___x_109_, 0);
lean_inc_ref(v_env_110_);
lean_dec(v___x_109_);
v___x_111_ = 0;
v_env_112_ = l_Lean_Environment_setRecordingDeps(v_env_110_, v___x_111_);
v___x_113_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_114_ = lean_st_ref_get(v___y_107_);
v_scopes_115_ = lean_ctor_get(v___x_114_, 2);
lean_inc(v_scopes_115_);
lean_dec(v___x_114_);
v___x_116_ = l_List_head_x21___redArg(v___x_113_, v_scopes_115_);
lean_dec(v_scopes_115_);
v_opts_117_ = lean_ctor_get(v___x_116_, 1);
lean_inc_ref(v_opts_117_);
lean_dec(v___x_116_);
v___x_118_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_119_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_120_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_120_, 0, v_env_112_);
lean_ctor_set(v___x_120_, 1, v___x_118_);
lean_ctor_set(v___x_120_, 2, v___x_119_);
lean_ctor_set(v___x_120_, 3, v_opts_117_);
v___x_121_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
lean_ctor_set(v___x_121_, 1, v_msgData_106_);
v___x_122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_122_, 0, v___x_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msgData_123_, lean_object* v___y_124_, lean_object* v___y_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg(v_msgData_123_, v___y_124_);
lean_dec(v___y_124_);
return v_res_126_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___lam__0(uint8_t v_suppressElabErrors_128_, uint8_t v___y_129_, lean_object* v_x_130_){
_start:
{
if (lean_obj_tag(v_x_130_) == 1)
{
lean_object* v_pre_131_; 
v_pre_131_ = lean_ctor_get(v_x_130_, 0);
if (lean_obj_tag(v_pre_131_) == 0)
{
lean_object* v_str_132_; lean_object* v___x_133_; uint8_t v___x_134_; 
v_str_132_ = lean_ctor_get(v_x_130_, 1);
v___x_133_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___lam__0___closed__0));
v___x_134_ = lean_string_dec_eq(v_str_132_, v___x_133_);
if (v___x_134_ == 0)
{
return v___x_134_;
}
else
{
return v_suppressElabErrors_128_;
}
}
else
{
return v___y_129_;
}
}
else
{
return v___y_129_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___lam__0___boxed(lean_object* v_suppressElabErrors_135_, lean_object* v___y_136_, lean_object* v_x_137_){
_start:
{
uint8_t v_suppressElabErrors_boxed_138_; uint8_t v___y_3096__boxed_139_; uint8_t v_res_140_; lean_object* v_r_141_; 
v_suppressElabErrors_boxed_138_ = lean_unbox(v_suppressElabErrors_135_);
v___y_3096__boxed_139_ = lean_unbox(v___y_136_);
v_res_140_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___lam__0(v_suppressElabErrors_boxed_138_, v___y_3096__boxed_139_, v_x_137_);
lean_dec(v_x_137_);
v_r_141_ = lean_box(v_res_140_);
return v_r_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3(lean_object* v_ref_143_, lean_object* v_msgData_144_, uint8_t v_severity_145_, uint8_t v_isSilent_146_, lean_object* v___y_147_, lean_object* v___y_148_){
_start:
{
lean_object* v___y_151_; lean_object* v___y_152_; uint8_t v___y_153_; lean_object* v___y_154_; lean_object* v___y_155_; uint8_t v___y_156_; lean_object* v___y_157_; lean_object* v___y_158_; uint8_t v___y_216_; uint8_t v___y_217_; lean_object* v___y_218_; uint8_t v___y_219_; lean_object* v___y_220_; uint8_t v___y_244_; lean_object* v___y_245_; uint8_t v___y_246_; uint8_t v___y_247_; lean_object* v___y_248_; uint8_t v___y_252_; uint8_t v___y_253_; uint8_t v___y_254_; uint8_t v___x_269_; uint8_t v___y_271_; uint8_t v___y_272_; uint8_t v___y_273_; uint8_t v___y_275_; uint8_t v___x_287_; 
v___x_269_ = 2;
v___x_287_ = l_Lean_instBEqMessageSeverity_beq(v_severity_145_, v___x_269_);
if (v___x_287_ == 0)
{
v___y_275_ = v___x_287_;
goto v___jp_274_;
}
else
{
uint8_t v___x_288_; 
lean_inc_ref(v_msgData_144_);
v___x_288_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_144_);
v___y_275_ = v___x_288_;
goto v___jp_274_;
}
v___jp_150_:
{
lean_object* v___x_159_; 
v___x_159_ = l_Lean_Elab_Command_getScope___redArg(v___y_158_);
if (lean_obj_tag(v___x_159_) == 0)
{
lean_object* v_a_160_; lean_object* v_currNamespace_161_; lean_object* v___x_162_; 
v_a_160_ = lean_ctor_get(v___x_159_, 0);
lean_inc(v_a_160_);
lean_dec_ref_known(v___x_159_, 1);
v_currNamespace_161_ = lean_ctor_get(v_a_160_, 2);
lean_inc(v_currNamespace_161_);
lean_dec(v_a_160_);
v___x_162_ = l_Lean_Elab_Command_getScope___redArg(v___y_158_);
if (lean_obj_tag(v___x_162_) == 0)
{
lean_object* v_a_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_198_; 
v_a_163_ = lean_ctor_get(v___x_162_, 0);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_162_);
if (v_isSharedCheck_198_ == 0)
{
v___x_165_ = v___x_162_;
v_isShared_166_ = v_isSharedCheck_198_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_a_163_);
lean_dec(v___x_162_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_198_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v_openDecls_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v_env_172_; lean_object* v_messages_173_; lean_object* v_scopes_174_; lean_object* v_usedQuotCtxts_175_; lean_object* v_nextMacroScope_176_; lean_object* v_maxRecDepth_177_; lean_object* v_ngen_178_; lean_object* v_auxDeclNGen_179_; lean_object* v_infoState_180_; lean_object* v_traceState_181_; lean_object* v_snapshotTasks_182_; lean_object* v_prevLinterStates_183_; lean_object* v_codeQualityEntryTasks_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_197_; 
v_openDecls_167_ = lean_ctor_get(v_a_163_, 3);
lean_inc(v_openDecls_167_);
lean_dec(v_a_163_);
v___x_168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_168_, 0, v_currNamespace_161_);
lean_ctor_set(v___x_168_, 1, v_openDecls_167_);
v___x_169_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
lean_ctor_set(v___x_169_, 1, v___y_155_);
lean_inc_ref(v___y_152_);
lean_inc_ref(v___y_157_);
v___x_170_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_170_, 0, v___y_157_);
lean_ctor_set(v___x_170_, 1, v___y_151_);
lean_ctor_set(v___x_170_, 2, v___y_154_);
lean_ctor_set(v___x_170_, 3, v___y_152_);
lean_ctor_set(v___x_170_, 4, v___x_169_);
lean_ctor_set_uint8(v___x_170_, sizeof(void*)*5, v___y_153_);
lean_ctor_set_uint8(v___x_170_, sizeof(void*)*5 + 1, v___y_156_);
lean_ctor_set_uint8(v___x_170_, sizeof(void*)*5 + 2, v_isSilent_146_);
v___x_171_ = lean_st_ref_take(v___y_158_);
v_env_172_ = lean_ctor_get(v___x_171_, 0);
v_messages_173_ = lean_ctor_get(v___x_171_, 1);
v_scopes_174_ = lean_ctor_get(v___x_171_, 2);
v_usedQuotCtxts_175_ = lean_ctor_get(v___x_171_, 3);
v_nextMacroScope_176_ = lean_ctor_get(v___x_171_, 4);
v_maxRecDepth_177_ = lean_ctor_get(v___x_171_, 5);
v_ngen_178_ = lean_ctor_get(v___x_171_, 6);
v_auxDeclNGen_179_ = lean_ctor_get(v___x_171_, 7);
v_infoState_180_ = lean_ctor_get(v___x_171_, 8);
v_traceState_181_ = lean_ctor_get(v___x_171_, 9);
v_snapshotTasks_182_ = lean_ctor_get(v___x_171_, 10);
v_prevLinterStates_183_ = lean_ctor_get(v___x_171_, 11);
v_codeQualityEntryTasks_184_ = lean_ctor_get(v___x_171_, 12);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_197_ == 0)
{
v___x_186_ = v___x_171_;
v_isShared_187_ = v_isSharedCheck_197_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_codeQualityEntryTasks_184_);
lean_inc(v_prevLinterStates_183_);
lean_inc(v_snapshotTasks_182_);
lean_inc(v_traceState_181_);
lean_inc(v_infoState_180_);
lean_inc(v_auxDeclNGen_179_);
lean_inc(v_ngen_178_);
lean_inc(v_maxRecDepth_177_);
lean_inc(v_nextMacroScope_176_);
lean_inc(v_usedQuotCtxts_175_);
lean_inc(v_scopes_174_);
lean_inc(v_messages_173_);
lean_inc(v_env_172_);
lean_dec(v___x_171_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_197_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_191_; 
v___x_188_ = lean_box(0);
v___x_189_ = l_Lean_MessageLog_add(v___x_170_, v_messages_173_);
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 1, v___x_189_);
v___x_191_ = v___x_186_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_env_172_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v___x_189_);
lean_ctor_set(v_reuseFailAlloc_196_, 2, v_scopes_174_);
lean_ctor_set(v_reuseFailAlloc_196_, 3, v_usedQuotCtxts_175_);
lean_ctor_set(v_reuseFailAlloc_196_, 4, v_nextMacroScope_176_);
lean_ctor_set(v_reuseFailAlloc_196_, 5, v_maxRecDepth_177_);
lean_ctor_set(v_reuseFailAlloc_196_, 6, v_ngen_178_);
lean_ctor_set(v_reuseFailAlloc_196_, 7, v_auxDeclNGen_179_);
lean_ctor_set(v_reuseFailAlloc_196_, 8, v_infoState_180_);
lean_ctor_set(v_reuseFailAlloc_196_, 9, v_traceState_181_);
lean_ctor_set(v_reuseFailAlloc_196_, 10, v_snapshotTasks_182_);
lean_ctor_set(v_reuseFailAlloc_196_, 11, v_prevLinterStates_183_);
lean_ctor_set(v_reuseFailAlloc_196_, 12, v_codeQualityEntryTasks_184_);
v___x_191_ = v_reuseFailAlloc_196_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
lean_object* v___x_192_; lean_object* v___x_194_; 
v___x_192_ = lean_st_ref_put(v___y_158_, v___x_191_);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 0, v___x_188_);
v___x_194_ = v___x_165_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v___x_188_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
}
}
else
{
lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_206_; 
lean_dec(v_currNamespace_161_);
lean_dec_ref(v___y_155_);
lean_dec(v___y_154_);
lean_dec_ref(v___y_151_);
v_a_199_ = lean_ctor_get(v___x_162_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_162_);
if (v_isSharedCheck_206_ == 0)
{
v___x_201_ = v___x_162_;
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_162_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_204_; 
if (v_isShared_202_ == 0)
{
v___x_204_ = v___x_201_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_a_199_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
else
{
lean_object* v_a_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_214_; 
lean_dec_ref(v___y_155_);
lean_dec(v___y_154_);
lean_dec_ref(v___y_151_);
v_a_207_ = lean_ctor_get(v___x_159_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_214_ == 0)
{
v___x_209_ = v___x_159_;
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_a_207_);
lean_dec(v___x_159_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_212_; 
if (v_isShared_210_ == 0)
{
v___x_212_ = v___x_209_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_a_207_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
}
v___jp_215_:
{
lean_object* v_fileName_221_; lean_object* v_fileMap_222_; uint8_t v_suppressElabErrors_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___f_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v_a_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_242_; 
v_fileName_221_ = lean_ctor_get(v___y_147_, 0);
v_fileMap_222_ = lean_ctor_get(v___y_147_, 1);
v_suppressElabErrors_223_ = lean_ctor_get_uint8(v___y_147_, sizeof(void*)*10);
v___x_224_ = lean_box(v_suppressElabErrors_223_);
v___x_225_ = lean_box(v___y_216_);
v___f_226_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___lam__0___boxed), 3, 2);
lean_closure_set(v___f_226_, 0, v___x_224_);
lean_closure_set(v___f_226_, 1, v___x_225_);
v___x_227_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_144_);
v___x_228_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg(v___x_227_, v___y_148_);
v_a_229_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_242_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_242_ == 0)
{
v___x_231_ = v___x_228_;
v_isShared_232_ = v_isSharedCheck_242_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_a_229_);
lean_dec(v___x_228_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_242_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
lean_inc_ref_n(v_fileMap_222_, 2);
v___x_233_ = l_Lean_FileMap_toPosition(v_fileMap_222_, v___y_218_);
lean_dec(v___y_218_);
v___x_234_ = l_Lean_FileMap_toPosition(v_fileMap_222_, v___y_220_);
lean_dec(v___y_220_);
v___x_235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
v___x_236_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___closed__0));
if (v_suppressElabErrors_223_ == 0)
{
lean_del_object(v___x_231_);
lean_dec_ref(v___f_226_);
v___y_151_ = v___x_233_;
v___y_152_ = v___x_236_;
v___y_153_ = v___y_217_;
v___y_154_ = v___x_235_;
v___y_155_ = v_a_229_;
v___y_156_ = v___y_219_;
v___y_157_ = v_fileName_221_;
v___y_158_ = v___y_148_;
goto v___jp_150_;
}
else
{
uint8_t v___x_237_; 
lean_inc(v_a_229_);
v___x_237_ = l_Lean_MessageData_hasTag(v___f_226_, v_a_229_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; lean_object* v___x_240_; 
lean_dec_ref_known(v___x_235_, 1);
lean_dec_ref(v___x_233_);
lean_dec(v_a_229_);
v___x_238_ = lean_box(0);
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 0, v___x_238_);
v___x_240_ = v___x_231_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_238_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
else
{
lean_del_object(v___x_231_);
v___y_151_ = v___x_233_;
v___y_152_ = v___x_236_;
v___y_153_ = v___y_217_;
v___y_154_ = v___x_235_;
v___y_155_ = v_a_229_;
v___y_156_ = v___y_219_;
v___y_157_ = v_fileName_221_;
v___y_158_ = v___y_148_;
goto v___jp_150_;
}
}
}
}
v___jp_243_:
{
lean_object* v___x_249_; 
v___x_249_ = l_Lean_Syntax_getTailPos_x3f(v___y_245_, v___y_246_);
lean_dec(v___y_245_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_inc(v___y_248_);
v___y_216_ = v___y_244_;
v___y_217_ = v___y_246_;
v___y_218_ = v___y_248_;
v___y_219_ = v___y_247_;
v___y_220_ = v___y_248_;
goto v___jp_215_;
}
else
{
lean_object* v_val_250_; 
v_val_250_ = lean_ctor_get(v___x_249_, 0);
lean_inc(v_val_250_);
lean_dec_ref_known(v___x_249_, 1);
v___y_216_ = v___y_244_;
v___y_217_ = v___y_246_;
v___y_218_ = v___y_248_;
v___y_219_ = v___y_247_;
v___y_220_ = v_val_250_;
goto v___jp_215_;
}
}
v___jp_251_:
{
lean_object* v___x_255_; 
v___x_255_ = l_Lean_Elab_Command_getRef___redArg(v___y_147_);
if (lean_obj_tag(v___x_255_) == 0)
{
lean_object* v_a_256_; lean_object* v_ref_257_; lean_object* v___x_258_; 
v_a_256_ = lean_ctor_get(v___x_255_, 0);
lean_inc(v_a_256_);
lean_dec_ref_known(v___x_255_, 1);
v_ref_257_ = l_Lean_replaceRef(v_ref_143_, v_a_256_);
lean_dec(v_a_256_);
v___x_258_ = l_Lean_Syntax_getPos_x3f(v_ref_257_, v___y_253_);
if (lean_obj_tag(v___x_258_) == 0)
{
lean_object* v___x_259_; 
v___x_259_ = lean_unsigned_to_nat(0u);
v___y_244_ = v___y_252_;
v___y_245_ = v_ref_257_;
v___y_246_ = v___y_253_;
v___y_247_ = v___y_254_;
v___y_248_ = v___x_259_;
goto v___jp_243_;
}
else
{
lean_object* v_val_260_; 
v_val_260_ = lean_ctor_get(v___x_258_, 0);
lean_inc(v_val_260_);
lean_dec_ref_known(v___x_258_, 1);
v___y_244_ = v___y_252_;
v___y_245_ = v_ref_257_;
v___y_246_ = v___y_253_;
v___y_247_ = v___y_254_;
v___y_248_ = v_val_260_;
goto v___jp_243_;
}
}
else
{
lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_268_; 
lean_dec_ref(v_msgData_144_);
v_a_261_ = lean_ctor_get(v___x_255_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_268_ == 0)
{
v___x_263_ = v___x_255_;
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v___x_255_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_266_; 
if (v_isShared_264_ == 0)
{
v___x_266_ = v___x_263_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_a_261_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
}
v___jp_270_:
{
if (v___y_273_ == 0)
{
v___y_252_ = v___y_271_;
v___y_253_ = v___y_272_;
v___y_254_ = v_severity_145_;
goto v___jp_251_;
}
else
{
v___y_252_ = v___y_271_;
v___y_253_ = v___y_272_;
v___y_254_ = v___x_269_;
goto v___jp_251_;
}
}
v___jp_274_:
{
if (v___y_275_ == 0)
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v_scopes_278_; lean_object* v___x_279_; lean_object* v_opts_280_; uint8_t v___x_281_; uint8_t v___x_282_; 
v___x_276_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_277_ = lean_st_ref_get(v___y_148_);
v_scopes_278_ = lean_ctor_get(v___x_277_, 2);
lean_inc(v_scopes_278_);
lean_dec(v___x_277_);
v___x_279_ = l_List_head_x21___redArg(v___x_276_, v_scopes_278_);
lean_dec(v_scopes_278_);
v_opts_280_ = lean_ctor_get(v___x_279_, 1);
lean_inc_ref(v_opts_280_);
lean_dec(v___x_279_);
v___x_281_ = 1;
v___x_282_ = l_Lean_instBEqMessageSeverity_beq(v_severity_145_, v___x_281_);
if (v___x_282_ == 0)
{
lean_dec_ref(v_opts_280_);
v___y_271_ = v___y_275_;
v___y_272_ = v___y_275_;
v___y_273_ = v___x_282_;
goto v___jp_270_;
}
else
{
lean_object* v___x_283_; uint8_t v___x_284_; 
v___x_283_ = l_Lean_warningAsError;
v___x_284_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__5(v_opts_280_, v___x_283_);
lean_dec_ref(v_opts_280_);
v___y_271_ = v___y_275_;
v___y_272_ = v___y_275_;
v___y_273_ = v___x_284_;
goto v___jp_270_;
}
}
else
{
lean_object* v___x_285_; lean_object* v___x_286_; 
lean_dec_ref(v_msgData_144_);
v___x_285_ = lean_box(0);
v___x_286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
return v___x_286_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___boxed(lean_object* v_ref_289_, lean_object* v_msgData_290_, lean_object* v_severity_291_, lean_object* v_isSilent_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
uint8_t v_severity_boxed_296_; uint8_t v_isSilent_boxed_297_; lean_object* v_res_298_; 
v_severity_boxed_296_ = lean_unbox(v_severity_291_);
v_isSilent_boxed_297_ = lean_unbox(v_isSilent_292_);
v_res_298_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3(v_ref_289_, v_msgData_290_, v_severity_boxed_296_, v_isSilent_boxed_297_, v___y_293_, v___y_294_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
lean_dec(v_ref_289_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2(lean_object* v_ref_299_, lean_object* v_msgData_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
uint8_t v___x_304_; uint8_t v___x_305_; lean_object* v___x_306_; 
v___x_304_ = 1;
v___x_305_ = 0;
v___x_306_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3(v_ref_299_, v_msgData_300_, v___x_304_, v___x_305_, v___y_301_, v___y_302_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2___boxed(lean_object* v_ref_307_, lean_object* v_msgData_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2(v_ref_307_, v_msgData_308_, v___y_309_, v___y_310_);
lean_dec(v___y_310_);
lean_dec_ref(v___y_309_);
lean_dec(v_ref_307_);
return v_res_312_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__1(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__0));
v___x_315_ = l_Lean_stringToMessageData(v___x_314_);
return v___x_315_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__3(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__2));
v___x_318_ = l_Lean_stringToMessageData(v___x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1(lean_object* v_linterOption_319_, lean_object* v_stx_320_, lean_object* v_msg_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
lean_object* v_name_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_343_; 
v_name_325_ = lean_ctor_get(v_linterOption_319_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v_linterOption_319_);
if (v_isSharedCheck_343_ == 0)
{
lean_object* v_unused_344_; 
v_unused_344_ = lean_ctor_get(v_linterOption_319_, 1);
lean_dec(v_unused_344_);
v___x_327_ = v_linterOption_319_;
v_isShared_328_ = v_isSharedCheck_343_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_name_325_);
lean_dec(v_linterOption_319_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_343_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_332_; 
v___x_329_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__1);
lean_inc(v_name_325_);
v___x_330_ = l_Lean_MessageData_ofName(v_name_325_);
if (v_isShared_328_ == 0)
{
lean_ctor_set_tag(v___x_327_, 7);
lean_ctor_set(v___x_327_, 1, v___x_330_);
lean_ctor_set(v___x_327_, 0, v___x_329_);
v___x_332_ = v___x_327_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_329_);
lean_ctor_set(v_reuseFailAlloc_342_, 1, v___x_330_);
v___x_332_ = v_reuseFailAlloc_342_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v_disable_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_333_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__3);
v___x_334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_334_, 0, v___x_332_);
lean_ctor_set(v___x_334_, 1, v___x_333_);
v_disable_335_ = l_Lean_MessageData_note(v___x_334_);
v___x_336_ = l_Lean_Linter_linterMessageTag;
v___x_337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_337_, 0, v_msg_321_);
lean_ctor_set(v___x_337_, 1, v_disable_335_);
v___x_338_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_336_);
lean_ctor_set(v___x_338_, 1, v___x_337_);
v___x_339_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_339_, 0, v_name_325_);
lean_ctor_set(v___x_339_, 1, v___x_338_);
lean_inc(v_stx_320_);
v___x_340_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_340_, 0, v_stx_320_);
lean_ctor_set(v___x_340_, 1, v___x_339_);
v___x_341_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2(v_stx_320_, v___x_340_, v___y_322_, v___y_323_);
lean_dec(v_stx_320_);
return v___x_341_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___boxed(lean_object* v_linterOption_345_, lean_object* v_stx_346_, lean_object* v_msg_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1(v_linterOption_345_, v_stx_346_, v_msg_347_, v___y_348_, v___y_349_);
lean_dec(v___y_349_);
lean_dec_ref(v___y_348_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0___redArg(lean_object* v_o_352_, lean_object* v___y_353_){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v_env_357_; lean_object* v___x_358_; lean_object* v_toEnvExtension_359_; lean_object* v_asyncMode_360_; lean_object* v___x_361_; uint8_t v___x_362_; lean_object* v___x_363_; lean_object* v_merged_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_372_; 
v___x_355_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_356_ = lean_st_ref_get(v___y_353_);
v_env_357_ = lean_ctor_get(v___x_356_, 0);
lean_inc_ref(v_env_357_);
lean_dec(v___x_356_);
v___x_358_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_359_ = lean_ctor_get(v___x_358_, 0);
v_asyncMode_360_ = lean_ctor_get(v_toEnvExtension_359_, 2);
v___x_361_ = lean_box(0);
v___x_362_ = 0;
v___x_363_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_355_, v___x_358_, v_env_357_, v_asyncMode_360_, v___x_361_, v___x_362_);
v_merged_364_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_372_ == 0)
{
lean_object* v_unused_373_; 
v_unused_373_ = lean_ctor_get(v___x_363_, 1);
lean_dec(v_unused_373_);
v___x_366_ = v___x_363_;
v_isShared_367_ = v_isSharedCheck_372_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_merged_364_);
lean_dec(v___x_363_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_372_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_369_; 
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 1, v_merged_364_);
lean_ctor_set(v___x_366_, 0, v_o_352_);
v___x_369_ = v___x_366_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_o_352_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v_merged_364_);
v___x_369_ = v_reuseFailAlloc_371_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
lean_object* v___x_370_; 
v___x_370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
return v___x_370_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0___redArg___boxed(lean_object* v_o_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0___redArg(v_o_374_, v___y_375_);
lean_dec(v___y_375_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0(lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v_scopes_383_; lean_object* v___x_384_; lean_object* v_opts_385_; lean_object* v___x_386_; 
v___x_381_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_382_ = lean_st_ref_get(v___y_379_);
v_scopes_383_ = lean_ctor_get(v___x_382_, 2);
lean_inc(v_scopes_383_);
lean_dec(v___x_382_);
v___x_384_ = l_List_head_x21___redArg(v___x_381_, v_scopes_383_);
lean_dec(v_scopes_383_);
v_opts_385_ = lean_ctor_get(v___x_384_, 1);
lean_inc_ref(v_opts_385_);
lean_dec(v___x_384_);
v___x_386_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0___redArg(v_opts_385_, v___y_379_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0___boxed(lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0(v___y_387_, v___y_388_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
return v_res_390_;
}
}
static lean_object* _init_l_Lean_Linter_omit___lam__1___closed__1(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = ((lean_object*)(l_Lean_Linter_omit___lam__1___closed__0));
v___x_393_ = l_Lean_stringToMessageData(v___x_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_omit___lam__1(lean_object* v___f_394_, lean_object* v_stx_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v___x_399_; lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_418_; 
v___x_399_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0(v___y_396_, v___y_397_);
v_a_400_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_418_ == 0)
{
v___x_402_ = v___x_399_;
v_isShared_403_ = v_isSharedCheck_418_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_399_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_418_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_404_; uint8_t v___x_405_; 
v___x_404_ = l_Lean_Linter_linter_omit;
v___x_405_ = l_Lean_Linter_getLinterValue(v___x_404_, v_a_400_);
lean_dec(v_a_400_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; lean_object* v___x_408_; 
lean_dec(v_stx_395_);
lean_dec_ref(v___f_394_);
v___x_406_ = lean_box(0);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 0, v___x_406_);
v___x_408_ = v___x_402_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_406_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
else
{
lean_object* v___x_410_; 
v___x_410_ = l_Lean_Syntax_find_x3f(v_stx_395_, v___f_394_);
if (lean_obj_tag(v___x_410_) == 1)
{
lean_object* v_val_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
lean_del_object(v___x_402_);
v_val_411_ = lean_ctor_get(v___x_410_, 0);
lean_inc(v_val_411_);
lean_dec_ref_known(v___x_410_, 1);
v___x_412_ = lean_obj_once(&l_Lean_Linter_omit___lam__1___closed__1, &l_Lean_Linter_omit___lam__1___closed__1_once, _init_l_Lean_Linter_omit___lam__1___closed__1);
v___x_413_ = l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1(v___x_404_, v_val_411_, v___x_412_, v___y_396_, v___y_397_);
return v___x_413_;
}
else
{
lean_object* v___x_414_; lean_object* v___x_416_; 
lean_dec(v___x_410_);
v___x_414_ = lean_box(0);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 0, v___x_414_);
v___x_416_ = v___x_402_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_414_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_omit___lam__1___boxed(lean_object* v___f_419_, lean_object* v_stx_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Lean_Linter_omit___lam__1(v___f_419_, v_stx_420_, v___y_421_, v___y_422_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0(lean_object* v_o_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
lean_object* v___x_440_; 
v___x_440_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0___redArg(v_o_436_, v___y_438_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0___boxed(lean_object* v_o_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0(v_o_441_, v___y_442_, v___y_443_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4(lean_object* v_msgData_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg(v_msgData_446_, v___y_448_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msgData_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4(v_msgData_451_, v___y_452_, v___y_453_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3756037646____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_457_ = ((lean_object*)(l_Lean_Linter_omit));
v___x_458_ = l_Lean_Elab_Command_addLinter(v___x_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3756037646____hygCtx___hyg_2____boxed(lean_object* v_a_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l___private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3756037646____hygCtx___hyg_2_();
return v_res_460_;
}
}
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_Omit(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_linter_omit = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_linter_omit);
lean_dec_ref(res);
res = l___private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3756037646____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Linter_Omit(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* initialize_Lean_Linter_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Linter_Omit(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Omit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Linter_Omit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Linter_Omit(builtin);
}
#ifdef __cplusplus
}
#endif
