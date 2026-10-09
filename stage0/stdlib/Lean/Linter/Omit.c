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
lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1_ = stack[0].m_obj;
lean_object* v_decl_2_ = stack[1].m_obj;
lean_object* v_ref_3_ = stack[2].m_obj;
lean_object* v_res_29_;
v_res_29_ = l_Lean_Option_register___at___00__private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__spec__0(v_name_1_, v_decl_2_, v_ref_3_);
stack->m_obj
 = v_res_29_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_30_, lean_object* v_decl_31_, lean_object* v_ref_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Option_register___at___00__private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__spec__0(v_name_30_, v_decl_31_, v_ref_32_);
lean_dec_ref(v_decl_31_);
return v_res_34_;
}
}
lean_object* l___private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_54_ = ((lean_object*)(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_));
v___x_55_ = ((lean_object*)(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_));
v___x_56_ = ((lean_object*)(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_));
v___x_57_ = l_Lean_Option_register___at___00__private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__spec__0(v___x_54_, v___x_55_, v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT void l___private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_58_;
v_res_58_ = l___private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_();
stack->m_obj
 = v_res_58_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4____boxed(lean_object* v_a_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l___private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_();
return v_res_60_;
}
}
uint8_t l_Lean_Linter_omit___lam__0(lean_object* v_x_68_){
_start:
{
lean_object* v___x_69_; uint8_t v___x_70_; 
v___x_69_ = ((lean_object*)(l_Lean_Linter_omit___lam__0___closed__2));
v___x_70_ = l_Lean_Syntax_isOfKind(v_x_68_, v___x_69_);
return v___x_70_;
}
}
LEAN_EXPORT void l_Lean_Linter_omit___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_68_ = stack[0].m_obj;
uint8_t v_res_71_;
v_res_71_ = l_Lean_Linter_omit___lam__0(v_x_68_);
stack->m_num = v_res_71_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_omit___lam__0___boxed(lean_object* v_x_72_){
_start:
{
uint8_t v_res_73_; lean_object* v_r_74_; 
v_res_73_ = l_Lean_Linter_omit___lam__0(v_x_72_);
v_r_74_ = lean_box(v_res_73_);
return v_r_74_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__5(lean_object* v_opts_75_, lean_object* v_opt_76_){
_start:
{
lean_object* v_name_77_; lean_object* v_defValue_78_; lean_object* v_map_79_; lean_object* v___x_80_; 
v_name_77_ = lean_ctor_get(v_opt_76_, 0);
v_defValue_78_ = lean_ctor_get(v_opt_76_, 1);
v_map_79_ = lean_ctor_get(v_opts_75_, 0);
v___x_80_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_79_, v_name_77_);
if (lean_obj_tag(v___x_80_) == 0)
{
uint8_t v___x_81_; 
v___x_81_ = lean_unbox(v_defValue_78_);
return v___x_81_;
}
else
{
lean_object* v_val_82_; 
v_val_82_ = lean_ctor_get(v___x_80_, 0);
lean_inc(v_val_82_);
lean_dec_ref_known(v___x_80_, 1);
if (lean_obj_tag(v_val_82_) == 1)
{
uint8_t v_v_83_; 
v_v_83_ = lean_ctor_get_uint8(v_val_82_, 0);
lean_dec_ref_known(v_val_82_, 0);
return v_v_83_;
}
else
{
uint8_t v___x_84_; 
lean_dec(v_val_82_);
v___x_84_ = lean_unbox(v_defValue_78_);
return v___x_84_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_75_ = stack[0].m_obj;
lean_object* v_opt_76_ = stack[1].m_obj;
uint8_t v_res_85_;
v_res_85_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__5(v_opts_75_, v_opt_76_);
stack->m_num = v_res_85_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_opts_86_, lean_object* v_opt_87_){
_start:
{
uint8_t v_res_88_; lean_object* v_r_89_; 
v_res_88_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__5(v_opts_86_, v_opt_87_);
lean_dec_ref(v_opt_87_);
lean_dec_ref(v_opts_86_);
v_r_89_ = lean_box(v_res_88_);
return v_r_89_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_90_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_92_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
return v___x_92_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_93_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_94_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_95_ = lean_unsigned_to_nat(0u);
v___x_96_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
lean_ctor_set(v___x_96_, 1, v___x_95_);
lean_ctor_set(v___x_96_, 2, v___x_95_);
lean_ctor_set(v___x_96_, 3, v___x_95_);
lean_ctor_set(v___x_96_, 4, v___x_94_);
lean_ctor_set(v___x_96_, 5, v___x_94_);
lean_ctor_set(v___x_96_, 6, v___x_94_);
lean_ctor_set(v___x_96_, 7, v___x_94_);
lean_ctor_set(v___x_96_, 8, v___x_94_);
lean_ctor_set(v___x_96_, 9, v___x_94_);
lean_ctor_set(v___x_96_, 10, v___x_94_);
lean_ctor_set(v___x_96_, 11, v___x_93_);
return v___x_96_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_97_ = lean_unsigned_to_nat(32u);
v___x_98_ = lean_mk_empty_array_with_capacity(v___x_97_);
v___x_99_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
return v___x_99_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_100_ = ((size_t)5ULL);
v___x_101_ = lean_unsigned_to_nat(0u);
v___x_102_ = lean_unsigned_to_nat(32u);
v___x_103_ = lean_mk_empty_array_with_capacity(v___x_102_);
v___x_104_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_105_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_105_, 0, v___x_104_);
lean_ctor_set(v___x_105_, 1, v___x_103_);
lean_ctor_set(v___x_105_, 2, v___x_101_);
lean_ctor_set(v___x_105_, 3, v___x_101_);
lean_ctor_set_usize(v___x_105_, 4, v___x_100_);
return v___x_105_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_106_ = lean_box(1);
v___x_107_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_108_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_109_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
lean_ctor_set(v___x_109_, 1, v___x_107_);
lean_ctor_set(v___x_109_, 2, v___x_106_);
return v___x_109_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msgData_110_, lean_object* v___y_111_){
_start:
{
lean_object* v___x_113_; lean_object* v_env_114_; uint8_t v___x_115_; lean_object* v_env_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v_scopes_119_; lean_object* v___x_120_; lean_object* v_opts_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_113_ = lean_st_ref_get(v___y_111_);
v_env_114_ = lean_ctor_get(v___x_113_, 0);
lean_inc_ref(v_env_114_);
lean_dec(v___x_113_);
v___x_115_ = 0;
v_env_116_ = l_Lean_Environment_setRecordingDeps(v_env_114_, v___x_115_);
v___x_117_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_118_ = lean_st_ref_get(v___y_111_);
v_scopes_119_ = lean_ctor_get(v___x_118_, 2);
lean_inc(v_scopes_119_);
lean_dec(v___x_118_);
v___x_120_ = l_List_head_x21___redArg(v___x_117_, v_scopes_119_);
lean_dec(v_scopes_119_);
v_opts_121_ = lean_ctor_get(v___x_120_, 1);
lean_inc_ref(v_opts_121_);
lean_dec(v___x_120_);
v___x_122_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_123_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_124_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_124_, 0, v_env_116_);
lean_ctor_set(v___x_124_, 1, v___x_122_);
lean_ctor_set(v___x_124_, 2, v___x_123_);
lean_ctor_set(v___x_124_, 3, v_opts_121_);
v___x_125_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_125_, 0, v___x_124_);
lean_ctor_set(v___x_125_, 1, v_msgData_110_);
v___x_126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
return v___x_126_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_110_ = stack[0].m_obj;
lean_object* v___y_111_ = stack[1].m_obj;
lean_object* v_res_127_;
v_res_127_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg(v_msgData_110_, v___y_111_);
stack->m_obj
 = v_res_127_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msgData_128_, lean_object* v___y_129_, lean_object* v___y_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg(v_msgData_128_, v___y_129_);
lean_dec(v___y_129_);
return v_res_131_;
}
}
uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___lam__0(uint8_t v_suppressElabErrors_133_, uint8_t v___y_134_, lean_object* v_x_135_){
_start:
{
if (lean_obj_tag(v_x_135_) == 1)
{
lean_object* v_pre_136_; 
v_pre_136_ = lean_ctor_get(v_x_135_, 0);
if (lean_obj_tag(v_pre_136_) == 0)
{
lean_object* v_str_137_; lean_object* v___x_138_; uint8_t v___x_139_; 
v_str_137_ = lean_ctor_get(v_x_135_, 1);
v___x_138_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___lam__0___closed__0));
v___x_139_ = lean_string_dec_eq(v_str_137_, v___x_138_);
if (v___x_139_ == 0)
{
return v___x_139_;
}
else
{
return v_suppressElabErrors_133_;
}
}
else
{
return v___y_134_;
}
}
else
{
return v___y_134_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_133_ = stack[0].m_num;
uint8_t v___y_134_ = stack[1].m_num;
lean_object* v_x_135_ = stack[2].m_obj;
uint8_t v_res_140_;
v_res_140_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___lam__0(v_suppressElabErrors_133_, v___y_134_, v_x_135_);
stack->m_num = v_res_140_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___lam__0___boxed(lean_object* v_suppressElabErrors_141_, lean_object* v___y_142_, lean_object* v_x_143_){
_start:
{
uint8_t v_suppressElabErrors_boxed_144_; uint8_t v___y_3146__boxed_145_; uint8_t v_res_146_; lean_object* v_r_147_; 
v_suppressElabErrors_boxed_144_ = lean_unbox(v_suppressElabErrors_141_);
v___y_3146__boxed_145_ = lean_unbox(v___y_142_);
v_res_146_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___lam__0(v_suppressElabErrors_boxed_144_, v___y_3146__boxed_145_, v_x_143_);
lean_dec(v_x_143_);
v_r_147_ = lean_box(v_res_146_);
return v_r_147_;
}
}
lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3(lean_object* v_ref_149_, lean_object* v_msgData_150_, uint8_t v_severity_151_, uint8_t v_isSilent_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
lean_object* v___y_157_; lean_object* v___y_158_; uint8_t v___y_159_; lean_object* v___y_160_; lean_object* v___y_161_; uint8_t v___y_162_; lean_object* v___y_163_; lean_object* v___y_164_; uint8_t v___y_222_; uint8_t v___y_223_; lean_object* v___y_224_; uint8_t v___y_225_; lean_object* v___y_226_; uint8_t v___y_250_; lean_object* v___y_251_; uint8_t v___y_252_; uint8_t v___y_253_; lean_object* v___y_254_; uint8_t v___y_258_; uint8_t v___y_259_; uint8_t v___y_260_; uint8_t v___x_275_; uint8_t v___y_277_; uint8_t v___y_278_; uint8_t v___y_279_; uint8_t v___y_281_; uint8_t v___x_293_; 
v___x_275_ = 2;
v___x_293_ = l_Lean_instBEqMessageSeverity_beq(v_severity_151_, v___x_275_);
if (v___x_293_ == 0)
{
v___y_281_ = v___x_293_;
goto v___jp_280_;
}
else
{
uint8_t v___x_294_; 
lean_inc_ref(v_msgData_150_);
v___x_294_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_150_);
v___y_281_ = v___x_294_;
goto v___jp_280_;
}
v___jp_156_:
{
lean_object* v___x_165_; 
v___x_165_ = l_Lean_Elab_Command_getScope___redArg(v___y_164_);
if (lean_obj_tag(v___x_165_) == 0)
{
lean_object* v_a_166_; lean_object* v_currNamespace_167_; lean_object* v___x_168_; 
v_a_166_ = lean_ctor_get(v___x_165_, 0);
lean_inc(v_a_166_);
lean_dec_ref_known(v___x_165_, 1);
v_currNamespace_167_ = lean_ctor_get(v_a_166_, 2);
lean_inc(v_currNamespace_167_);
lean_dec(v_a_166_);
v___x_168_ = l_Lean_Elab_Command_getScope___redArg(v___y_164_);
if (lean_obj_tag(v___x_168_) == 0)
{
lean_object* v_a_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_204_; 
v_a_169_ = lean_ctor_get(v___x_168_, 0);
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_168_);
if (v_isSharedCheck_204_ == 0)
{
v___x_171_ = v___x_168_;
v_isShared_172_ = v_isSharedCheck_204_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_a_169_);
lean_dec(v___x_168_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_204_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v_openDecls_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v_env_178_; lean_object* v_messages_179_; lean_object* v_scopes_180_; lean_object* v_usedQuotCtxts_181_; lean_object* v_nextMacroScope_182_; lean_object* v_maxRecDepth_183_; lean_object* v_ngen_184_; lean_object* v_auxDeclNGen_185_; lean_object* v_infoState_186_; lean_object* v_traceState_187_; lean_object* v_snapshotTasks_188_; lean_object* v_prevLinterStates_189_; lean_object* v_codeQualityEntryTasks_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_203_; 
v_openDecls_173_ = lean_ctor_get(v_a_169_, 3);
lean_inc(v_openDecls_173_);
lean_dec(v_a_169_);
v___x_174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_174_, 0, v_currNamespace_167_);
lean_ctor_set(v___x_174_, 1, v_openDecls_173_);
v___x_175_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
lean_ctor_set(v___x_175_, 1, v___y_161_);
lean_inc_ref(v___y_158_);
lean_inc_ref(v___y_163_);
v___x_176_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_176_, 0, v___y_163_);
lean_ctor_set(v___x_176_, 1, v___y_157_);
lean_ctor_set(v___x_176_, 2, v___y_160_);
lean_ctor_set(v___x_176_, 3, v___y_158_);
lean_ctor_set(v___x_176_, 4, v___x_175_);
lean_ctor_set_uint8(v___x_176_, sizeof(void*)*5, v___y_159_);
lean_ctor_set_uint8(v___x_176_, sizeof(void*)*5 + 1, v___y_162_);
lean_ctor_set_uint8(v___x_176_, sizeof(void*)*5 + 2, v_isSilent_152_);
v___x_177_ = lean_st_ref_take(v___y_164_);
v_env_178_ = lean_ctor_get(v___x_177_, 0);
v_messages_179_ = lean_ctor_get(v___x_177_, 1);
v_scopes_180_ = lean_ctor_get(v___x_177_, 2);
v_usedQuotCtxts_181_ = lean_ctor_get(v___x_177_, 3);
v_nextMacroScope_182_ = lean_ctor_get(v___x_177_, 4);
v_maxRecDepth_183_ = lean_ctor_get(v___x_177_, 5);
v_ngen_184_ = lean_ctor_get(v___x_177_, 6);
v_auxDeclNGen_185_ = lean_ctor_get(v___x_177_, 7);
v_infoState_186_ = lean_ctor_get(v___x_177_, 8);
v_traceState_187_ = lean_ctor_get(v___x_177_, 9);
v_snapshotTasks_188_ = lean_ctor_get(v___x_177_, 10);
v_prevLinterStates_189_ = lean_ctor_get(v___x_177_, 11);
v_codeQualityEntryTasks_190_ = lean_ctor_get(v___x_177_, 12);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_203_ == 0)
{
v___x_192_ = v___x_177_;
v_isShared_193_ = v_isSharedCheck_203_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_codeQualityEntryTasks_190_);
lean_inc(v_prevLinterStates_189_);
lean_inc(v_snapshotTasks_188_);
lean_inc(v_traceState_187_);
lean_inc(v_infoState_186_);
lean_inc(v_auxDeclNGen_185_);
lean_inc(v_ngen_184_);
lean_inc(v_maxRecDepth_183_);
lean_inc(v_nextMacroScope_182_);
lean_inc(v_usedQuotCtxts_181_);
lean_inc(v_scopes_180_);
lean_inc(v_messages_179_);
lean_inc(v_env_178_);
lean_dec(v___x_177_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_203_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_197_; 
v___x_194_ = lean_box(0);
v___x_195_ = l_Lean_MessageLog_add(v___x_176_, v_messages_179_);
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 1, v___x_195_);
v___x_197_ = v___x_192_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_env_178_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v___x_195_);
lean_ctor_set(v_reuseFailAlloc_202_, 2, v_scopes_180_);
lean_ctor_set(v_reuseFailAlloc_202_, 3, v_usedQuotCtxts_181_);
lean_ctor_set(v_reuseFailAlloc_202_, 4, v_nextMacroScope_182_);
lean_ctor_set(v_reuseFailAlloc_202_, 5, v_maxRecDepth_183_);
lean_ctor_set(v_reuseFailAlloc_202_, 6, v_ngen_184_);
lean_ctor_set(v_reuseFailAlloc_202_, 7, v_auxDeclNGen_185_);
lean_ctor_set(v_reuseFailAlloc_202_, 8, v_infoState_186_);
lean_ctor_set(v_reuseFailAlloc_202_, 9, v_traceState_187_);
lean_ctor_set(v_reuseFailAlloc_202_, 10, v_snapshotTasks_188_);
lean_ctor_set(v_reuseFailAlloc_202_, 11, v_prevLinterStates_189_);
lean_ctor_set(v_reuseFailAlloc_202_, 12, v_codeQualityEntryTasks_190_);
v___x_197_ = v_reuseFailAlloc_202_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
lean_object* v___x_198_; lean_object* v___x_200_; 
v___x_198_ = lean_st_ref_put(v___y_164_, v___x_197_);
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 0, v___x_194_);
v___x_200_ = v___x_171_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_194_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
}
}
}
else
{
lean_object* v_a_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_212_; 
lean_dec(v_currNamespace_167_);
lean_dec_ref(v___y_161_);
lean_dec(v___y_160_);
lean_dec_ref(v___y_157_);
v_a_205_ = lean_ctor_get(v___x_168_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_168_);
if (v_isSharedCheck_212_ == 0)
{
v___x_207_ = v___x_168_;
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_a_205_);
lean_dec(v___x_168_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_210_; 
if (v_isShared_208_ == 0)
{
v___x_210_ = v___x_207_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_a_205_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
}
else
{
lean_object* v_a_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_220_; 
lean_dec_ref(v___y_161_);
lean_dec(v___y_160_);
lean_dec_ref(v___y_157_);
v_a_213_ = lean_ctor_get(v___x_165_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_165_);
if (v_isSharedCheck_220_ == 0)
{
v___x_215_ = v___x_165_;
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_a_213_);
lean_dec(v___x_165_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_218_; 
if (v_isShared_216_ == 0)
{
v___x_218_ = v___x_215_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_a_213_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
}
v___jp_221_:
{
lean_object* v_fileName_227_; lean_object* v_fileMap_228_; uint8_t v_suppressElabErrors_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___f_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v_a_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_248_; 
v_fileName_227_ = lean_ctor_get(v___y_153_, 0);
v_fileMap_228_ = lean_ctor_get(v___y_153_, 1);
v_suppressElabErrors_229_ = lean_ctor_get_uint8(v___y_153_, sizeof(void*)*10);
v___x_230_ = lean_box(v_suppressElabErrors_229_);
v___x_231_ = lean_box(v___y_222_);
v___f_232_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___lam__0___boxed), 3, 2);
lean_closure_set(v___f_232_, 0, v___x_230_);
lean_closure_set(v___f_232_, 1, v___x_231_);
v___x_233_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_150_);
v___x_234_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg(v___x_233_, v___y_154_);
v_a_235_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_248_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_248_ == 0)
{
v___x_237_ = v___x_234_;
v_isShared_238_ = v_isSharedCheck_248_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_a_235_);
lean_dec(v___x_234_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_248_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
lean_inc_ref_n(v_fileMap_228_, 2);
v___x_239_ = l_Lean_FileMap_toPosition(v_fileMap_228_, v___y_224_);
lean_dec(v___y_224_);
v___x_240_ = l_Lean_FileMap_toPosition(v_fileMap_228_, v___y_226_);
lean_dec(v___y_226_);
v___x_241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
v___x_242_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___closed__0));
if (v_suppressElabErrors_229_ == 0)
{
lean_del_object(v___x_237_);
lean_dec_ref(v___f_232_);
v___y_157_ = v___x_239_;
v___y_158_ = v___x_242_;
v___y_159_ = v___y_223_;
v___y_160_ = v___x_241_;
v___y_161_ = v_a_235_;
v___y_162_ = v___y_225_;
v___y_163_ = v_fileName_227_;
v___y_164_ = v___y_154_;
goto v___jp_156_;
}
else
{
uint8_t v___x_243_; 
lean_inc(v_a_235_);
v___x_243_ = l_Lean_MessageData_hasTag(v___f_232_, v_a_235_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; lean_object* v___x_246_; 
lean_dec_ref_known(v___x_241_, 1);
lean_dec_ref(v___x_239_);
lean_dec(v_a_235_);
v___x_244_ = lean_box(0);
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 0, v___x_244_);
v___x_246_ = v___x_237_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v___x_244_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
else
{
lean_del_object(v___x_237_);
v___y_157_ = v___x_239_;
v___y_158_ = v___x_242_;
v___y_159_ = v___y_223_;
v___y_160_ = v___x_241_;
v___y_161_ = v_a_235_;
v___y_162_ = v___y_225_;
v___y_163_ = v_fileName_227_;
v___y_164_ = v___y_154_;
goto v___jp_156_;
}
}
}
}
v___jp_249_:
{
lean_object* v___x_255_; 
v___x_255_ = l_Lean_Syntax_getTailPos_x3f(v___y_251_, v___y_252_);
lean_dec(v___y_251_);
if (lean_obj_tag(v___x_255_) == 0)
{
lean_inc(v___y_254_);
v___y_222_ = v___y_250_;
v___y_223_ = v___y_252_;
v___y_224_ = v___y_254_;
v___y_225_ = v___y_253_;
v___y_226_ = v___y_254_;
goto v___jp_221_;
}
else
{
lean_object* v_val_256_; 
v_val_256_ = lean_ctor_get(v___x_255_, 0);
lean_inc(v_val_256_);
lean_dec_ref_known(v___x_255_, 1);
v___y_222_ = v___y_250_;
v___y_223_ = v___y_252_;
v___y_224_ = v___y_254_;
v___y_225_ = v___y_253_;
v___y_226_ = v_val_256_;
goto v___jp_221_;
}
}
v___jp_257_:
{
lean_object* v___x_261_; 
v___x_261_ = l_Lean_Elab_Command_getRef___redArg(v___y_153_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v_a_262_; lean_object* v_ref_263_; lean_object* v___x_264_; 
v_a_262_ = lean_ctor_get(v___x_261_, 0);
lean_inc(v_a_262_);
lean_dec_ref_known(v___x_261_, 1);
v_ref_263_ = l_Lean_replaceRef(v_ref_149_, v_a_262_);
lean_dec(v_a_262_);
v___x_264_ = l_Lean_Syntax_getPos_x3f(v_ref_263_, v___y_259_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v___x_265_; 
v___x_265_ = lean_unsigned_to_nat(0u);
v___y_250_ = v___y_258_;
v___y_251_ = v_ref_263_;
v___y_252_ = v___y_259_;
v___y_253_ = v___y_260_;
v___y_254_ = v___x_265_;
goto v___jp_249_;
}
else
{
lean_object* v_val_266_; 
v_val_266_ = lean_ctor_get(v___x_264_, 0);
lean_inc(v_val_266_);
lean_dec_ref_known(v___x_264_, 1);
v___y_250_ = v___y_258_;
v___y_251_ = v_ref_263_;
v___y_252_ = v___y_259_;
v___y_253_ = v___y_260_;
v___y_254_ = v_val_266_;
goto v___jp_249_;
}
}
else
{
lean_object* v_a_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_274_; 
lean_dec_ref(v_msgData_150_);
v_a_267_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_274_ == 0)
{
v___x_269_ = v___x_261_;
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_a_267_);
lean_dec(v___x_261_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_272_; 
if (v_isShared_270_ == 0)
{
v___x_272_ = v___x_269_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_a_267_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
}
v___jp_276_:
{
if (v___y_279_ == 0)
{
v___y_258_ = v___y_277_;
v___y_259_ = v___y_278_;
v___y_260_ = v_severity_151_;
goto v___jp_257_;
}
else
{
v___y_258_ = v___y_277_;
v___y_259_ = v___y_278_;
v___y_260_ = v___x_275_;
goto v___jp_257_;
}
}
v___jp_280_:
{
if (v___y_281_ == 0)
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v_scopes_284_; lean_object* v___x_285_; lean_object* v_opts_286_; uint8_t v___x_287_; uint8_t v___x_288_; 
v___x_282_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_283_ = lean_st_ref_get(v___y_154_);
v_scopes_284_ = lean_ctor_get(v___x_283_, 2);
lean_inc(v_scopes_284_);
lean_dec(v___x_283_);
v___x_285_ = l_List_head_x21___redArg(v___x_282_, v_scopes_284_);
lean_dec(v_scopes_284_);
v_opts_286_ = lean_ctor_get(v___x_285_, 1);
lean_inc_ref(v_opts_286_);
lean_dec(v___x_285_);
v___x_287_ = 1;
v___x_288_ = l_Lean_instBEqMessageSeverity_beq(v_severity_151_, v___x_287_);
if (v___x_288_ == 0)
{
lean_dec_ref(v_opts_286_);
v___y_277_ = v___y_281_;
v___y_278_ = v___y_281_;
v___y_279_ = v___x_288_;
goto v___jp_276_;
}
else
{
lean_object* v___x_289_; uint8_t v___x_290_; 
v___x_289_ = l_Lean_warningAsError;
v___x_290_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__5(v_opts_286_, v___x_289_);
lean_dec_ref(v_opts_286_);
v___y_277_ = v___y_281_;
v___y_278_ = v___y_281_;
v___y_279_ = v___x_290_;
goto v___jp_276_;
}
}
else
{
lean_object* v___x_291_; lean_object* v___x_292_; 
lean_dec_ref(v_msgData_150_);
v___x_291_ = lean_box(0);
v___x_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
return v___x_292_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_149_ = stack[0].m_obj;
lean_object* v_msgData_150_ = stack[1].m_obj;
uint8_t v_severity_151_ = stack[2].m_num;
uint8_t v_isSilent_152_ = stack[3].m_num;
lean_object* v___y_153_ = stack[4].m_obj;
lean_object* v___y_154_ = stack[5].m_obj;
lean_object* v_res_295_;
v_res_295_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3(v_ref_149_, v_msgData_150_, v_severity_151_, v_isSilent_152_, v___y_153_, v___y_154_);
stack->m_obj
 = v_res_295_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___boxed(lean_object* v_ref_296_, lean_object* v_msgData_297_, lean_object* v_severity_298_, lean_object* v_isSilent_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
uint8_t v_severity_boxed_303_; uint8_t v_isSilent_boxed_304_; lean_object* v_res_305_; 
v_severity_boxed_303_ = lean_unbox(v_severity_298_);
v_isSilent_boxed_304_ = lean_unbox(v_isSilent_299_);
v_res_305_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3(v_ref_296_, v_msgData_297_, v_severity_boxed_303_, v_isSilent_boxed_304_, v___y_300_, v___y_301_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec(v_ref_296_);
return v_res_305_;
}
}
lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2(lean_object* v_ref_306_, lean_object* v_msgData_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
uint8_t v___x_311_; uint8_t v___x_312_; lean_object* v___x_313_; 
v___x_311_ = 1;
v___x_312_ = 0;
v___x_313_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3(v_ref_306_, v_msgData_307_, v___x_311_, v___x_312_, v___y_308_, v___y_309_);
return v___x_313_;
}
}
LEAN_EXPORT void l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_306_ = stack[0].m_obj;
lean_object* v_msgData_307_ = stack[1].m_obj;
lean_object* v___y_308_ = stack[2].m_obj;
lean_object* v___y_309_ = stack[3].m_obj;
lean_object* v_res_314_;
v_res_314_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2(v_ref_306_, v_msgData_307_, v___y_308_, v___y_309_);
stack->m_obj
 = v_res_314_;
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2___boxed(lean_object* v_ref_315_, lean_object* v_msgData_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2(v_ref_315_, v_msgData_316_, v___y_317_, v___y_318_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
lean_dec(v_ref_315_);
return v_res_320_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__1(void){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_322_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__0));
v___x_323_ = l_Lean_stringToMessageData(v___x_322_);
return v___x_323_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__3(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__2));
v___x_326_ = l_Lean_stringToMessageData(v___x_325_);
return v___x_326_;
}
}
lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1(lean_object* v_linterOption_327_, lean_object* v_stx_328_, lean_object* v_msg_329_, lean_object* v___y_330_, lean_object* v___y_331_){
_start:
{
lean_object* v_name_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_351_; 
v_name_333_ = lean_ctor_get(v_linterOption_327_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v_linterOption_327_);
if (v_isSharedCheck_351_ == 0)
{
lean_object* v_unused_352_; 
v_unused_352_ = lean_ctor_get(v_linterOption_327_, 1);
lean_dec(v_unused_352_);
v___x_335_ = v_linterOption_327_;
v_isShared_336_ = v_isSharedCheck_351_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_name_333_);
lean_dec(v_linterOption_327_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_351_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_340_; 
v___x_337_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__1);
lean_inc(v_name_333_);
v___x_338_ = l_Lean_MessageData_ofName(v_name_333_);
if (v_isShared_336_ == 0)
{
lean_ctor_set_tag(v___x_335_, 7);
lean_ctor_set(v___x_335_, 1, v___x_338_);
lean_ctor_set(v___x_335_, 0, v___x_337_);
v___x_340_ = v___x_335_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v___x_337_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v___x_338_);
v___x_340_ = v_reuseFailAlloc_350_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v_disable_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_341_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__3);
v___x_342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_340_);
lean_ctor_set(v___x_342_, 1, v___x_341_);
v_disable_343_ = l_Lean_MessageData_note(v___x_342_);
v___x_344_ = l_Lean_Linter_linterMessageTag;
v___x_345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_345_, 0, v_msg_329_);
lean_ctor_set(v___x_345_, 1, v_disable_343_);
v___x_346_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_344_);
lean_ctor_set(v___x_346_, 1, v___x_345_);
v___x_347_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_347_, 0, v_name_333_);
lean_ctor_set(v___x_347_, 1, v___x_346_);
lean_inc(v_stx_328_);
v___x_348_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_348_, 0, v_stx_328_);
lean_ctor_set(v___x_348_, 1, v___x_347_);
v___x_349_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2(v_stx_328_, v___x_348_, v___y_330_, v___y_331_);
lean_dec(v_stx_328_);
return v___x_349_;
}
}
}
}
LEAN_EXPORT void l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_linterOption_327_ = stack[0].m_obj;
lean_object* v_stx_328_ = stack[1].m_obj;
lean_object* v_msg_329_ = stack[2].m_obj;
lean_object* v___y_330_ = stack[3].m_obj;
lean_object* v___y_331_ = stack[4].m_obj;
lean_object* v_res_353_;
v_res_353_ = l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1(v_linterOption_327_, v_stx_328_, v_msg_329_, v___y_330_, v___y_331_);
stack->m_obj
 = v_res_353_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___boxed(lean_object* v_linterOption_354_, lean_object* v_stx_355_, lean_object* v_msg_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1(v_linterOption_354_, v_stx_355_, v_msg_356_, v___y_357_, v___y_358_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
return v_res_360_;
}
}
lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0___redArg(lean_object* v_o_361_, lean_object* v___y_362_){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v_env_366_; lean_object* v___x_367_; lean_object* v_toEnvExtension_368_; lean_object* v_asyncMode_369_; lean_object* v___x_370_; uint8_t v___x_371_; lean_object* v___x_372_; lean_object* v_merged_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_381_; 
v___x_364_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_365_ = lean_st_ref_get(v___y_362_);
v_env_366_ = lean_ctor_get(v___x_365_, 0);
lean_inc_ref(v_env_366_);
lean_dec(v___x_365_);
v___x_367_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_368_ = lean_ctor_get(v___x_367_, 0);
v_asyncMode_369_ = lean_ctor_get(v_toEnvExtension_368_, 2);
v___x_370_ = lean_box(0);
v___x_371_ = 0;
v___x_372_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_364_, v___x_367_, v_env_366_, v_asyncMode_369_, v___x_370_, v___x_371_);
v_merged_373_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_381_ == 0)
{
lean_object* v_unused_382_; 
v_unused_382_ = lean_ctor_get(v___x_372_, 1);
lean_dec(v_unused_382_);
v___x_375_ = v___x_372_;
v_isShared_376_ = v_isSharedCheck_381_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_merged_373_);
lean_dec(v___x_372_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_381_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_378_; 
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 1, v_merged_373_);
lean_ctor_set(v___x_375_, 0, v_o_361_);
v___x_378_ = v___x_375_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_o_361_);
lean_ctor_set(v_reuseFailAlloc_380_, 1, v_merged_373_);
v___x_378_ = v_reuseFailAlloc_380_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
lean_object* v___x_379_; 
v___x_379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
return v___x_379_;
}
}
}
}
LEAN_EXPORT void l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_361_ = stack[0].m_obj;
lean_object* v___y_362_ = stack[1].m_obj;
lean_object* v_res_383_;
v_res_383_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0___redArg(v_o_361_, v___y_362_);
stack->m_obj
 = v_res_383_;
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0___redArg___boxed(lean_object* v_o_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0___redArg(v_o_384_, v___y_385_);
lean_dec(v___y_385_);
return v_res_387_;
}
}
lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0(lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v_scopes_393_; lean_object* v___x_394_; lean_object* v_opts_395_; lean_object* v___x_396_; 
v___x_391_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_392_ = lean_st_ref_get(v___y_389_);
v_scopes_393_ = lean_ctor_get(v___x_392_, 2);
lean_inc(v_scopes_393_);
lean_dec(v___x_392_);
v___x_394_ = l_List_head_x21___redArg(v___x_391_, v_scopes_393_);
lean_dec(v_scopes_393_);
v_opts_395_ = lean_ctor_get(v___x_394_, 1);
lean_inc_ref(v_opts_395_);
lean_dec(v___x_394_);
v___x_396_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0___redArg(v_opts_395_, v___y_389_);
return v___x_396_;
}
}
LEAN_EXPORT void l_Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_388_ = stack[0].m_obj;
lean_object* v___y_389_ = stack[1].m_obj;
lean_object* v_res_397_;
v_res_397_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0(v___y_388_, v___y_389_);
stack->m_obj
 = v_res_397_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0___boxed(lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0(v___y_398_, v___y_399_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
return v_res_401_;
}
}
static lean_object* _init_l_Lean_Linter_omit___lam__1___closed__1(void){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = ((lean_object*)(l_Lean_Linter_omit___lam__1___closed__0));
v___x_404_ = l_Lean_stringToMessageData(v___x_403_);
return v___x_404_;
}
}
lean_object* l_Lean_Linter_omit___lam__1(lean_object* v___f_405_, lean_object* v_stx_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
lean_object* v___x_410_; lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_429_; 
v___x_410_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0(v___y_407_, v___y_408_);
v_a_411_ = lean_ctor_get(v___x_410_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_429_ == 0)
{
v___x_413_ = v___x_410_;
v_isShared_414_ = v_isSharedCheck_429_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_dec(v___x_410_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_429_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_415_; uint8_t v___x_416_; 
v___x_415_ = l_Lean_Linter_linter_omit;
v___x_416_ = l_Lean_Linter_getLinterValue(v___x_415_, v_a_411_);
lean_dec(v_a_411_);
if (v___x_416_ == 0)
{
lean_object* v___x_417_; lean_object* v___x_419_; 
lean_dec(v_stx_406_);
lean_dec_ref(v___f_405_);
v___x_417_ = lean_box(0);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 0, v___x_417_);
v___x_419_ = v___x_413_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_417_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
else
{
lean_object* v___x_421_; 
v___x_421_ = l_Lean_Syntax_find_x3f(v_stx_406_, v___f_405_);
if (lean_obj_tag(v___x_421_) == 1)
{
lean_object* v_val_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
lean_del_object(v___x_413_);
v_val_422_ = lean_ctor_get(v___x_421_, 0);
lean_inc(v_val_422_);
lean_dec_ref_known(v___x_421_, 1);
v___x_423_ = lean_obj_once(&l_Lean_Linter_omit___lam__1___closed__1, &l_Lean_Linter_omit___lam__1___closed__1_once, _init_l_Lean_Linter_omit___lam__1___closed__1);
v___x_424_ = l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1(v___x_415_, v_val_422_, v___x_423_, v___y_407_, v___y_408_);
return v___x_424_;
}
else
{
lean_object* v___x_425_; lean_object* v___x_427_; 
lean_dec(v___x_421_);
v___x_425_ = lean_box(0);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 0, v___x_425_);
v___x_427_ = v___x_413_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_425_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Linter_omit___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_405_ = stack[0].m_obj;
lean_object* v_stx_406_ = stack[1].m_obj;
lean_object* v___y_407_ = stack[2].m_obj;
lean_object* v___y_408_ = stack[3].m_obj;
lean_object* v_res_430_;
v_res_430_ = l_Lean_Linter_omit___lam__1(v___f_405_, v_stx_406_, v___y_407_, v___y_408_);
stack->m_obj
 = v_res_430_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_omit___lam__1___boxed(lean_object* v___f_431_, lean_object* v_stx_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_Linter_omit___lam__1(v___f_431_, v_stx_432_, v___y_433_, v___y_434_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
return v_res_436_;
}
}
lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0(lean_object* v_o_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0___redArg(v_o_448_, v___y_450_);
return v___x_452_;
}
}
LEAN_EXPORT void l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_448_ = stack[0].m_obj;
lean_object* v___y_449_ = stack[1].m_obj;
lean_object* v___y_450_ = stack[2].m_obj;
lean_object* v_res_453_;
v_res_453_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0(v_o_448_, v___y_449_, v___y_450_);
stack->m_obj
 = v_res_453_;
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0___boxed(lean_object* v_o_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0(v_o_454_, v___y_455_, v___y_456_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
return v_res_458_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4(lean_object* v_msgData_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg(v_msgData_459_, v___y_461_);
return v___x_463_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_459_ = stack[0].m_obj;
lean_object* v___y_460_ = stack[1].m_obj;
lean_object* v___y_461_ = stack[2].m_obj;
lean_object* v_res_464_;
v_res_464_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4(v_msgData_459_, v___y_460_, v___y_461_);
stack->m_obj
 = v_res_464_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msgData_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4(v_msgData_465_, v___y_466_, v___y_467_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
return v_res_469_;
}
}
lean_object* l___private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3756037646____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = ((lean_object*)(l_Lean_Linter_omit));
v___x_472_ = l_Lean_Elab_Command_addLinter(v___x_471_);
return v___x_472_;
}
}
LEAN_EXPORT void l___private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3756037646____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_473_;
v_res_473_ = l___private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3756037646____hygCtx___hyg_2_();
stack->m_obj
 = v_res_473_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3756037646____hygCtx___hyg_2____boxed(lean_object* v_a_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l___private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3756037646____hygCtx___hyg_2_();
return v_res_475_;
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
