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
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_linterSetsExt;
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
v___x_86_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
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
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_89_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_90_ = lean_unsigned_to_nat(0u);
v___x_91_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
lean_ctor_set(v___x_91_, 1, v___x_90_);
lean_ctor_set(v___x_91_, 2, v___x_90_);
lean_ctor_set(v___x_91_, 3, v___x_90_);
lean_ctor_set(v___x_91_, 4, v___x_89_);
lean_ctor_set(v___x_91_, 5, v___x_89_);
lean_ctor_set(v___x_91_, 6, v___x_89_);
lean_ctor_set(v___x_91_, 7, v___x_89_);
lean_ctor_set(v___x_91_, 8, v___x_89_);
lean_ctor_set(v___x_91_, 9, v___x_89_);
lean_ctor_set(v___x_91_, 10, v___x_89_);
return v___x_91_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_92_ = lean_unsigned_to_nat(32u);
v___x_93_ = lean_mk_empty_array_with_capacity(v___x_92_);
v___x_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
return v___x_94_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_95_ = ((size_t)5ULL);
v___x_96_ = lean_unsigned_to_nat(0u);
v___x_97_ = lean_unsigned_to_nat(32u);
v___x_98_ = lean_mk_empty_array_with_capacity(v___x_97_);
v___x_99_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_100_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_100_, 0, v___x_99_);
lean_ctor_set(v___x_100_, 1, v___x_98_);
lean_ctor_set(v___x_100_, 2, v___x_96_);
lean_ctor_set(v___x_100_, 3, v___x_96_);
lean_ctor_set_usize(v___x_100_, 4, v___x_95_);
return v___x_100_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_101_ = lean_box(1);
v___x_102_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_103_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_104_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
lean_ctor_set(v___x_104_, 1, v___x_102_);
lean_ctor_set(v___x_104_, 2, v___x_101_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msgData_105_, lean_object* v___y_106_){
_start:
{
lean_object* v___x_108_; lean_object* v_env_109_; lean_object* v___x_110_; lean_object* v_scopes_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v_opts_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_108_ = lean_st_ref_get(v___y_106_);
v_env_109_ = lean_ctor_get(v___x_108_, 0);
lean_inc_ref(v_env_109_);
lean_dec(v___x_108_);
v___x_110_ = lean_st_ref_get(v___y_106_);
v_scopes_111_ = lean_ctor_get(v___x_110_, 2);
lean_inc(v_scopes_111_);
lean_dec(v___x_110_);
v___x_112_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_113_ = l_List_head_x21___redArg(v___x_112_, v_scopes_111_);
lean_dec(v_scopes_111_);
v_opts_114_ = lean_ctor_get(v___x_113_, 1);
lean_inc_ref(v_opts_114_);
lean_dec(v___x_113_);
v___x_115_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_116_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_117_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_117_, 0, v_env_109_);
lean_ctor_set(v___x_117_, 1, v___x_115_);
lean_ctor_set(v___x_117_, 2, v___x_116_);
lean_ctor_set(v___x_117_, 3, v_opts_114_);
v___x_118_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
lean_ctor_set(v___x_118_, 1, v_msgData_105_);
v___x_119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msgData_120_, lean_object* v___y_121_, lean_object* v___y_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg(v_msgData_120_, v___y_121_);
lean_dec(v___y_121_);
return v_res_123_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___lam__0(uint8_t v_suppressElabErrors_125_, uint8_t v___y_126_, lean_object* v_x_127_){
_start:
{
if (lean_obj_tag(v_x_127_) == 1)
{
lean_object* v_pre_128_; 
v_pre_128_ = lean_ctor_get(v_x_127_, 0);
if (lean_obj_tag(v_pre_128_) == 0)
{
lean_object* v_str_129_; lean_object* v___x_130_; uint8_t v___x_131_; 
v_str_129_ = lean_ctor_get(v_x_127_, 1);
v___x_130_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___lam__0___closed__0));
v___x_131_ = lean_string_dec_eq(v_str_129_, v___x_130_);
if (v___x_131_ == 0)
{
return v___x_131_;
}
else
{
return v_suppressElabErrors_125_;
}
}
else
{
return v___y_126_;
}
}
else
{
return v___y_126_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___lam__0___boxed(lean_object* v_suppressElabErrors_132_, lean_object* v___y_133_, lean_object* v_x_134_){
_start:
{
uint8_t v_suppressElabErrors_boxed_135_; uint8_t v___y_3060__boxed_136_; uint8_t v_res_137_; lean_object* v_r_138_; 
v_suppressElabErrors_boxed_135_ = lean_unbox(v_suppressElabErrors_132_);
v___y_3060__boxed_136_ = lean_unbox(v___y_133_);
v_res_137_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___lam__0(v_suppressElabErrors_boxed_135_, v___y_3060__boxed_136_, v_x_134_);
lean_dec(v_x_134_);
v_r_138_ = lean_box(v_res_137_);
return v_r_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3(lean_object* v_ref_140_, lean_object* v_msgData_141_, uint8_t v_severity_142_, uint8_t v_isSilent_143_, lean_object* v___y_144_, lean_object* v___y_145_){
_start:
{
lean_object* v___y_148_; lean_object* v___y_149_; uint8_t v___y_150_; uint8_t v___y_151_; lean_object* v___y_152_; lean_object* v___y_153_; lean_object* v___y_154_; lean_object* v___y_155_; uint8_t v___y_213_; uint8_t v___y_214_; uint8_t v___y_215_; lean_object* v___y_216_; lean_object* v___y_217_; uint8_t v___y_241_; uint8_t v___y_242_; uint8_t v___y_243_; lean_object* v___y_244_; lean_object* v___y_245_; uint8_t v___y_249_; uint8_t v___y_250_; uint8_t v___y_251_; uint8_t v___x_266_; uint8_t v___y_268_; uint8_t v___y_269_; uint8_t v___y_270_; uint8_t v___y_272_; uint8_t v___x_284_; 
v___x_266_ = 2;
v___x_284_ = l_Lean_instBEqMessageSeverity_beq(v_severity_142_, v___x_266_);
if (v___x_284_ == 0)
{
v___y_272_ = v___x_284_;
goto v___jp_271_;
}
else
{
uint8_t v___x_285_; 
lean_inc_ref(v_msgData_141_);
v___x_285_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_141_);
v___y_272_ = v___x_285_;
goto v___jp_271_;
}
v___jp_147_:
{
lean_object* v___x_156_; 
v___x_156_ = l_Lean_Elab_Command_getScope___redArg(v___y_155_);
if (lean_obj_tag(v___x_156_) == 0)
{
lean_object* v_a_157_; lean_object* v___x_158_; 
v_a_157_ = lean_ctor_get(v___x_156_, 0);
lean_inc(v_a_157_);
lean_dec_ref_known(v___x_156_, 1);
v___x_158_ = l_Lean_Elab_Command_getScope___redArg(v___y_155_);
if (lean_obj_tag(v___x_158_) == 0)
{
lean_object* v_a_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_195_; 
v_a_159_ = lean_ctor_get(v___x_158_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_195_ == 0)
{
v___x_161_ = v___x_158_;
v_isShared_162_ = v_isSharedCheck_195_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_a_159_);
lean_dec(v___x_158_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_195_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_163_; lean_object* v_currNamespace_164_; lean_object* v_openDecls_165_; lean_object* v_env_166_; lean_object* v_messages_167_; lean_object* v_scopes_168_; lean_object* v_usedQuotCtxts_169_; lean_object* v_nextMacroScope_170_; lean_object* v_maxRecDepth_171_; lean_object* v_ngen_172_; lean_object* v_auxDeclNGen_173_; lean_object* v_infoState_174_; lean_object* v_traceState_175_; lean_object* v_snapshotTasks_176_; lean_object* v_prevLinterStates_177_; lean_object* v_codeQualityEntryTasks_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_194_; 
v___x_163_ = lean_st_ref_take(v___y_155_);
v_currNamespace_164_ = lean_ctor_get(v_a_157_, 2);
lean_inc(v_currNamespace_164_);
lean_dec(v_a_157_);
v_openDecls_165_ = lean_ctor_get(v_a_159_, 3);
lean_inc(v_openDecls_165_);
lean_dec(v_a_159_);
v_env_166_ = lean_ctor_get(v___x_163_, 0);
v_messages_167_ = lean_ctor_get(v___x_163_, 1);
v_scopes_168_ = lean_ctor_get(v___x_163_, 2);
v_usedQuotCtxts_169_ = lean_ctor_get(v___x_163_, 3);
v_nextMacroScope_170_ = lean_ctor_get(v___x_163_, 4);
v_maxRecDepth_171_ = lean_ctor_get(v___x_163_, 5);
v_ngen_172_ = lean_ctor_get(v___x_163_, 6);
v_auxDeclNGen_173_ = lean_ctor_get(v___x_163_, 7);
v_infoState_174_ = lean_ctor_get(v___x_163_, 8);
v_traceState_175_ = lean_ctor_get(v___x_163_, 9);
v_snapshotTasks_176_ = lean_ctor_get(v___x_163_, 10);
v_prevLinterStates_177_ = lean_ctor_get(v___x_163_, 11);
v_codeQualityEntryTasks_178_ = lean_ctor_get(v___x_163_, 12);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_163_);
if (v_isSharedCheck_194_ == 0)
{
v___x_180_ = v___x_163_;
v_isShared_181_ = v_isSharedCheck_194_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_codeQualityEntryTasks_178_);
lean_inc(v_prevLinterStates_177_);
lean_inc(v_snapshotTasks_176_);
lean_inc(v_traceState_175_);
lean_inc(v_infoState_174_);
lean_inc(v_auxDeclNGen_173_);
lean_inc(v_ngen_172_);
lean_inc(v_maxRecDepth_171_);
lean_inc(v_nextMacroScope_170_);
lean_inc(v_usedQuotCtxts_169_);
lean_inc(v_scopes_168_);
lean_inc(v_messages_167_);
lean_inc(v_env_166_);
lean_dec(v___x_163_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_194_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_187_; 
v___x_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_182_, 0, v_currNamespace_164_);
lean_ctor_set(v___x_182_, 1, v_openDecls_165_);
v___x_183_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
lean_ctor_set(v___x_183_, 1, v___y_154_);
lean_inc_ref(v___y_152_);
lean_inc_ref(v___y_149_);
v___x_184_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_184_, 0, v___y_149_);
lean_ctor_set(v___x_184_, 1, v___y_148_);
lean_ctor_set(v___x_184_, 2, v___y_153_);
lean_ctor_set(v___x_184_, 3, v___y_152_);
lean_ctor_set(v___x_184_, 4, v___x_183_);
lean_ctor_set_uint8(v___x_184_, sizeof(void*)*5, v___y_151_);
lean_ctor_set_uint8(v___x_184_, sizeof(void*)*5 + 1, v___y_150_);
lean_ctor_set_uint8(v___x_184_, sizeof(void*)*5 + 2, v_isSilent_143_);
v___x_185_ = l_Lean_MessageLog_add(v___x_184_, v_messages_167_);
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 1, v___x_185_);
v___x_187_ = v___x_180_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_env_166_);
lean_ctor_set(v_reuseFailAlloc_193_, 1, v___x_185_);
lean_ctor_set(v_reuseFailAlloc_193_, 2, v_scopes_168_);
lean_ctor_set(v_reuseFailAlloc_193_, 3, v_usedQuotCtxts_169_);
lean_ctor_set(v_reuseFailAlloc_193_, 4, v_nextMacroScope_170_);
lean_ctor_set(v_reuseFailAlloc_193_, 5, v_maxRecDepth_171_);
lean_ctor_set(v_reuseFailAlloc_193_, 6, v_ngen_172_);
lean_ctor_set(v_reuseFailAlloc_193_, 7, v_auxDeclNGen_173_);
lean_ctor_set(v_reuseFailAlloc_193_, 8, v_infoState_174_);
lean_ctor_set(v_reuseFailAlloc_193_, 9, v_traceState_175_);
lean_ctor_set(v_reuseFailAlloc_193_, 10, v_snapshotTasks_176_);
lean_ctor_set(v_reuseFailAlloc_193_, 11, v_prevLinterStates_177_);
lean_ctor_set(v_reuseFailAlloc_193_, 12, v_codeQualityEntryTasks_178_);
v___x_187_ = v_reuseFailAlloc_193_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_191_; 
v___x_188_ = lean_st_ref_put(v___y_155_, v___x_187_);
v___x_189_ = lean_box(0);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 0, v___x_189_);
v___x_191_ = v___x_161_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_189_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
}
}
else
{
lean_object* v_a_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_203_; 
lean_dec(v_a_157_);
lean_dec_ref(v___y_154_);
lean_dec(v___y_153_);
lean_dec_ref(v___y_148_);
v_a_196_ = lean_ctor_get(v___x_158_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_203_ == 0)
{
v___x_198_ = v___x_158_;
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_a_196_);
lean_dec(v___x_158_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_201_; 
if (v_isShared_199_ == 0)
{
v___x_201_ = v___x_198_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_a_196_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
}
else
{
lean_object* v_a_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_211_; 
lean_dec_ref(v___y_154_);
lean_dec(v___y_153_);
lean_dec_ref(v___y_148_);
v_a_204_ = lean_ctor_get(v___x_156_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v___x_156_);
if (v_isSharedCheck_211_ == 0)
{
v___x_206_ = v___x_156_;
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_a_204_);
lean_dec(v___x_156_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_209_; 
if (v_isShared_207_ == 0)
{
v___x_209_ = v___x_206_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v_a_204_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
}
v___jp_212_:
{
lean_object* v_fileName_218_; lean_object* v_fileMap_219_; uint8_t v_suppressElabErrors_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v_a_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_239_; 
v_fileName_218_ = lean_ctor_get(v___y_144_, 0);
v_fileMap_219_ = lean_ctor_get(v___y_144_, 1);
v_suppressElabErrors_220_ = lean_ctor_get_uint8(v___y_144_, sizeof(void*)*10);
v___x_221_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_141_);
v___x_222_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg(v___x_221_, v___y_145_);
v_a_223_ = lean_ctor_get(v___x_222_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_239_ == 0)
{
v___x_225_ = v___x_222_;
v_isShared_226_ = v_isSharedCheck_239_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_a_223_);
lean_dec(v___x_222_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_239_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
lean_inc_ref_n(v_fileMap_219_, 2);
v___x_227_ = l_Lean_FileMap_toPosition(v_fileMap_219_, v___y_216_);
lean_dec(v___y_216_);
v___x_228_ = l_Lean_FileMap_toPosition(v_fileMap_219_, v___y_217_);
lean_dec(v___y_217_);
v___x_229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
v___x_230_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___closed__0));
if (v_suppressElabErrors_220_ == 0)
{
lean_del_object(v___x_225_);
v___y_148_ = v___x_227_;
v___y_149_ = v_fileName_218_;
v___y_150_ = v___y_214_;
v___y_151_ = v___y_215_;
v___y_152_ = v___x_230_;
v___y_153_ = v___x_229_;
v___y_154_ = v_a_223_;
v___y_155_ = v___y_145_;
goto v___jp_147_;
}
else
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___f_233_; uint8_t v___x_234_; 
v___x_231_ = lean_box(v_suppressElabErrors_220_);
v___x_232_ = lean_box(v___y_213_);
v___f_233_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___lam__0___boxed), 3, 2);
lean_closure_set(v___f_233_, 0, v___x_231_);
lean_closure_set(v___f_233_, 1, v___x_232_);
lean_inc(v_a_223_);
v___x_234_ = l_Lean_MessageData_hasTag(v___f_233_, v_a_223_);
if (v___x_234_ == 0)
{
lean_object* v___x_235_; lean_object* v___x_237_; 
lean_dec_ref_known(v___x_229_, 1);
lean_dec_ref(v___x_227_);
lean_dec(v_a_223_);
v___x_235_ = lean_box(0);
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 0, v___x_235_);
v___x_237_ = v___x_225_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_235_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
else
{
lean_del_object(v___x_225_);
v___y_148_ = v___x_227_;
v___y_149_ = v_fileName_218_;
v___y_150_ = v___y_214_;
v___y_151_ = v___y_215_;
v___y_152_ = v___x_230_;
v___y_153_ = v___x_229_;
v___y_154_ = v_a_223_;
v___y_155_ = v___y_145_;
goto v___jp_147_;
}
}
}
}
v___jp_240_:
{
lean_object* v___x_246_; 
v___x_246_ = l_Lean_Syntax_getTailPos_x3f(v___y_244_, v___y_243_);
lean_dec(v___y_244_);
if (lean_obj_tag(v___x_246_) == 0)
{
lean_inc(v___y_245_);
v___y_213_ = v___y_241_;
v___y_214_ = v___y_242_;
v___y_215_ = v___y_243_;
v___y_216_ = v___y_245_;
v___y_217_ = v___y_245_;
goto v___jp_212_;
}
else
{
lean_object* v_val_247_; 
v_val_247_ = lean_ctor_get(v___x_246_, 0);
lean_inc(v_val_247_);
lean_dec_ref_known(v___x_246_, 1);
v___y_213_ = v___y_241_;
v___y_214_ = v___y_242_;
v___y_215_ = v___y_243_;
v___y_216_ = v___y_245_;
v___y_217_ = v_val_247_;
goto v___jp_212_;
}
}
v___jp_248_:
{
lean_object* v___x_252_; 
v___x_252_ = l_Lean_Elab_Command_getRef___redArg(v___y_144_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_a_253_; lean_object* v_ref_254_; lean_object* v___x_255_; 
v_a_253_ = lean_ctor_get(v___x_252_, 0);
lean_inc(v_a_253_);
lean_dec_ref_known(v___x_252_, 1);
v_ref_254_ = l_Lean_replaceRef(v_ref_140_, v_a_253_);
lean_dec(v_a_253_);
v___x_255_ = l_Lean_Syntax_getPos_x3f(v_ref_254_, v___y_250_);
if (lean_obj_tag(v___x_255_) == 0)
{
lean_object* v___x_256_; 
v___x_256_ = lean_unsigned_to_nat(0u);
v___y_241_ = v___y_249_;
v___y_242_ = v___y_251_;
v___y_243_ = v___y_250_;
v___y_244_ = v_ref_254_;
v___y_245_ = v___x_256_;
goto v___jp_240_;
}
else
{
lean_object* v_val_257_; 
v_val_257_ = lean_ctor_get(v___x_255_, 0);
lean_inc(v_val_257_);
lean_dec_ref_known(v___x_255_, 1);
v___y_241_ = v___y_249_;
v___y_242_ = v___y_251_;
v___y_243_ = v___y_250_;
v___y_244_ = v_ref_254_;
v___y_245_ = v_val_257_;
goto v___jp_240_;
}
}
else
{
lean_object* v_a_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_265_; 
lean_dec_ref(v_msgData_141_);
v_a_258_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_265_ == 0)
{
v___x_260_ = v___x_252_;
v_isShared_261_ = v_isSharedCheck_265_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_a_258_);
lean_dec(v___x_252_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_265_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_263_; 
if (v_isShared_261_ == 0)
{
v___x_263_ = v___x_260_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_a_258_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
}
v___jp_267_:
{
if (v___y_270_ == 0)
{
v___y_249_ = v___y_268_;
v___y_250_ = v___y_269_;
v___y_251_ = v_severity_142_;
goto v___jp_248_;
}
else
{
v___y_249_ = v___y_268_;
v___y_250_ = v___y_269_;
v___y_251_ = v___x_266_;
goto v___jp_248_;
}
}
v___jp_271_:
{
if (v___y_272_ == 0)
{
lean_object* v___x_273_; lean_object* v_scopes_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v_opts_277_; uint8_t v___x_278_; uint8_t v___x_279_; 
v___x_273_ = lean_st_ref_get(v___y_145_);
v_scopes_274_ = lean_ctor_get(v___x_273_, 2);
lean_inc(v_scopes_274_);
lean_dec(v___x_273_);
v___x_275_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_276_ = l_List_head_x21___redArg(v___x_275_, v_scopes_274_);
lean_dec(v_scopes_274_);
v_opts_277_ = lean_ctor_get(v___x_276_, 1);
lean_inc_ref(v_opts_277_);
lean_dec(v___x_276_);
v___x_278_ = 1;
v___x_279_ = l_Lean_instBEqMessageSeverity_beq(v_severity_142_, v___x_278_);
if (v___x_279_ == 0)
{
lean_dec_ref(v_opts_277_);
v___y_268_ = v___y_272_;
v___y_269_ = v___y_272_;
v___y_270_ = v___x_279_;
goto v___jp_267_;
}
else
{
lean_object* v___x_280_; uint8_t v___x_281_; 
v___x_280_ = l_Lean_warningAsError;
v___x_281_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__5(v_opts_277_, v___x_280_);
lean_dec_ref(v_opts_277_);
v___y_268_ = v___y_272_;
v___y_269_ = v___y_272_;
v___y_270_ = v___x_281_;
goto v___jp_267_;
}
}
else
{
lean_object* v___x_282_; lean_object* v___x_283_; 
lean_dec_ref(v_msgData_141_);
v___x_282_ = lean_box(0);
v___x_283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
return v___x_283_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___boxed(lean_object* v_ref_286_, lean_object* v_msgData_287_, lean_object* v_severity_288_, lean_object* v_isSilent_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_){
_start:
{
uint8_t v_severity_boxed_293_; uint8_t v_isSilent_boxed_294_; lean_object* v_res_295_; 
v_severity_boxed_293_ = lean_unbox(v_severity_288_);
v_isSilent_boxed_294_ = lean_unbox(v_isSilent_289_);
v_res_295_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3(v_ref_286_, v_msgData_287_, v_severity_boxed_293_, v_isSilent_boxed_294_, v___y_290_, v___y_291_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
lean_dec(v_ref_286_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2(lean_object* v_ref_296_, lean_object* v_msgData_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
uint8_t v___x_301_; uint8_t v___x_302_; lean_object* v___x_303_; 
v___x_301_ = 1;
v___x_302_ = 0;
v___x_303_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3(v_ref_296_, v_msgData_297_, v___x_301_, v___x_302_, v___y_298_, v___y_299_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2___boxed(lean_object* v_ref_304_, lean_object* v_msgData_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2(v_ref_304_, v_msgData_305_, v___y_306_, v___y_307_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
lean_dec(v_ref_304_);
return v_res_309_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__1(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__0));
v___x_312_ = l_Lean_stringToMessageData(v___x_311_);
return v___x_312_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__3(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__2));
v___x_315_ = l_Lean_stringToMessageData(v___x_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1(lean_object* v_linterOption_316_, lean_object* v_stx_317_, lean_object* v_msg_318_, lean_object* v___y_319_, lean_object* v___y_320_){
_start:
{
lean_object* v_name_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_340_; 
v_name_322_ = lean_ctor_get(v_linterOption_316_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v_linterOption_316_);
if (v_isSharedCheck_340_ == 0)
{
lean_object* v_unused_341_; 
v_unused_341_ = lean_ctor_get(v_linterOption_316_, 1);
lean_dec(v_unused_341_);
v___x_324_ = v_linterOption_316_;
v_isShared_325_ = v_isSharedCheck_340_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_name_322_);
lean_dec(v_linterOption_316_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_340_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_329_; 
v___x_326_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__1);
lean_inc(v_name_322_);
v___x_327_ = l_Lean_MessageData_ofName(v_name_322_);
if (v_isShared_325_ == 0)
{
lean_ctor_set_tag(v___x_324_, 7);
lean_ctor_set(v___x_324_, 1, v___x_327_);
lean_ctor_set(v___x_324_, 0, v___x_326_);
v___x_329_ = v___x_324_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_326_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v___x_327_);
v___x_329_ = v_reuseFailAlloc_339_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v_disable_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_330_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__3);
v___x_331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_329_);
lean_ctor_set(v___x_331_, 1, v___x_330_);
v_disable_332_ = l_Lean_MessageData_note(v___x_331_);
v___x_333_ = l_Lean_Linter_linterMessageTag;
v___x_334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_334_, 0, v_msg_318_);
lean_ctor_set(v___x_334_, 1, v_disable_332_);
v___x_335_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_333_);
lean_ctor_set(v___x_335_, 1, v___x_334_);
v___x_336_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_336_, 0, v_name_322_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
lean_inc(v_stx_317_);
v___x_337_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_337_, 0, v_stx_317_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
v___x_338_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2(v_stx_317_, v___x_337_, v___y_319_, v___y_320_);
lean_dec(v_stx_317_);
return v___x_338_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___boxed(lean_object* v_linterOption_342_, lean_object* v_stx_343_, lean_object* v_msg_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1(v_linterOption_342_, v_stx_343_, v_msg_344_, v___y_345_, v___y_346_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0___redArg(lean_object* v_o_349_, lean_object* v___y_350_){
_start:
{
lean_object* v___x_352_; lean_object* v_env_353_; lean_object* v___x_354_; lean_object* v_toEnvExtension_355_; lean_object* v_asyncMode_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v_merged_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_368_; 
v___x_352_ = lean_st_ref_get(v___y_350_);
v_env_353_ = lean_ctor_get(v___x_352_, 0);
lean_inc_ref(v_env_353_);
lean_dec(v___x_352_);
v___x_354_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_355_ = lean_ctor_get(v___x_354_, 0);
v_asyncMode_356_ = lean_ctor_get(v_toEnvExtension_355_, 2);
v___x_357_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_358_ = lean_box(0);
v___x_359_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_357_, v___x_354_, v_env_353_, v_asyncMode_356_, v___x_358_);
v_merged_360_ = lean_ctor_get(v___x_359_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_368_ == 0)
{
lean_object* v_unused_369_; 
v_unused_369_ = lean_ctor_get(v___x_359_, 1);
lean_dec(v_unused_369_);
v___x_362_ = v___x_359_;
v_isShared_363_ = v_isSharedCheck_368_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_merged_360_);
lean_dec(v___x_359_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_368_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_365_; 
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 1, v_merged_360_);
lean_ctor_set(v___x_362_, 0, v_o_349_);
v___x_365_ = v___x_362_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_o_349_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v_merged_360_);
v___x_365_ = v_reuseFailAlloc_367_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
lean_object* v___x_366_; 
v___x_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
return v___x_366_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0___redArg___boxed(lean_object* v_o_370_, lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0___redArg(v_o_370_, v___y_371_);
lean_dec(v___y_371_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0(lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
lean_object* v___x_377_; lean_object* v_scopes_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v_opts_381_; lean_object* v___x_382_; 
v___x_377_ = lean_st_ref_get(v___y_375_);
v_scopes_378_ = lean_ctor_get(v___x_377_, 2);
lean_inc(v_scopes_378_);
lean_dec(v___x_377_);
v___x_379_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_380_ = l_List_head_x21___redArg(v___x_379_, v_scopes_378_);
lean_dec(v_scopes_378_);
v_opts_381_ = lean_ctor_get(v___x_380_, 1);
lean_inc_ref(v_opts_381_);
lean_dec(v___x_380_);
v___x_382_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0___redArg(v_opts_381_, v___y_375_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0___boxed(lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0(v___y_383_, v___y_384_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
return v_res_386_;
}
}
static lean_object* _init_l_Lean_Linter_omit___lam__1___closed__1(void){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = ((lean_object*)(l_Lean_Linter_omit___lam__1___closed__0));
v___x_389_ = l_Lean_stringToMessageData(v___x_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_omit___lam__1(lean_object* v___f_390_, lean_object* v_stx_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v___x_395_; lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_414_; 
v___x_395_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0(v___y_392_, v___y_393_);
v_a_396_ = lean_ctor_get(v___x_395_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_414_ == 0)
{
v___x_398_ = v___x_395_;
v_isShared_399_ = v_isSharedCheck_414_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v___x_395_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_414_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_400_; uint8_t v___x_401_; 
v___x_400_ = l_Lean_Linter_linter_omit;
v___x_401_ = l_Lean_Linter_getLinterValue(v___x_400_, v_a_396_);
lean_dec(v_a_396_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; lean_object* v___x_404_; 
lean_dec(v_stx_391_);
lean_dec_ref(v___f_390_);
v___x_402_ = lean_box(0);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 0, v___x_402_);
v___x_404_ = v___x_398_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_402_);
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
lean_object* v___x_406_; 
v___x_406_ = l_Lean_Syntax_find_x3f(v_stx_391_, v___f_390_);
if (lean_obj_tag(v___x_406_) == 1)
{
lean_object* v_val_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
lean_del_object(v___x_398_);
v_val_407_ = lean_ctor_get(v___x_406_, 0);
lean_inc(v_val_407_);
lean_dec_ref_known(v___x_406_, 1);
v___x_408_ = lean_obj_once(&l_Lean_Linter_omit___lam__1___closed__1, &l_Lean_Linter_omit___lam__1___closed__1_once, _init_l_Lean_Linter_omit___lam__1___closed__1);
v___x_409_ = l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1(v___x_400_, v_val_407_, v___x_408_, v___y_392_, v___y_393_);
return v___x_409_;
}
else
{
lean_object* v___x_410_; lean_object* v___x_412_; 
lean_dec(v___x_406_);
v___x_410_ = lean_box(0);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 0, v___x_410_);
v___x_412_ = v___x_398_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v___x_410_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_omit___lam__1___boxed(lean_object* v___f_415_, lean_object* v_stx_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Lean_Linter_omit___lam__1(v___f_415_, v_stx_416_, v___y_417_, v___y_418_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0(lean_object* v_o_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0___redArg(v_o_432_, v___y_434_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0___boxed(lean_object* v_o_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0(v_o_437_, v___y_438_, v___y_439_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4(lean_object* v_msgData_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg(v_msgData_442_, v___y_444_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msgData_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4(v_msgData_447_, v___y_448_, v___y_449_);
lean_dec(v___y_449_);
lean_dec_ref(v___y_448_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3756037646____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = ((lean_object*)(l_Lean_Linter_omit));
v___x_454_ = l_Lean_Elab_Command_addLinter(v___x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3756037646____hygCtx___hyg_2____boxed(lean_object* v_a_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l___private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3756037646____hygCtx___hyg_2_();
return v_res_456_;
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
