// Lean compiler output
// Module: Lean.Log
// Imports: public import Lean.ErrorExplanation
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
extern lean_object* l_Lean_KVMap_instValueBool;
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_stripNestedTags(lean_object*);
lean_object* l_Lean_MessageData_errorName_x3f(lean_object*);
uint64_t lean_string_hash(lean_object*);
extern lean_object* l_Lean_manualRoot;
extern lean_object* l_Lean_errorExplanationManualDomain;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_MessageData_composePreservingKind(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Option_get___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_MessageData_tagWithErrorName(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadLogOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadLogOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadLogOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPos___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPos___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPos___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPos(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPosition___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPosition___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPosition___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPosition___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPosition(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Log_0__Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Log_0__Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Log_0__Lean_initFn___closed__0_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "warningAsError"};
static const lean_object* l___private_Lean_Log_0__Lean_initFn___closed__0_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Log_0__Lean_initFn___closed__0_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Log_0__Lean_initFn___closed__1_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Log_0__Lean_initFn___closed__0_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(67, 210, 29, 118, 39, 158, 180, 72)}};
static const lean_object* l___private_Lean_Log_0__Lean_initFn___closed__1_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Log_0__Lean_initFn___closed__1_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Log_0__Lean_initFn___closed__2_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "treat warnings as errors"};
static const lean_object* l___private_Lean_Log_0__Lean_initFn___closed__2_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Log_0__Lean_initFn___closed__2_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Log_0__Lean_initFn___closed__3_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Log_0__Lean_initFn___closed__2_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Log_0__Lean_initFn___closed__3_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Log_0__Lean_initFn___closed__3_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Log_0__Lean_initFn___closed__4_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Log_0__Lean_initFn___closed__4_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Log_0__Lean_initFn___closed__4_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Log_0__Lean_initFn___closed__5_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Log_0__Lean_initFn___closed__4_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Log_0__Lean_initFn___closed__5_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Log_0__Lean_initFn___closed__5_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Log_0__Lean_initFn___closed__0_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(82, 127, 119, 5, 244, 162, 222, 133)}};
static const lean_object* l___private_Lean_Log_0__Lean_initFn___closed__5_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Log_0__Lean_initFn___closed__5_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Log_0__Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Log_0__Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_warningAsError;
static const lean_string_object l_Lean_errorDescriptionWidget___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 623, .m_capacity = 623, .m_length = 622, .m_data = "\nimport { createElement } from 'react';\n\nexport default function ({ code, explanationUrl }) {\n  const sansText = { fontFamily: 'var(--vscode-font-family)' }\n\n  const codeSpan = createElement('span', {}, [\n    createElement('span', { style: sansText }, 'Error code: '), code])\n  const brSpan = createElement('span', {}, '\\n')\n  const linkSpan = createElement('span', { style: sansText },\n    createElement('a', { href: explanationUrl, target: '_blank', rel: 'noreferrer noopener' },\n      'View explanation'))\n\n  const all = createElement('div', { style: { marginTop: '1em' } }, [codeSpan, brSpan, linkSpan])\n  return all\n}"};
static const lean_object* l_Lean_errorDescriptionWidget___closed__0 = (const lean_object*)&l_Lean_errorDescriptionWidget___closed__0_value;
static lean_once_cell_t l_Lean_errorDescriptionWidget___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_errorDescriptionWidget___closed__1;
static lean_once_cell_t l_Lean_errorDescriptionWidget___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_errorDescriptionWidget___closed__2;
LEAN_EXPORT lean_object* l_Lean_errorDescriptionWidget;
LEAN_EXPORT lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___lam__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "find/\?domain="};
static const lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__0 = (const lean_object*)&l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__0_value;
static lean_once_cell_t l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__1;
static const lean_string_object l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "&name="};
static const lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__2 = (const lean_object*)&l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__2_value;
static lean_once_cell_t l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__3;
static const lean_string_object l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "errorDescriptionWidget"};
static const lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__4 = (const lean_object*)&l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__4_value;
static const lean_ctor_object l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Log_0__Lean_initFn___closed__4_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__4_value),LEAN_SCALAR_PTR_LITERAL(97, 213, 240, 52, 84, 173, 13, 164)}};
static const lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__5 = (const lean_object*)&l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__5_value;
static const lean_string_object l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "code"};
static const lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__6 = (const lean_object*)&l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__6_value;
static const lean_string_object l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "explanationUrl"};
static const lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__7 = (const lean_object*)&l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
static const lean_string_object l_Lean_logAt___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__2(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__3(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__4(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_logAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logNamedErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logNamedErrorAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logNamedWarningAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logNamedWarningAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfoAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfoAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_log___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_log___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logNamedError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logNamedError(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logNamedWarning___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logNamedWarning(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logUnknownDecl___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "unknown declaration '"};
static const lean_object* l_Lean_logUnknownDecl___redArg___closed__0 = (const lean_object*)&l_Lean_logUnknownDecl___redArg___closed__0_value;
static lean_once_cell_t l_Lean_logUnknownDecl___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_logUnknownDecl___redArg___closed__1;
static const lean_string_object l_Lean_logUnknownDecl___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_logUnknownDecl___redArg___closed__2 = (const lean_object*)&l_Lean_logUnknownDecl___redArg___closed__2_value;
static lean_once_cell_t l_Lean_logUnknownDecl___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_logUnknownDecl___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_logUnknownDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logUnknownDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadLogOfMonadLift___redArg___lam__0(lean_object* v_logMessage_1_, lean_object* v_inst_2_, lean_object* v_msg_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_apply_1(v_logMessage_1_, v_msg_3_);
v___x_5_ = lean_apply_2(v_inst_2_, lean_box(0), v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLogOfMonadLift___redArg(lean_object* v_inst_6_, lean_object* v_inst_7_){
_start:
{
lean_object* v_toMonadFileMap_8_; lean_object* v_getRef_9_; lean_object* v_getFileName_10_; lean_object* v_hasErrors_11_; lean_object* v_logMessage_12_; lean_object* v___x_14_; uint8_t v_isShared_15_; uint8_t v_isSharedCheck_24_; 
v_toMonadFileMap_8_ = lean_ctor_get(v_inst_7_, 0);
v_getRef_9_ = lean_ctor_get(v_inst_7_, 1);
v_getFileName_10_ = lean_ctor_get(v_inst_7_, 2);
v_hasErrors_11_ = lean_ctor_get(v_inst_7_, 3);
v_logMessage_12_ = lean_ctor_get(v_inst_7_, 4);
v_isSharedCheck_24_ = !lean_is_exclusive(v_inst_7_);
if (v_isSharedCheck_24_ == 0)
{
v___x_14_ = v_inst_7_;
v_isShared_15_ = v_isSharedCheck_24_;
goto v_resetjp_13_;
}
else
{
lean_inc(v_logMessage_12_);
lean_inc(v_hasErrors_11_);
lean_inc(v_getFileName_10_);
lean_inc(v_getRef_9_);
lean_inc(v_toMonadFileMap_8_);
lean_dec(v_inst_7_);
v___x_14_ = lean_box(0);
v_isShared_15_ = v_isSharedCheck_24_;
goto v_resetjp_13_;
}
v_resetjp_13_:
{
lean_object* v___f_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_22_; 
lean_inc_n(v_inst_6_, 4);
v___f_16_ = lean_alloc_closure((void*)(l_Lean_instMonadLogOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_16_, 0, v_logMessage_12_);
lean_closure_set(v___f_16_, 1, v_inst_6_);
v___x_17_ = lean_apply_2(v_inst_6_, lean_box(0), v_toMonadFileMap_8_);
v___x_18_ = lean_apply_2(v_inst_6_, lean_box(0), v_getRef_9_);
v___x_19_ = lean_apply_2(v_inst_6_, lean_box(0), v_getFileName_10_);
v___x_20_ = lean_apply_2(v_inst_6_, lean_box(0), v_hasErrors_11_);
if (v_isShared_15_ == 0)
{
lean_ctor_set(v___x_14_, 4, v___f_16_);
lean_ctor_set(v___x_14_, 3, v___x_20_);
lean_ctor_set(v___x_14_, 2, v___x_19_);
lean_ctor_set(v___x_14_, 1, v___x_18_);
lean_ctor_set(v___x_14_, 0, v___x_17_);
v___x_22_ = v___x_14_;
goto v_reusejp_21_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v___x_17_);
lean_ctor_set(v_reuseFailAlloc_23_, 1, v___x_18_);
lean_ctor_set(v_reuseFailAlloc_23_, 2, v___x_19_);
lean_ctor_set(v_reuseFailAlloc_23_, 3, v___x_20_);
lean_ctor_set(v_reuseFailAlloc_23_, 4, v___f_16_);
v___x_22_ = v_reuseFailAlloc_23_;
goto v_reusejp_21_;
}
v_reusejp_21_:
{
return v___x_22_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLogOfMonadLift(lean_object* v_m_25_, lean_object* v_n_26_, lean_object* v_inst_27_, lean_object* v_inst_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Lean_instMonadLogOfMonadLift___redArg(v_inst_27_, v_inst_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___redArg___lam__0(lean_object* v_toPure_30_, lean_object* v_ref_31_){
_start:
{
uint8_t v___x_32_; lean_object* v___x_33_; 
v___x_32_ = 0;
v___x_33_ = l_Lean_Syntax_getPos_x3f(v_ref_31_, v___x_32_);
if (lean_obj_tag(v___x_33_) == 0)
{
lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_34_ = lean_unsigned_to_nat(0u);
v___x_35_ = lean_apply_2(v_toPure_30_, lean_box(0), v___x_34_);
return v___x_35_;
}
else
{
lean_object* v_val_36_; lean_object* v___x_37_; 
v_val_36_ = lean_ctor_get(v___x_33_, 0);
lean_inc(v_val_36_);
lean_dec_ref_known(v___x_33_, 1);
v___x_37_ = lean_apply_2(v_toPure_30_, lean_box(0), v_val_36_);
return v___x_37_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___redArg___lam__0___boxed(lean_object* v_toPure_38_, lean_object* v_ref_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_getRefPos___redArg___lam__0(v_toPure_38_, v_ref_39_);
lean_dec(v_ref_39_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___redArg(lean_object* v_inst_41_, lean_object* v_inst_42_){
_start:
{
lean_object* v_toApplicative_43_; lean_object* v_toBind_44_; lean_object* v_getRef_45_; lean_object* v_toPure_46_; lean_object* v___f_47_; lean_object* v___x_48_; 
v_toApplicative_43_ = lean_ctor_get(v_inst_41_, 0);
lean_inc_ref(v_toApplicative_43_);
v_toBind_44_ = lean_ctor_get(v_inst_41_, 1);
lean_inc(v_toBind_44_);
lean_dec_ref(v_inst_41_);
v_getRef_45_ = lean_ctor_get(v_inst_42_, 1);
lean_inc(v_getRef_45_);
lean_dec_ref(v_inst_42_);
v_toPure_46_ = lean_ctor_get(v_toApplicative_43_, 1);
lean_inc(v_toPure_46_);
lean_dec_ref(v_toApplicative_43_);
v___f_47_ = lean_alloc_closure((void*)(l_Lean_getRefPos___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_47_, 0, v_toPure_46_);
v___x_48_ = lean_apply_4(v_toBind_44_, lean_box(0), lean_box(0), v_getRef_45_, v___f_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos(lean_object* v_m_49_, lean_object* v_inst_50_, lean_object* v_inst_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Lean_getRefPos___redArg(v_inst_50_, v_inst_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPosition___redArg___lam__0(lean_object* v_fileMap_53_, lean_object* v_toPure_54_, lean_object* v_____do__lift_55_){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_56_ = l_Lean_FileMap_toPosition(v_fileMap_53_, v_____do__lift_55_);
v___x_57_ = lean_apply_2(v_toPure_54_, lean_box(0), v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPosition___redArg___lam__0___boxed(lean_object* v_fileMap_58_, lean_object* v_toPure_59_, lean_object* v_____do__lift_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_Lean_getRefPosition___redArg___lam__0(v_fileMap_58_, v_toPure_59_, v_____do__lift_60_);
lean_dec(v_____do__lift_60_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPosition___redArg___lam__1(lean_object* v_toPure_62_, lean_object* v_inst_63_, lean_object* v_inst_64_, lean_object* v_toBind_65_, lean_object* v_fileMap_66_){
_start:
{
lean_object* v___f_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___f_67_ = lean_alloc_closure((void*)(l_Lean_getRefPosition___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_67_, 0, v_fileMap_66_);
lean_closure_set(v___f_67_, 1, v_toPure_62_);
v___x_68_ = l_Lean_getRefPos___redArg(v_inst_63_, v_inst_64_);
v___x_69_ = lean_apply_4(v_toBind_65_, lean_box(0), lean_box(0), v___x_68_, v___f_67_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPosition___redArg(lean_object* v_inst_70_, lean_object* v_inst_71_){
_start:
{
lean_object* v_toApplicative_72_; lean_object* v_toBind_73_; lean_object* v_toMonadFileMap_74_; lean_object* v_toPure_75_; lean_object* v___f_76_; lean_object* v___x_77_; 
v_toApplicative_72_ = lean_ctor_get(v_inst_70_, 0);
v_toBind_73_ = lean_ctor_get(v_inst_70_, 1);
lean_inc_n(v_toBind_73_, 2);
v_toMonadFileMap_74_ = lean_ctor_get(v_inst_71_, 0);
lean_inc(v_toMonadFileMap_74_);
v_toPure_75_ = lean_ctor_get(v_toApplicative_72_, 1);
lean_inc(v_toPure_75_);
v___f_76_ = lean_alloc_closure((void*)(l_Lean_getRefPosition___redArg___lam__1), 5, 4);
lean_closure_set(v___f_76_, 0, v_toPure_75_);
lean_closure_set(v___f_76_, 1, v_inst_70_);
lean_closure_set(v___f_76_, 2, v_inst_71_);
lean_closure_set(v___f_76_, 3, v_toBind_73_);
v___x_77_ = lean_apply_4(v_toBind_73_, lean_box(0), lean_box(0), v_toMonadFileMap_74_, v___f_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPosition(lean_object* v_m_78_, lean_object* v_inst_79_, lean_object* v_inst_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = l_Lean_getRefPosition___redArg(v_inst_79_, v_inst_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Log_0__Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__spec__0(lean_object* v_name_82_, lean_object* v_decl_83_, lean_object* v_ref_84_){
_start:
{
lean_object* v_defValue_86_; lean_object* v_descr_87_; lean_object* v_deprecation_x3f_88_; lean_object* v___x_89_; uint8_t v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v_defValue_86_ = lean_ctor_get(v_decl_83_, 0);
v_descr_87_ = lean_ctor_get(v_decl_83_, 1);
v_deprecation_x3f_88_ = lean_ctor_get(v_decl_83_, 2);
v___x_89_ = lean_alloc_ctor(1, 0, 1);
v___x_90_ = lean_unbox(v_defValue_86_);
lean_ctor_set_uint8(v___x_89_, 0, v___x_90_);
lean_inc(v_deprecation_x3f_88_);
lean_inc_ref(v_descr_87_);
lean_inc_n(v_name_82_, 2);
v___x_91_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_91_, 0, v_name_82_);
lean_ctor_set(v___x_91_, 1, v_ref_84_);
lean_ctor_set(v___x_91_, 2, v___x_89_);
lean_ctor_set(v___x_91_, 3, v_descr_87_);
lean_ctor_set(v___x_91_, 4, v_deprecation_x3f_88_);
v___x_92_ = lean_register_option(v_name_82_, v___x_91_);
if (lean_obj_tag(v___x_92_) == 0)
{
lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_100_; 
v_isSharedCheck_100_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_100_ == 0)
{
lean_object* v_unused_101_; 
v_unused_101_ = lean_ctor_get(v___x_92_, 0);
lean_dec(v_unused_101_);
v___x_94_ = v___x_92_;
v_isShared_95_ = v_isSharedCheck_100_;
goto v_resetjp_93_;
}
else
{
lean_dec(v___x_92_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_100_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_96_; lean_object* v___x_98_; 
lean_inc(v_defValue_86_);
v___x_96_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_96_, 0, v_name_82_);
lean_ctor_set(v___x_96_, 1, v_defValue_86_);
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 0, v___x_96_);
v___x_98_ = v___x_94_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v___x_96_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
else
{
lean_object* v_a_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_109_; 
lean_dec(v_name_82_);
v_a_102_ = lean_ctor_get(v___x_92_, 0);
v_isSharedCheck_109_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_109_ == 0)
{
v___x_104_ = v___x_92_;
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_a_102_);
lean_dec(v___x_92_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_107_; 
if (v_isShared_105_ == 0)
{
v___x_107_ = v___x_104_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_a_102_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Log_0__Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_110_, lean_object* v_decl_111_, lean_object* v_ref_112_, lean_object* v_a_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lean_Option_register___at___00__private_Lean_Log_0__Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__spec__0(v_name_110_, v_decl_111_, v_ref_112_);
lean_dec_ref(v_decl_111_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Log_0__Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_129_ = ((lean_object*)(l___private_Lean_Log_0__Lean_initFn___closed__1_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_));
v___x_130_ = ((lean_object*)(l___private_Lean_Log_0__Lean_initFn___closed__3_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_));
v___x_131_ = ((lean_object*)(l___private_Lean_Log_0__Lean_initFn___closed__5_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_));
v___x_132_ = l_Lean_Option_register___at___00__private_Lean_Log_0__Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__spec__0(v___x_129_, v___x_130_, v___x_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Log_0__Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4____boxed(lean_object* v_a_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l___private_Lean_Log_0__Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_();
return v_res_134_;
}
}
static uint64_t _init_l_Lean_errorDescriptionWidget___closed__1(void){
_start:
{
lean_object* v___x_136_; uint64_t v___x_137_; 
v___x_136_ = ((lean_object*)(l_Lean_errorDescriptionWidget___closed__0));
v___x_137_ = lean_string_hash(v___x_136_);
return v___x_137_;
}
}
static lean_object* _init_l_Lean_errorDescriptionWidget___closed__2(void){
_start:
{
uint64_t v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_138_ = lean_uint64_once(&l_Lean_errorDescriptionWidget___closed__1, &l_Lean_errorDescriptionWidget___closed__1_once, _init_l_Lean_errorDescriptionWidget___closed__1);
v___x_139_ = ((lean_object*)(l_Lean_errorDescriptionWidget___closed__0));
v___x_140_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_140_, 0, v___x_139_);
lean_ctor_set_uint64(v___x_140_, sizeof(void*)*1, v___x_138_);
return v___x_140_;
}
}
static lean_object* _init_l_Lean_errorDescriptionWidget(void){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = lean_obj_once(&l_Lean_errorDescriptionWidget___closed__2, &l_Lean_errorDescriptionWidget___closed__2_once, _init_l_Lean_errorDescriptionWidget___closed__2);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___lam__0(lean_object* v___x_142_, lean_object* v___y_143_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_142_);
lean_ctor_set(v___x_144_, 1, v___y_143_);
return v___x_144_;
}
}
static lean_object* _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__1(void){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_146_ = l_Lean_errorExplanationManualDomain;
v___x_147_ = ((lean_object*)(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__0));
v___x_148_ = lean_string_append(v___x_147_, v___x_146_);
return v___x_148_;
}
}
static lean_object* _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__3(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_150_ = ((lean_object*)(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__2));
v___x_151_ = lean_obj_once(&l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__1, &l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__1_once, _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__1);
v___x_152_ = lean_string_append(v___x_151_, v___x_150_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object* v_msg_159_){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; 
lean_inc_ref(v_msg_159_);
v___x_160_ = l_Lean_MessageData_stripNestedTags(v_msg_159_);
v___x_161_ = l_Lean_MessageData_errorName_x3f(v___x_160_);
lean_dec_ref(v___x_160_);
if (lean_obj_tag(v___x_161_) == 0)
{
return v_msg_159_;
}
else
{
lean_object* v_val_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_192_; 
v_val_162_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_192_ == 0)
{
v___x_164_ = v___x_161_;
v_isShared_165_ = v_isSharedCheck_192_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_val_162_);
lean_dec(v___x_161_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_192_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_166_; uint64_t v_javascriptHash_167_; lean_object* v___x_168_; lean_object* v___x_169_; uint8_t v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v_url_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_177_; 
v___x_166_ = l_Lean_errorDescriptionWidget;
v_javascriptHash_167_ = lean_ctor_get_uint64(v___x_166_, sizeof(void*)*1);
v___x_168_ = l_Lean_manualRoot;
v___x_169_ = lean_obj_once(&l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__3, &l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__3_once, _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__3);
v___x_170_ = 1;
v___x_171_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_162_, v___x_170_);
v___x_172_ = lean_string_append(v___x_169_, v___x_171_);
v_url_173_ = lean_string_append(v___x_168_, v___x_172_);
lean_dec_ref(v___x_172_);
v___x_174_ = ((lean_object*)(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__5));
v___x_175_ = ((lean_object*)(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__6));
if (v_isShared_165_ == 0)
{
lean_ctor_set_tag(v___x_164_, 3);
lean_ctor_set(v___x_164_, 0, v___x_171_);
v___x_177_ = v___x_164_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_171_);
v___x_177_ = v_reuseFailAlloc_191_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___f_186_; lean_object* v_inst_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_175_);
lean_ctor_set(v___x_178_, 1, v___x_177_);
v___x_179_ = ((lean_object*)(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__7));
v___x_180_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_180_, 0, v_url_173_);
v___x_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_179_);
lean_ctor_set(v___x_181_, 1, v___x_180_);
v___x_182_ = lean_box(0);
v___x_183_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_181_);
lean_ctor_set(v___x_183_, 1, v___x_182_);
v___x_184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_178_);
lean_ctor_set(v___x_184_, 1, v___x_183_);
v___x_185_ = l_Lean_Json_mkObj(v___x_184_);
lean_dec_ref_known(v___x_184_, 2);
v___f_186_ = lean_alloc_closure((void*)(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___lam__0), 2, 1);
lean_closure_set(v___f_186_, 0, v___x_185_);
v_inst_187_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v_inst_187_, 0, v___x_174_);
lean_ctor_set(v_inst_187_, 1, v___f_186_);
lean_ctor_set_uint64(v_inst_187_, sizeof(void*)*2, v_javascriptHash_167_);
v___x_188_ = l_Lean_MessageData_nil;
v___x_189_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_189_, 0, v_inst_187_);
lean_ctor_set(v___x_189_, 1, v___x_188_);
v___x_190_ = l_Lean_MessageData_composePreservingKind(v_msg_159_, v___x_189_);
return v___x_190_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__0(lean_object* v_fileMap_194_, lean_object* v___y_195_, lean_object* v___y_196_, uint8_t v___y_197_, uint8_t v___y_198_, uint8_t v_isSilent_199_, lean_object* v_msgData_200_, lean_object* v_logMessage_201_, lean_object* v_____do__lift_202_){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
lean_inc_ref(v_fileMap_194_);
v___x_203_ = l_Lean_FileMap_toPosition(v_fileMap_194_, v___y_195_);
v___x_204_ = l_Lean_FileMap_toPosition(v_fileMap_194_, v___y_196_);
v___x_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
v___x_206_ = ((lean_object*)(l_Lean_logAt___redArg___lam__0___closed__0));
v___x_207_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_207_, 0, v_____do__lift_202_);
lean_ctor_set(v___x_207_, 1, v___x_203_);
lean_ctor_set(v___x_207_, 2, v___x_205_);
lean_ctor_set(v___x_207_, 3, v___x_206_);
lean_ctor_set(v___x_207_, 4, v_msgData_200_);
lean_ctor_set_uint8(v___x_207_, sizeof(void*)*5, v___y_197_);
lean_ctor_set_uint8(v___x_207_, sizeof(void*)*5 + 1, v___y_198_);
lean_ctor_set_uint8(v___x_207_, sizeof(void*)*5 + 2, v_isSilent_199_);
v___x_208_ = lean_apply_1(v_logMessage_201_, v___x_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__0___boxed(lean_object* v_fileMap_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v_isSilent_214_, lean_object* v_msgData_215_, lean_object* v_logMessage_216_, lean_object* v_____do__lift_217_){
_start:
{
uint8_t v___y_229__boxed_218_; uint8_t v___y_230__boxed_219_; uint8_t v_isSilent_boxed_220_; lean_object* v_res_221_; 
v___y_229__boxed_218_ = lean_unbox(v___y_212_);
v___y_230__boxed_219_ = lean_unbox(v___y_213_);
v_isSilent_boxed_220_ = lean_unbox(v_isSilent_214_);
v_res_221_ = l_Lean_logAt___redArg___lam__0(v_fileMap_209_, v___y_210_, v___y_211_, v___y_229__boxed_218_, v___y_230__boxed_219_, v_isSilent_boxed_220_, v_msgData_215_, v_logMessage_216_, v_____do__lift_217_);
lean_dec(v___y_211_);
lean_dec(v___y_210_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__1(lean_object* v_fileMap_222_, lean_object* v___y_223_, lean_object* v___y_224_, uint8_t v___y_225_, uint8_t v___y_226_, uint8_t v_isSilent_227_, lean_object* v_logMessage_228_, lean_object* v_toBind_229_, lean_object* v_getFileName_230_, lean_object* v_msgData_231_){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___f_235_; lean_object* v___x_236_; 
v___x_232_ = lean_box(v___y_225_);
v___x_233_ = lean_box(v___y_226_);
v___x_234_ = lean_box(v_isSilent_227_);
v___f_235_ = lean_alloc_closure((void*)(l_Lean_logAt___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_235_, 0, v_fileMap_222_);
lean_closure_set(v___f_235_, 1, v___y_223_);
lean_closure_set(v___f_235_, 2, v___y_224_);
lean_closure_set(v___f_235_, 3, v___x_232_);
lean_closure_set(v___f_235_, 4, v___x_233_);
lean_closure_set(v___f_235_, 5, v___x_234_);
lean_closure_set(v___f_235_, 6, v_msgData_231_);
lean_closure_set(v___f_235_, 7, v_logMessage_228_);
v___x_236_ = lean_apply_4(v_toBind_229_, lean_box(0), lean_box(0), v_getFileName_230_, v___f_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__1___boxed(lean_object* v_fileMap_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v_isSilent_242_, lean_object* v_logMessage_243_, lean_object* v_toBind_244_, lean_object* v_getFileName_245_, lean_object* v_msgData_246_){
_start:
{
uint8_t v___y_257__boxed_247_; uint8_t v___y_258__boxed_248_; uint8_t v_isSilent_boxed_249_; lean_object* v_res_250_; 
v___y_257__boxed_247_ = lean_unbox(v___y_240_);
v___y_258__boxed_248_ = lean_unbox(v___y_241_);
v_isSilent_boxed_249_ = lean_unbox(v_isSilent_242_);
v_res_250_ = l_Lean_logAt___redArg___lam__1(v_fileMap_237_, v___y_238_, v___y_239_, v___y_257__boxed_247_, v___y_258__boxed_248_, v_isSilent_boxed_249_, v_logMessage_243_, v_toBind_244_, v_getFileName_245_, v_msgData_246_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__2(lean_object* v___y_251_, lean_object* v___y_252_, uint8_t v___y_253_, uint8_t v___y_254_, uint8_t v_isSilent_255_, lean_object* v_logMessage_256_, lean_object* v_toBind_257_, lean_object* v_getFileName_258_, lean_object* v_msgData_259_, lean_object* v_inst_260_, lean_object* v_fileMap_261_){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___f_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_262_ = lean_box(v___y_253_);
v___x_263_ = lean_box(v___y_254_);
v___x_264_ = lean_box(v_isSilent_255_);
lean_inc(v_toBind_257_);
v___f_265_ = lean_alloc_closure((void*)(l_Lean_logAt___redArg___lam__1___boxed), 10, 9);
lean_closure_set(v___f_265_, 0, v_fileMap_261_);
lean_closure_set(v___f_265_, 1, v___y_251_);
lean_closure_set(v___f_265_, 2, v___y_252_);
lean_closure_set(v___f_265_, 3, v___x_262_);
lean_closure_set(v___f_265_, 4, v___x_263_);
lean_closure_set(v___f_265_, 5, v___x_264_);
lean_closure_set(v___f_265_, 6, v_logMessage_256_);
lean_closure_set(v___f_265_, 7, v_toBind_257_);
lean_closure_set(v___f_265_, 8, v_getFileName_258_);
v___x_266_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_259_);
v___x_267_ = lean_apply_1(v_inst_260_, v___x_266_);
v___x_268_ = lean_apply_4(v_toBind_257_, lean_box(0), lean_box(0), v___x_267_, v___f_265_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__2___boxed(lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v_isSilent_273_, lean_object* v_logMessage_274_, lean_object* v_toBind_275_, lean_object* v_getFileName_276_, lean_object* v_msgData_277_, lean_object* v_inst_278_, lean_object* v_fileMap_279_){
_start:
{
uint8_t v___y_279__boxed_280_; uint8_t v___y_280__boxed_281_; uint8_t v_isSilent_boxed_282_; lean_object* v_res_283_; 
v___y_279__boxed_280_ = lean_unbox(v___y_271_);
v___y_280__boxed_281_ = lean_unbox(v___y_272_);
v_isSilent_boxed_282_ = lean_unbox(v_isSilent_273_);
v_res_283_ = l_Lean_logAt___redArg___lam__2(v___y_269_, v___y_270_, v___y_279__boxed_280_, v___y_280__boxed_281_, v_isSilent_boxed_282_, v_logMessage_274_, v_toBind_275_, v_getFileName_276_, v_msgData_277_, v_inst_278_, v_fileMap_279_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__3(lean_object* v_ref_284_, uint8_t v___y_285_, uint8_t v___y_286_, uint8_t v_isSilent_287_, lean_object* v_logMessage_288_, lean_object* v_toBind_289_, lean_object* v_getFileName_290_, lean_object* v_msgData_291_, lean_object* v_inst_292_, lean_object* v_toMonadFileMap_293_, lean_object* v_____do__lift_294_){
_start:
{
lean_object* v___y_296_; lean_object* v___y_297_; lean_object* v_ref_303_; lean_object* v___y_305_; lean_object* v___x_308_; 
v_ref_303_ = l_Lean_replaceRef(v_ref_284_, v_____do__lift_294_);
v___x_308_ = l_Lean_Syntax_getPos_x3f(v_ref_303_, v___y_285_);
if (lean_obj_tag(v___x_308_) == 0)
{
lean_object* v___x_309_; 
v___x_309_ = lean_unsigned_to_nat(0u);
v___y_305_ = v___x_309_;
goto v___jp_304_;
}
else
{
lean_object* v_val_310_; 
v_val_310_ = lean_ctor_get(v___x_308_, 0);
lean_inc(v_val_310_);
lean_dec_ref_known(v___x_308_, 1);
v___y_305_ = v_val_310_;
goto v___jp_304_;
}
v___jp_295_:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___f_301_; lean_object* v___x_302_; 
v___x_298_ = lean_box(v___y_285_);
v___x_299_ = lean_box(v___y_286_);
v___x_300_ = lean_box(v_isSilent_287_);
lean_inc(v_toBind_289_);
v___f_301_ = lean_alloc_closure((void*)(l_Lean_logAt___redArg___lam__2___boxed), 11, 10);
lean_closure_set(v___f_301_, 0, v___y_296_);
lean_closure_set(v___f_301_, 1, v___y_297_);
lean_closure_set(v___f_301_, 2, v___x_298_);
lean_closure_set(v___f_301_, 3, v___x_299_);
lean_closure_set(v___f_301_, 4, v___x_300_);
lean_closure_set(v___f_301_, 5, v_logMessage_288_);
lean_closure_set(v___f_301_, 6, v_toBind_289_);
lean_closure_set(v___f_301_, 7, v_getFileName_290_);
lean_closure_set(v___f_301_, 8, v_msgData_291_);
lean_closure_set(v___f_301_, 9, v_inst_292_);
v___x_302_ = lean_apply_4(v_toBind_289_, lean_box(0), lean_box(0), v_toMonadFileMap_293_, v___f_301_);
return v___x_302_;
}
v___jp_304_:
{
lean_object* v___x_306_; 
v___x_306_ = l_Lean_Syntax_getTailPos_x3f(v_ref_303_, v___y_285_);
lean_dec(v_ref_303_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_inc(v___y_305_);
v___y_296_ = v___y_305_;
v___y_297_ = v___y_305_;
goto v___jp_295_;
}
else
{
lean_object* v_val_307_; 
v_val_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc(v_val_307_);
lean_dec_ref_known(v___x_306_, 1);
v___y_296_ = v___y_305_;
v___y_297_ = v_val_307_;
goto v___jp_295_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__3___boxed(lean_object* v_ref_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v_isSilent_314_, lean_object* v_logMessage_315_, lean_object* v_toBind_316_, lean_object* v_getFileName_317_, lean_object* v_msgData_318_, lean_object* v_inst_319_, lean_object* v_toMonadFileMap_320_, lean_object* v_____do__lift_321_){
_start:
{
uint8_t v___y_307__boxed_322_; uint8_t v___y_308__boxed_323_; uint8_t v_isSilent_boxed_324_; lean_object* v_res_325_; 
v___y_307__boxed_322_ = lean_unbox(v___y_312_);
v___y_308__boxed_323_ = lean_unbox(v___y_313_);
v_isSilent_boxed_324_ = lean_unbox(v_isSilent_314_);
v_res_325_ = l_Lean_logAt___redArg___lam__3(v_ref_311_, v___y_307__boxed_322_, v___y_308__boxed_323_, v_isSilent_boxed_324_, v_logMessage_315_, v_toBind_316_, v_getFileName_317_, v_msgData_318_, v_inst_319_, v_toMonadFileMap_320_, v_____do__lift_321_);
lean_dec(v_____do__lift_321_);
lean_dec(v_ref_311_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__4(lean_object* v_ref_326_, uint8_t v___y_327_, uint8_t v_isSilent_328_, lean_object* v_logMessage_329_, lean_object* v_toBind_330_, lean_object* v_getFileName_331_, lean_object* v_msgData_332_, lean_object* v_inst_333_, lean_object* v_toMonadFileMap_334_, lean_object* v_getRef_335_, uint8_t v_severity_336_, uint8_t v___x_337_, lean_object* v___x_338_, lean_object* v_____do__lift_339_){
_start:
{
uint8_t v___y_341_; uint8_t v___y_348_; uint8_t v___x_349_; uint8_t v___x_350_; 
v___x_349_ = 1;
v___x_350_ = l_Lean_instBEqMessageSeverity_beq(v_severity_336_, v___x_349_);
if (v___x_350_ == 0)
{
lean_dec_ref(v___x_338_);
v___y_348_ = v___x_350_;
goto v___jp_347_;
}
else
{
lean_object* v___x_351_; lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_351_ = l_Lean_warningAsError;
v___x_352_ = l_Lean_Option_get___redArg(v___x_338_, v_____do__lift_339_, v___x_351_);
v___x_353_ = lean_unbox(v___x_352_);
lean_dec(v___x_352_);
v___y_348_ = v___x_353_;
goto v___jp_347_;
}
v___jp_340_:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___f_345_; lean_object* v___x_346_; 
v___x_342_ = lean_box(v___y_327_);
v___x_343_ = lean_box(v___y_341_);
v___x_344_ = lean_box(v_isSilent_328_);
lean_inc(v_toBind_330_);
v___f_345_ = lean_alloc_closure((void*)(l_Lean_logAt___redArg___lam__3___boxed), 11, 10);
lean_closure_set(v___f_345_, 0, v_ref_326_);
lean_closure_set(v___f_345_, 1, v___x_342_);
lean_closure_set(v___f_345_, 2, v___x_343_);
lean_closure_set(v___f_345_, 3, v___x_344_);
lean_closure_set(v___f_345_, 4, v_logMessage_329_);
lean_closure_set(v___f_345_, 5, v_toBind_330_);
lean_closure_set(v___f_345_, 6, v_getFileName_331_);
lean_closure_set(v___f_345_, 7, v_msgData_332_);
lean_closure_set(v___f_345_, 8, v_inst_333_);
lean_closure_set(v___f_345_, 9, v_toMonadFileMap_334_);
v___x_346_ = lean_apply_4(v_toBind_330_, lean_box(0), lean_box(0), v_getRef_335_, v___f_345_);
return v___x_346_;
}
v___jp_347_:
{
if (v___y_348_ == 0)
{
v___y_341_ = v_severity_336_;
goto v___jp_340_;
}
else
{
v___y_341_ = v___x_337_;
goto v___jp_340_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__4___boxed(lean_object* v_ref_354_, lean_object* v___y_355_, lean_object* v_isSilent_356_, lean_object* v_logMessage_357_, lean_object* v_toBind_358_, lean_object* v_getFileName_359_, lean_object* v_msgData_360_, lean_object* v_inst_361_, lean_object* v_toMonadFileMap_362_, lean_object* v_getRef_363_, lean_object* v_severity_364_, lean_object* v___x_365_, lean_object* v___x_366_, lean_object* v_____do__lift_367_){
_start:
{
uint8_t v___y_349__boxed_368_; uint8_t v_isSilent_boxed_369_; uint8_t v_severity_boxed_370_; uint8_t v___x_351__boxed_371_; lean_object* v_res_372_; 
v___y_349__boxed_368_ = lean_unbox(v___y_355_);
v_isSilent_boxed_369_ = lean_unbox(v_isSilent_356_);
v_severity_boxed_370_ = lean_unbox(v_severity_364_);
v___x_351__boxed_371_ = lean_unbox(v___x_365_);
v_res_372_ = l_Lean_logAt___redArg___lam__4(v_ref_354_, v___y_349__boxed_368_, v_isSilent_boxed_369_, v_logMessage_357_, v_toBind_358_, v_getFileName_359_, v_msgData_360_, v_inst_361_, v_toMonadFileMap_362_, v_getRef_363_, v_severity_boxed_370_, v___x_351__boxed_371_, v___x_366_, v_____do__lift_367_);
lean_dec_ref(v_____do__lift_367_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg(lean_object* v_inst_373_, lean_object* v_inst_374_, lean_object* v_inst_375_, lean_object* v_inst_376_, lean_object* v_ref_377_, lean_object* v_msgData_378_, uint8_t v_severity_379_, uint8_t v_isSilent_380_){
_start:
{
lean_object* v___x_381_; lean_object* v_toApplicative_382_; lean_object* v_toBind_383_; lean_object* v_toMonadFileMap_384_; lean_object* v_getRef_385_; lean_object* v_getFileName_386_; lean_object* v_logMessage_387_; lean_object* v_toPure_388_; uint8_t v___x_389_; uint8_t v___y_391_; uint8_t v___x_400_; 
v___x_381_ = l_Lean_KVMap_instValueBool;
v_toApplicative_382_ = lean_ctor_get(v_inst_373_, 0);
lean_inc_ref(v_toApplicative_382_);
v_toBind_383_ = lean_ctor_get(v_inst_373_, 1);
lean_inc(v_toBind_383_);
lean_dec_ref(v_inst_373_);
v_toMonadFileMap_384_ = lean_ctor_get(v_inst_374_, 0);
lean_inc(v_toMonadFileMap_384_);
v_getRef_385_ = lean_ctor_get(v_inst_374_, 1);
lean_inc(v_getRef_385_);
v_getFileName_386_ = lean_ctor_get(v_inst_374_, 2);
lean_inc(v_getFileName_386_);
v_logMessage_387_ = lean_ctor_get(v_inst_374_, 4);
lean_inc(v_logMessage_387_);
lean_dec_ref(v_inst_374_);
v_toPure_388_ = lean_ctor_get(v_toApplicative_382_, 1);
lean_inc(v_toPure_388_);
lean_dec_ref(v_toApplicative_382_);
v___x_389_ = 2;
v___x_400_ = l_Lean_instBEqMessageSeverity_beq(v_severity_379_, v___x_389_);
if (v___x_400_ == 0)
{
v___y_391_ = v___x_400_;
goto v___jp_390_;
}
else
{
uint8_t v___x_401_; 
lean_inc_ref(v_msgData_378_);
v___x_401_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_378_);
v___y_391_ = v___x_401_;
goto v___jp_390_;
}
v___jp_390_:
{
if (v___y_391_ == 0)
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___f_396_; lean_object* v___x_397_; 
lean_dec(v_toPure_388_);
v___x_392_ = lean_box(v___y_391_);
v___x_393_ = lean_box(v_isSilent_380_);
v___x_394_ = lean_box(v_severity_379_);
v___x_395_ = lean_box(v___x_389_);
lean_inc(v_toBind_383_);
v___f_396_ = lean_alloc_closure((void*)(l_Lean_logAt___redArg___lam__4___boxed), 14, 13);
lean_closure_set(v___f_396_, 0, v_ref_377_);
lean_closure_set(v___f_396_, 1, v___x_392_);
lean_closure_set(v___f_396_, 2, v___x_393_);
lean_closure_set(v___f_396_, 3, v_logMessage_387_);
lean_closure_set(v___f_396_, 4, v_toBind_383_);
lean_closure_set(v___f_396_, 5, v_getFileName_386_);
lean_closure_set(v___f_396_, 6, v_msgData_378_);
lean_closure_set(v___f_396_, 7, v_inst_375_);
lean_closure_set(v___f_396_, 8, v_toMonadFileMap_384_);
lean_closure_set(v___f_396_, 9, v_getRef_385_);
lean_closure_set(v___f_396_, 10, v___x_394_);
lean_closure_set(v___f_396_, 11, v___x_395_);
lean_closure_set(v___f_396_, 12, v___x_381_);
v___x_397_ = lean_apply_4(v_toBind_383_, lean_box(0), lean_box(0), v_inst_376_, v___f_396_);
return v___x_397_;
}
else
{
lean_object* v___x_398_; lean_object* v___x_399_; 
lean_dec(v_logMessage_387_);
lean_dec(v_getFileName_386_);
lean_dec(v_getRef_385_);
lean_dec(v_toMonadFileMap_384_);
lean_dec(v_toBind_383_);
lean_dec_ref(v_msgData_378_);
lean_dec(v_ref_377_);
lean_dec(v_inst_376_);
lean_dec(v_inst_375_);
v___x_398_ = lean_box(0);
v___x_399_ = lean_apply_2(v_toPure_388_, lean_box(0), v___x_398_);
return v___x_399_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___boxed(lean_object* v_inst_402_, lean_object* v_inst_403_, lean_object* v_inst_404_, lean_object* v_inst_405_, lean_object* v_ref_406_, lean_object* v_msgData_407_, lean_object* v_severity_408_, lean_object* v_isSilent_409_){
_start:
{
uint8_t v_severity_boxed_410_; uint8_t v_isSilent_boxed_411_; lean_object* v_res_412_; 
v_severity_boxed_410_ = lean_unbox(v_severity_408_);
v_isSilent_boxed_411_ = lean_unbox(v_isSilent_409_);
v_res_412_ = l_Lean_logAt___redArg(v_inst_402_, v_inst_403_, v_inst_404_, v_inst_405_, v_ref_406_, v_msgData_407_, v_severity_boxed_410_, v_isSilent_boxed_411_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt(lean_object* v_m_413_, lean_object* v_inst_414_, lean_object* v_inst_415_, lean_object* v_inst_416_, lean_object* v_inst_417_, lean_object* v_ref_418_, lean_object* v_msgData_419_, uint8_t v_severity_420_, uint8_t v_isSilent_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_Lean_logAt___redArg(v_inst_414_, v_inst_415_, v_inst_416_, v_inst_417_, v_ref_418_, v_msgData_419_, v_severity_420_, v_isSilent_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___boxed(lean_object* v_m_423_, lean_object* v_inst_424_, lean_object* v_inst_425_, lean_object* v_inst_426_, lean_object* v_inst_427_, lean_object* v_ref_428_, lean_object* v_msgData_429_, lean_object* v_severity_430_, lean_object* v_isSilent_431_){
_start:
{
uint8_t v_severity_boxed_432_; uint8_t v_isSilent_boxed_433_; lean_object* v_res_434_; 
v_severity_boxed_432_ = lean_unbox(v_severity_430_);
v_isSilent_boxed_433_ = lean_unbox(v_isSilent_431_);
v_res_434_ = l_Lean_logAt(v_m_423_, v_inst_424_, v_inst_425_, v_inst_426_, v_inst_427_, v_ref_428_, v_msgData_429_, v_severity_boxed_432_, v_isSilent_boxed_433_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___redArg(lean_object* v_inst_435_, lean_object* v_inst_436_, lean_object* v_inst_437_, lean_object* v_inst_438_, lean_object* v_ref_439_, lean_object* v_msgData_440_){
_start:
{
uint8_t v___x_441_; uint8_t v___x_442_; lean_object* v___x_443_; 
v___x_441_ = 2;
v___x_442_ = 0;
v___x_443_ = l_Lean_logAt___redArg(v_inst_435_, v_inst_436_, v_inst_437_, v_inst_438_, v_ref_439_, v_msgData_440_, v___x_441_, v___x_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt(lean_object* v_m_444_, lean_object* v_inst_445_, lean_object* v_inst_446_, lean_object* v_inst_447_, lean_object* v_inst_448_, lean_object* v_ref_449_, lean_object* v_msgData_450_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l_Lean_logErrorAt___redArg(v_inst_445_, v_inst_446_, v_inst_447_, v_inst_448_, v_ref_449_, v_msgData_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedErrorAt___redArg(lean_object* v_inst_452_, lean_object* v_inst_453_, lean_object* v_inst_454_, lean_object* v_inst_455_, lean_object* v_ref_456_, lean_object* v_name_457_, lean_object* v_msgData_458_){
_start:
{
lean_object* v___x_459_; uint8_t v___x_460_; uint8_t v___x_461_; lean_object* v___x_462_; 
v___x_459_ = l_Lean_MessageData_tagWithErrorName(v_msgData_458_, v_name_457_);
v___x_460_ = 2;
v___x_461_ = 0;
v___x_462_ = l_Lean_logAt___redArg(v_inst_452_, v_inst_453_, v_inst_454_, v_inst_455_, v_ref_456_, v___x_459_, v___x_460_, v___x_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedErrorAt(lean_object* v_m_463_, lean_object* v_inst_464_, lean_object* v_inst_465_, lean_object* v_inst_466_, lean_object* v_inst_467_, lean_object* v_ref_468_, lean_object* v_name_469_, lean_object* v_msgData_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Lean_logNamedErrorAt___redArg(v_inst_464_, v_inst_465_, v_inst_466_, v_inst_467_, v_ref_468_, v_name_469_, v_msgData_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___redArg(lean_object* v_inst_472_, lean_object* v_inst_473_, lean_object* v_inst_474_, lean_object* v_inst_475_, lean_object* v_ref_476_, lean_object* v_msgData_477_){
_start:
{
uint8_t v___x_478_; uint8_t v___x_479_; lean_object* v___x_480_; 
v___x_478_ = 1;
v___x_479_ = 0;
v___x_480_ = l_Lean_logAt___redArg(v_inst_472_, v_inst_473_, v_inst_474_, v_inst_475_, v_ref_476_, v_msgData_477_, v___x_478_, v___x_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt(lean_object* v_m_481_, lean_object* v_inst_482_, lean_object* v_inst_483_, lean_object* v_inst_484_, lean_object* v_inst_485_, lean_object* v_ref_486_, lean_object* v_msgData_487_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l_Lean_logWarningAt___redArg(v_inst_482_, v_inst_483_, v_inst_484_, v_inst_485_, v_ref_486_, v_msgData_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedWarningAt___redArg(lean_object* v_inst_489_, lean_object* v_inst_490_, lean_object* v_inst_491_, lean_object* v_inst_492_, lean_object* v_ref_493_, lean_object* v_name_494_, lean_object* v_msgData_495_){
_start:
{
lean_object* v___x_496_; uint8_t v___x_497_; uint8_t v___x_498_; lean_object* v___x_499_; 
v___x_496_ = l_Lean_MessageData_tagWithErrorName(v_msgData_495_, v_name_494_);
v___x_497_ = 1;
v___x_498_ = 0;
v___x_499_ = l_Lean_logAt___redArg(v_inst_489_, v_inst_490_, v_inst_491_, v_inst_492_, v_ref_493_, v___x_496_, v___x_497_, v___x_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedWarningAt(lean_object* v_m_500_, lean_object* v_inst_501_, lean_object* v_inst_502_, lean_object* v_inst_503_, lean_object* v_inst_504_, lean_object* v_ref_505_, lean_object* v_name_506_, lean_object* v_msgData_507_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l_Lean_logNamedWarningAt___redArg(v_inst_501_, v_inst_502_, v_inst_503_, v_inst_504_, v_ref_505_, v_name_506_, v_msgData_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___redArg(lean_object* v_inst_509_, lean_object* v_inst_510_, lean_object* v_inst_511_, lean_object* v_inst_512_, lean_object* v_ref_513_, lean_object* v_msgData_514_){
_start:
{
uint8_t v___x_515_; uint8_t v___x_516_; lean_object* v___x_517_; 
v___x_515_ = 0;
v___x_516_ = 0;
v___x_517_ = l_Lean_logAt___redArg(v_inst_509_, v_inst_510_, v_inst_511_, v_inst_512_, v_ref_513_, v_msgData_514_, v___x_515_, v___x_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt(lean_object* v_m_518_, lean_object* v_inst_519_, lean_object* v_inst_520_, lean_object* v_inst_521_, lean_object* v_inst_522_, lean_object* v_ref_523_, lean_object* v_msgData_524_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Lean_logInfoAt___redArg(v_inst_519_, v_inst_520_, v_inst_521_, v_inst_522_, v_ref_523_, v_msgData_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___redArg___lam__0(lean_object* v_inst_526_, lean_object* v_inst_527_, lean_object* v_inst_528_, lean_object* v_inst_529_, lean_object* v_msgData_530_, uint8_t v_severity_531_, uint8_t v_isSilent_532_, lean_object* v_ref_533_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = l_Lean_logAt___redArg(v_inst_526_, v_inst_527_, v_inst_528_, v_inst_529_, v_ref_533_, v_msgData_530_, v_severity_531_, v_isSilent_532_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___redArg___lam__0___boxed(lean_object* v_inst_535_, lean_object* v_inst_536_, lean_object* v_inst_537_, lean_object* v_inst_538_, lean_object* v_msgData_539_, lean_object* v_severity_540_, lean_object* v_isSilent_541_, lean_object* v_ref_542_){
_start:
{
uint8_t v_severity_boxed_543_; uint8_t v_isSilent_boxed_544_; lean_object* v_res_545_; 
v_severity_boxed_543_ = lean_unbox(v_severity_540_);
v_isSilent_boxed_544_ = lean_unbox(v_isSilent_541_);
v_res_545_ = l_Lean_log___redArg___lam__0(v_inst_535_, v_inst_536_, v_inst_537_, v_inst_538_, v_msgData_539_, v_severity_boxed_543_, v_isSilent_boxed_544_, v_ref_542_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___redArg(lean_object* v_inst_546_, lean_object* v_inst_547_, lean_object* v_inst_548_, lean_object* v_inst_549_, lean_object* v_msgData_550_, uint8_t v_severity_551_, uint8_t v_isSilent_552_){
_start:
{
lean_object* v_toBind_553_; lean_object* v_getRef_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___f_557_; lean_object* v___x_558_; 
v_toBind_553_ = lean_ctor_get(v_inst_546_, 1);
lean_inc(v_toBind_553_);
v_getRef_554_ = lean_ctor_get(v_inst_547_, 1);
lean_inc(v_getRef_554_);
v___x_555_ = lean_box(v_severity_551_);
v___x_556_ = lean_box(v_isSilent_552_);
v___f_557_ = lean_alloc_closure((void*)(l_Lean_log___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_557_, 0, v_inst_546_);
lean_closure_set(v___f_557_, 1, v_inst_547_);
lean_closure_set(v___f_557_, 2, v_inst_548_);
lean_closure_set(v___f_557_, 3, v_inst_549_);
lean_closure_set(v___f_557_, 4, v_msgData_550_);
lean_closure_set(v___f_557_, 5, v___x_555_);
lean_closure_set(v___f_557_, 6, v___x_556_);
v___x_558_ = lean_apply_4(v_toBind_553_, lean_box(0), lean_box(0), v_getRef_554_, v___f_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___redArg___boxed(lean_object* v_inst_559_, lean_object* v_inst_560_, lean_object* v_inst_561_, lean_object* v_inst_562_, lean_object* v_msgData_563_, lean_object* v_severity_564_, lean_object* v_isSilent_565_){
_start:
{
uint8_t v_severity_boxed_566_; uint8_t v_isSilent_boxed_567_; lean_object* v_res_568_; 
v_severity_boxed_566_ = lean_unbox(v_severity_564_);
v_isSilent_boxed_567_ = lean_unbox(v_isSilent_565_);
v_res_568_ = l_Lean_log___redArg(v_inst_559_, v_inst_560_, v_inst_561_, v_inst_562_, v_msgData_563_, v_severity_boxed_566_, v_isSilent_boxed_567_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_log(lean_object* v_m_569_, lean_object* v_inst_570_, lean_object* v_inst_571_, lean_object* v_inst_572_, lean_object* v_inst_573_, lean_object* v_msgData_574_, uint8_t v_severity_575_, uint8_t v_isSilent_576_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l_Lean_log___redArg(v_inst_570_, v_inst_571_, v_inst_572_, v_inst_573_, v_msgData_574_, v_severity_575_, v_isSilent_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___boxed(lean_object* v_m_578_, lean_object* v_inst_579_, lean_object* v_inst_580_, lean_object* v_inst_581_, lean_object* v_inst_582_, lean_object* v_msgData_583_, lean_object* v_severity_584_, lean_object* v_isSilent_585_){
_start:
{
uint8_t v_severity_boxed_586_; uint8_t v_isSilent_boxed_587_; lean_object* v_res_588_; 
v_severity_boxed_586_ = lean_unbox(v_severity_584_);
v_isSilent_boxed_587_ = lean_unbox(v_isSilent_585_);
v_res_588_ = l_Lean_log(v_m_578_, v_inst_579_, v_inst_580_, v_inst_581_, v_inst_582_, v_msgData_583_, v_severity_boxed_586_, v_isSilent_boxed_587_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___redArg(lean_object* v_inst_589_, lean_object* v_inst_590_, lean_object* v_inst_591_, lean_object* v_inst_592_, lean_object* v_msgData_593_){
_start:
{
uint8_t v___x_594_; uint8_t v___x_595_; lean_object* v___x_596_; 
v___x_594_ = 2;
v___x_595_ = 0;
v___x_596_ = l_Lean_log___redArg(v_inst_589_, v_inst_590_, v_inst_591_, v_inst_592_, v_msgData_593_, v___x_594_, v___x_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError(lean_object* v_m_597_, lean_object* v_inst_598_, lean_object* v_inst_599_, lean_object* v_inst_600_, lean_object* v_inst_601_, lean_object* v_msgData_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Lean_logError___redArg(v_inst_598_, v_inst_599_, v_inst_600_, v_inst_601_, v_msgData_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedError___redArg(lean_object* v_inst_604_, lean_object* v_inst_605_, lean_object* v_inst_606_, lean_object* v_inst_607_, lean_object* v_name_608_, lean_object* v_msgData_609_){
_start:
{
lean_object* v___x_610_; uint8_t v___x_611_; uint8_t v___x_612_; lean_object* v___x_613_; 
v___x_610_ = l_Lean_MessageData_tagWithErrorName(v_msgData_609_, v_name_608_);
v___x_611_ = 2;
v___x_612_ = 0;
v___x_613_ = l_Lean_log___redArg(v_inst_604_, v_inst_605_, v_inst_606_, v_inst_607_, v___x_610_, v___x_611_, v___x_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedError(lean_object* v_m_614_, lean_object* v_inst_615_, lean_object* v_inst_616_, lean_object* v_inst_617_, lean_object* v_inst_618_, lean_object* v_name_619_, lean_object* v_msgData_620_){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = l_Lean_logNamedError___redArg(v_inst_615_, v_inst_616_, v_inst_617_, v_inst_618_, v_name_619_, v_msgData_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___redArg(lean_object* v_inst_622_, lean_object* v_inst_623_, lean_object* v_inst_624_, lean_object* v_inst_625_, lean_object* v_msgData_626_){
_start:
{
uint8_t v___x_627_; uint8_t v___x_628_; lean_object* v___x_629_; 
v___x_627_ = 1;
v___x_628_ = 0;
v___x_629_ = l_Lean_log___redArg(v_inst_622_, v_inst_623_, v_inst_624_, v_inst_625_, v_msgData_626_, v___x_627_, v___x_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning(lean_object* v_m_630_, lean_object* v_inst_631_, lean_object* v_inst_632_, lean_object* v_inst_633_, lean_object* v_inst_634_, lean_object* v_msgData_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_Lean_logWarning___redArg(v_inst_631_, v_inst_632_, v_inst_633_, v_inst_634_, v_msgData_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedWarning___redArg(lean_object* v_inst_637_, lean_object* v_inst_638_, lean_object* v_inst_639_, lean_object* v_inst_640_, lean_object* v_name_641_, lean_object* v_msgData_642_){
_start:
{
lean_object* v___x_643_; uint8_t v___x_644_; uint8_t v___x_645_; lean_object* v___x_646_; 
v___x_643_ = l_Lean_MessageData_tagWithErrorName(v_msgData_642_, v_name_641_);
v___x_644_ = 1;
v___x_645_ = 0;
v___x_646_ = l_Lean_log___redArg(v_inst_637_, v_inst_638_, v_inst_639_, v_inst_640_, v___x_643_, v___x_644_, v___x_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedWarning(lean_object* v_m_647_, lean_object* v_inst_648_, lean_object* v_inst_649_, lean_object* v_inst_650_, lean_object* v_inst_651_, lean_object* v_name_652_, lean_object* v_msgData_653_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l_Lean_logNamedWarning___redArg(v_inst_648_, v_inst_649_, v_inst_650_, v_inst_651_, v_name_652_, v_msgData_653_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___redArg(lean_object* v_inst_655_, lean_object* v_inst_656_, lean_object* v_inst_657_, lean_object* v_inst_658_, lean_object* v_msgData_659_){
_start:
{
uint8_t v___x_660_; uint8_t v___x_661_; lean_object* v___x_662_; 
v___x_660_ = 0;
v___x_661_ = 0;
v___x_662_ = l_Lean_log___redArg(v_inst_655_, v_inst_656_, v_inst_657_, v_inst_658_, v_msgData_659_, v___x_660_, v___x_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo(lean_object* v_m_663_, lean_object* v_inst_664_, lean_object* v_inst_665_, lean_object* v_inst_666_, lean_object* v_inst_667_, lean_object* v_msgData_668_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = l_Lean_logInfo___redArg(v_inst_664_, v_inst_665_, v_inst_666_, v_inst_667_, v_msgData_668_);
return v___x_669_;
}
}
static lean_object* _init_l_Lean_logUnknownDecl___redArg___closed__1(void){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = ((lean_object*)(l_Lean_logUnknownDecl___redArg___closed__0));
v___x_672_ = l_Lean_stringToMessageData(v___x_671_);
return v___x_672_;
}
}
static lean_object* _init_l_Lean_logUnknownDecl___redArg___closed__3(void){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = ((lean_object*)(l_Lean_logUnknownDecl___redArg___closed__2));
v___x_675_ = l_Lean_stringToMessageData(v___x_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_logUnknownDecl___redArg(lean_object* v_inst_676_, lean_object* v_inst_677_, lean_object* v_inst_678_, lean_object* v_inst_679_, lean_object* v_declName_680_){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_681_ = lean_obj_once(&l_Lean_logUnknownDecl___redArg___closed__1, &l_Lean_logUnknownDecl___redArg___closed__1_once, _init_l_Lean_logUnknownDecl___redArg___closed__1);
v___x_682_ = l_Lean_MessageData_ofName(v_declName_680_);
v___x_683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_683_, 0, v___x_681_);
lean_ctor_set(v___x_683_, 1, v___x_682_);
v___x_684_ = lean_obj_once(&l_Lean_logUnknownDecl___redArg___closed__3, &l_Lean_logUnknownDecl___redArg___closed__3_once, _init_l_Lean_logUnknownDecl___redArg___closed__3);
v___x_685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_685_, 0, v___x_683_);
lean_ctor_set(v___x_685_, 1, v___x_684_);
v___x_686_ = l_Lean_logError___redArg(v_inst_676_, v_inst_677_, v_inst_678_, v_inst_679_, v___x_685_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_logUnknownDecl(lean_object* v_m_687_, lean_object* v_inst_688_, lean_object* v_inst_689_, lean_object* v_inst_690_, lean_object* v_inst_691_, lean_object* v_declName_692_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = l_Lean_logUnknownDecl___redArg(v_inst_688_, v_inst_689_, v_inst_690_, v_inst_691_, v_declName_692_);
return v___x_693_;
}
}
lean_object* runtime_initialize_Lean_ErrorExplanation(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Log(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_ErrorExplanation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Log_0__Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_warningAsError = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_warningAsError);
lean_dec_ref(res);
l_Lean_errorDescriptionWidget = _init_l_Lean_errorDescriptionWidget();
lean_mark_persistent(l_Lean_errorDescriptionWidget);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Log(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_ErrorExplanation(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Log(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_ErrorExplanation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Log(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Log(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Log(builtin);
}
#ifdef __cplusplus
}
#endif
