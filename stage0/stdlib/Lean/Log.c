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
static const lean_ctor_object l_Lean_errorDescriptionWidget___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_errorDescriptionWidget___closed__0_value),LEAN_SCALAR_PTR_LITERAL(51, 195, 126, 77, 82, 115, 229, 194)}};
static const lean_object* l_Lean_errorDescriptionWidget___closed__1 = (const lean_object*)&l_Lean_errorDescriptionWidget___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_errorDescriptionWidget = (const lean_object*)&l_Lean_errorDescriptionWidget___closed__1_value;
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
LEAN_EXPORT lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___lam__0(lean_object* v___x_140_, lean_object* v___y_141_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_140_);
lean_ctor_set(v___x_142_, 1, v___y_141_);
return v___x_142_;
}
}
static lean_object* _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__1(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_144_ = l_Lean_errorExplanationManualDomain;
v___x_145_ = ((lean_object*)(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__0));
v___x_146_ = lean_string_append(v___x_145_, v___x_144_);
return v___x_146_;
}
}
static lean_object* _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__3(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_148_ = ((lean_object*)(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__2));
v___x_149_ = lean_obj_once(&l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__1, &l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__1_once, _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__1);
v___x_150_ = lean_string_append(v___x_149_, v___x_148_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object* v_msg_157_){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; 
lean_inc_ref(v_msg_157_);
v___x_158_ = l_Lean_MessageData_stripNestedTags(v_msg_157_);
v___x_159_ = l_Lean_MessageData_errorName_x3f(v___x_158_);
lean_dec_ref(v___x_158_);
if (lean_obj_tag(v___x_159_) == 0)
{
return v_msg_157_;
}
else
{
lean_object* v_val_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_190_; 
v_val_160_ = lean_ctor_get(v___x_159_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_190_ == 0)
{
v___x_162_ = v___x_159_;
v_isShared_163_ = v_isSharedCheck_190_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_val_160_);
lean_dec(v___x_159_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_190_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_164_; uint64_t v_javascriptHash_165_; lean_object* v___x_166_; lean_object* v___x_167_; uint8_t v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v_url_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_175_; 
v___x_164_ = ((lean_object*)(l_Lean_errorDescriptionWidget));
v_javascriptHash_165_ = lean_ctor_get_uint64(v___x_164_, sizeof(void*)*1);
v___x_166_ = l_Lean_manualRoot;
v___x_167_ = lean_obj_once(&l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__3, &l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__3_once, _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__3);
v___x_168_ = 1;
v___x_169_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_160_, v___x_168_);
v___x_170_ = lean_string_append(v___x_167_, v___x_169_);
v_url_171_ = lean_string_append(v___x_166_, v___x_170_);
lean_dec_ref(v___x_170_);
v___x_172_ = ((lean_object*)(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__5));
v___x_173_ = ((lean_object*)(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__6));
if (v_isShared_163_ == 0)
{
lean_ctor_set_tag(v___x_162_, 3);
lean_ctor_set(v___x_162_, 0, v___x_169_);
v___x_175_ = v___x_162_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v___x_169_);
v___x_175_ = v_reuseFailAlloc_189_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___f_184_; lean_object* v_inst_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_173_);
lean_ctor_set(v___x_176_, 1, v___x_175_);
v___x_177_ = ((lean_object*)(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__7));
v___x_178_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_178_, 0, v_url_171_);
v___x_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_177_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
v___x_180_ = lean_box(0);
v___x_181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_179_);
lean_ctor_set(v___x_181_, 1, v___x_180_);
v___x_182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_176_);
lean_ctor_set(v___x_182_, 1, v___x_181_);
v___x_183_ = l_Lean_Json_mkObj(v___x_182_);
lean_dec_ref_known(v___x_182_, 2);
v___f_184_ = lean_alloc_closure((void*)(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___lam__0), 2, 1);
lean_closure_set(v___f_184_, 0, v___x_183_);
v_inst_185_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v_inst_185_, 0, v___x_172_);
lean_ctor_set(v_inst_185_, 1, v___f_184_);
lean_ctor_set_uint64(v_inst_185_, sizeof(void*)*2, v_javascriptHash_165_);
v___x_186_ = l_Lean_MessageData_nil;
v___x_187_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_187_, 0, v_inst_185_);
lean_ctor_set(v___x_187_, 1, v___x_186_);
v___x_188_ = l_Lean_MessageData_composePreservingKind(v_msg_157_, v___x_187_);
return v___x_188_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__0(lean_object* v_fileMap_192_, lean_object* v___y_193_, lean_object* v___y_194_, uint8_t v___y_195_, uint8_t v___y_196_, uint8_t v_isSilent_197_, lean_object* v_msgData_198_, lean_object* v_logMessage_199_, lean_object* v_____do__lift_200_){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
lean_inc_ref(v_fileMap_192_);
v___x_201_ = l_Lean_FileMap_toPosition(v_fileMap_192_, v___y_193_);
v___x_202_ = l_Lean_FileMap_toPosition(v_fileMap_192_, v___y_194_);
v___x_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
v___x_204_ = ((lean_object*)(l_Lean_logAt___redArg___lam__0___closed__0));
v___x_205_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_205_, 0, v_____do__lift_200_);
lean_ctor_set(v___x_205_, 1, v___x_201_);
lean_ctor_set(v___x_205_, 2, v___x_203_);
lean_ctor_set(v___x_205_, 3, v___x_204_);
lean_ctor_set(v___x_205_, 4, v_msgData_198_);
lean_ctor_set_uint8(v___x_205_, sizeof(void*)*5, v___y_195_);
lean_ctor_set_uint8(v___x_205_, sizeof(void*)*5 + 1, v___y_196_);
lean_ctor_set_uint8(v___x_205_, sizeof(void*)*5 + 2, v_isSilent_197_);
v___x_206_ = lean_apply_1(v_logMessage_199_, v___x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__0___boxed(lean_object* v_fileMap_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v_isSilent_212_, lean_object* v_msgData_213_, lean_object* v_logMessage_214_, lean_object* v_____do__lift_215_){
_start:
{
uint8_t v___y_230__boxed_216_; uint8_t v___y_231__boxed_217_; uint8_t v_isSilent_boxed_218_; lean_object* v_res_219_; 
v___y_230__boxed_216_ = lean_unbox(v___y_210_);
v___y_231__boxed_217_ = lean_unbox(v___y_211_);
v_isSilent_boxed_218_ = lean_unbox(v_isSilent_212_);
v_res_219_ = l_Lean_logAt___redArg___lam__0(v_fileMap_207_, v___y_208_, v___y_209_, v___y_230__boxed_216_, v___y_231__boxed_217_, v_isSilent_boxed_218_, v_msgData_213_, v_logMessage_214_, v_____do__lift_215_);
lean_dec(v___y_209_);
lean_dec(v___y_208_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__1(lean_object* v_fileMap_220_, lean_object* v___y_221_, lean_object* v___y_222_, uint8_t v___y_223_, uint8_t v___y_224_, uint8_t v_isSilent_225_, lean_object* v_logMessage_226_, lean_object* v_toBind_227_, lean_object* v_getFileName_228_, lean_object* v_msgData_229_){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___f_233_; lean_object* v___x_234_; 
v___x_230_ = lean_box(v___y_223_);
v___x_231_ = lean_box(v___y_224_);
v___x_232_ = lean_box(v_isSilent_225_);
v___f_233_ = lean_alloc_closure((void*)(l_Lean_logAt___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_233_, 0, v_fileMap_220_);
lean_closure_set(v___f_233_, 1, v___y_221_);
lean_closure_set(v___f_233_, 2, v___y_222_);
lean_closure_set(v___f_233_, 3, v___x_230_);
lean_closure_set(v___f_233_, 4, v___x_231_);
lean_closure_set(v___f_233_, 5, v___x_232_);
lean_closure_set(v___f_233_, 6, v_msgData_229_);
lean_closure_set(v___f_233_, 7, v_logMessage_226_);
v___x_234_ = lean_apply_4(v_toBind_227_, lean_box(0), lean_box(0), v_getFileName_228_, v___f_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__1___boxed(lean_object* v_fileMap_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v_isSilent_240_, lean_object* v_logMessage_241_, lean_object* v_toBind_242_, lean_object* v_getFileName_243_, lean_object* v_msgData_244_){
_start:
{
uint8_t v___y_258__boxed_245_; uint8_t v___y_259__boxed_246_; uint8_t v_isSilent_boxed_247_; lean_object* v_res_248_; 
v___y_258__boxed_245_ = lean_unbox(v___y_238_);
v___y_259__boxed_246_ = lean_unbox(v___y_239_);
v_isSilent_boxed_247_ = lean_unbox(v_isSilent_240_);
v_res_248_ = l_Lean_logAt___redArg___lam__1(v_fileMap_235_, v___y_236_, v___y_237_, v___y_258__boxed_245_, v___y_259__boxed_246_, v_isSilent_boxed_247_, v_logMessage_241_, v_toBind_242_, v_getFileName_243_, v_msgData_244_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__2(lean_object* v___y_249_, lean_object* v___y_250_, uint8_t v___y_251_, uint8_t v___y_252_, uint8_t v_isSilent_253_, lean_object* v_logMessage_254_, lean_object* v_toBind_255_, lean_object* v_getFileName_256_, lean_object* v_msgData_257_, lean_object* v_inst_258_, lean_object* v_fileMap_259_){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___f_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_260_ = lean_box(v___y_251_);
v___x_261_ = lean_box(v___y_252_);
v___x_262_ = lean_box(v_isSilent_253_);
lean_inc(v_toBind_255_);
v___f_263_ = lean_alloc_closure((void*)(l_Lean_logAt___redArg___lam__1___boxed), 10, 9);
lean_closure_set(v___f_263_, 0, v_fileMap_259_);
lean_closure_set(v___f_263_, 1, v___y_249_);
lean_closure_set(v___f_263_, 2, v___y_250_);
lean_closure_set(v___f_263_, 3, v___x_260_);
lean_closure_set(v___f_263_, 4, v___x_261_);
lean_closure_set(v___f_263_, 5, v___x_262_);
lean_closure_set(v___f_263_, 6, v_logMessage_254_);
lean_closure_set(v___f_263_, 7, v_toBind_255_);
lean_closure_set(v___f_263_, 8, v_getFileName_256_);
v___x_264_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_257_);
v___x_265_ = lean_apply_1(v_inst_258_, v___x_264_);
v___x_266_ = lean_apply_4(v_toBind_255_, lean_box(0), lean_box(0), v___x_265_, v___f_263_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__2___boxed(lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v_isSilent_271_, lean_object* v_logMessage_272_, lean_object* v_toBind_273_, lean_object* v_getFileName_274_, lean_object* v_msgData_275_, lean_object* v_inst_276_, lean_object* v_fileMap_277_){
_start:
{
uint8_t v___y_280__boxed_278_; uint8_t v___y_281__boxed_279_; uint8_t v_isSilent_boxed_280_; lean_object* v_res_281_; 
v___y_280__boxed_278_ = lean_unbox(v___y_269_);
v___y_281__boxed_279_ = lean_unbox(v___y_270_);
v_isSilent_boxed_280_ = lean_unbox(v_isSilent_271_);
v_res_281_ = l_Lean_logAt___redArg___lam__2(v___y_267_, v___y_268_, v___y_280__boxed_278_, v___y_281__boxed_279_, v_isSilent_boxed_280_, v_logMessage_272_, v_toBind_273_, v_getFileName_274_, v_msgData_275_, v_inst_276_, v_fileMap_277_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__3(lean_object* v_ref_282_, uint8_t v___y_283_, uint8_t v___y_284_, uint8_t v_isSilent_285_, lean_object* v_logMessage_286_, lean_object* v_toBind_287_, lean_object* v_getFileName_288_, lean_object* v_msgData_289_, lean_object* v_inst_290_, lean_object* v_toMonadFileMap_291_, lean_object* v_____do__lift_292_){
_start:
{
lean_object* v___y_294_; lean_object* v___y_295_; lean_object* v_ref_301_; lean_object* v___y_303_; lean_object* v___x_306_; 
v_ref_301_ = l_Lean_replaceRef(v_ref_282_, v_____do__lift_292_);
v___x_306_ = l_Lean_Syntax_getPos_x3f(v_ref_301_, v___y_283_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v___x_307_; 
v___x_307_ = lean_unsigned_to_nat(0u);
v___y_303_ = v___x_307_;
goto v___jp_302_;
}
else
{
lean_object* v_val_308_; 
v_val_308_ = lean_ctor_get(v___x_306_, 0);
lean_inc(v_val_308_);
lean_dec_ref_known(v___x_306_, 1);
v___y_303_ = v_val_308_;
goto v___jp_302_;
}
v___jp_293_:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___f_299_; lean_object* v___x_300_; 
v___x_296_ = lean_box(v___y_283_);
v___x_297_ = lean_box(v___y_284_);
v___x_298_ = lean_box(v_isSilent_285_);
lean_inc(v_toBind_287_);
v___f_299_ = lean_alloc_closure((void*)(l_Lean_logAt___redArg___lam__2___boxed), 11, 10);
lean_closure_set(v___f_299_, 0, v___y_294_);
lean_closure_set(v___f_299_, 1, v___y_295_);
lean_closure_set(v___f_299_, 2, v___x_296_);
lean_closure_set(v___f_299_, 3, v___x_297_);
lean_closure_set(v___f_299_, 4, v___x_298_);
lean_closure_set(v___f_299_, 5, v_logMessage_286_);
lean_closure_set(v___f_299_, 6, v_toBind_287_);
lean_closure_set(v___f_299_, 7, v_getFileName_288_);
lean_closure_set(v___f_299_, 8, v_msgData_289_);
lean_closure_set(v___f_299_, 9, v_inst_290_);
v___x_300_ = lean_apply_4(v_toBind_287_, lean_box(0), lean_box(0), v_toMonadFileMap_291_, v___f_299_);
return v___x_300_;
}
v___jp_302_:
{
lean_object* v___x_304_; 
v___x_304_ = l_Lean_Syntax_getTailPos_x3f(v_ref_301_, v___y_283_);
lean_dec(v_ref_301_);
if (lean_obj_tag(v___x_304_) == 0)
{
lean_inc(v___y_303_);
v___y_294_ = v___y_303_;
v___y_295_ = v___y_303_;
goto v___jp_293_;
}
else
{
lean_object* v_val_305_; 
v_val_305_ = lean_ctor_get(v___x_304_, 0);
lean_inc(v_val_305_);
lean_dec_ref_known(v___x_304_, 1);
v___y_294_ = v___y_303_;
v___y_295_ = v_val_305_;
goto v___jp_293_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__3___boxed(lean_object* v_ref_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v_isSilent_312_, lean_object* v_logMessage_313_, lean_object* v_toBind_314_, lean_object* v_getFileName_315_, lean_object* v_msgData_316_, lean_object* v_inst_317_, lean_object* v_toMonadFileMap_318_, lean_object* v_____do__lift_319_){
_start:
{
uint8_t v___y_308__boxed_320_; uint8_t v___y_309__boxed_321_; uint8_t v_isSilent_boxed_322_; lean_object* v_res_323_; 
v___y_308__boxed_320_ = lean_unbox(v___y_310_);
v___y_309__boxed_321_ = lean_unbox(v___y_311_);
v_isSilent_boxed_322_ = lean_unbox(v_isSilent_312_);
v_res_323_ = l_Lean_logAt___redArg___lam__3(v_ref_309_, v___y_308__boxed_320_, v___y_309__boxed_321_, v_isSilent_boxed_322_, v_logMessage_313_, v_toBind_314_, v_getFileName_315_, v_msgData_316_, v_inst_317_, v_toMonadFileMap_318_, v_____do__lift_319_);
lean_dec(v_____do__lift_319_);
lean_dec(v_ref_309_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__4(lean_object* v_ref_324_, uint8_t v___y_325_, uint8_t v_isSilent_326_, lean_object* v_logMessage_327_, lean_object* v_toBind_328_, lean_object* v_getFileName_329_, lean_object* v_msgData_330_, lean_object* v_inst_331_, lean_object* v_toMonadFileMap_332_, lean_object* v_getRef_333_, uint8_t v_severity_334_, uint8_t v___x_335_, lean_object* v___x_336_, lean_object* v_____do__lift_337_){
_start:
{
uint8_t v___y_339_; uint8_t v___y_346_; uint8_t v___x_347_; uint8_t v___x_348_; 
v___x_347_ = 1;
v___x_348_ = l_Lean_instBEqMessageSeverity_beq(v_severity_334_, v___x_347_);
if (v___x_348_ == 0)
{
lean_dec_ref(v___x_336_);
v___y_346_ = v___x_348_;
goto v___jp_345_;
}
else
{
lean_object* v___x_349_; lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_349_ = l_Lean_warningAsError;
v___x_350_ = l_Lean_Option_get___redArg(v___x_336_, v_____do__lift_337_, v___x_349_);
v___x_351_ = lean_unbox(v___x_350_);
lean_dec(v___x_350_);
v___y_346_ = v___x_351_;
goto v___jp_345_;
}
v___jp_338_:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___f_343_; lean_object* v___x_344_; 
v___x_340_ = lean_box(v___y_325_);
v___x_341_ = lean_box(v___y_339_);
v___x_342_ = lean_box(v_isSilent_326_);
lean_inc(v_toBind_328_);
v___f_343_ = lean_alloc_closure((void*)(l_Lean_logAt___redArg___lam__3___boxed), 11, 10);
lean_closure_set(v___f_343_, 0, v_ref_324_);
lean_closure_set(v___f_343_, 1, v___x_340_);
lean_closure_set(v___f_343_, 2, v___x_341_);
lean_closure_set(v___f_343_, 3, v___x_342_);
lean_closure_set(v___f_343_, 4, v_logMessage_327_);
lean_closure_set(v___f_343_, 5, v_toBind_328_);
lean_closure_set(v___f_343_, 6, v_getFileName_329_);
lean_closure_set(v___f_343_, 7, v_msgData_330_);
lean_closure_set(v___f_343_, 8, v_inst_331_);
lean_closure_set(v___f_343_, 9, v_toMonadFileMap_332_);
v___x_344_ = lean_apply_4(v_toBind_328_, lean_box(0), lean_box(0), v_getRef_333_, v___f_343_);
return v___x_344_;
}
v___jp_345_:
{
if (v___y_346_ == 0)
{
v___y_339_ = v_severity_334_;
goto v___jp_338_;
}
else
{
v___y_339_ = v___x_335_;
goto v___jp_338_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__4___boxed(lean_object* v_ref_352_, lean_object* v___y_353_, lean_object* v_isSilent_354_, lean_object* v_logMessage_355_, lean_object* v_toBind_356_, lean_object* v_getFileName_357_, lean_object* v_msgData_358_, lean_object* v_inst_359_, lean_object* v_toMonadFileMap_360_, lean_object* v_getRef_361_, lean_object* v_severity_362_, lean_object* v___x_363_, lean_object* v___x_364_, lean_object* v_____do__lift_365_){
_start:
{
uint8_t v___y_350__boxed_366_; uint8_t v_isSilent_boxed_367_; uint8_t v_severity_boxed_368_; uint8_t v___x_352__boxed_369_; lean_object* v_res_370_; 
v___y_350__boxed_366_ = lean_unbox(v___y_353_);
v_isSilent_boxed_367_ = lean_unbox(v_isSilent_354_);
v_severity_boxed_368_ = lean_unbox(v_severity_362_);
v___x_352__boxed_369_ = lean_unbox(v___x_363_);
v_res_370_ = l_Lean_logAt___redArg___lam__4(v_ref_352_, v___y_350__boxed_366_, v_isSilent_boxed_367_, v_logMessage_355_, v_toBind_356_, v_getFileName_357_, v_msgData_358_, v_inst_359_, v_toMonadFileMap_360_, v_getRef_361_, v_severity_boxed_368_, v___x_352__boxed_369_, v___x_364_, v_____do__lift_365_);
lean_dec_ref(v_____do__lift_365_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg(lean_object* v_inst_371_, lean_object* v_inst_372_, lean_object* v_inst_373_, lean_object* v_inst_374_, lean_object* v_ref_375_, lean_object* v_msgData_376_, uint8_t v_severity_377_, uint8_t v_isSilent_378_){
_start:
{
lean_object* v___x_379_; lean_object* v_toApplicative_380_; lean_object* v_toBind_381_; lean_object* v_toMonadFileMap_382_; lean_object* v_getRef_383_; lean_object* v_getFileName_384_; lean_object* v_logMessage_385_; lean_object* v_toPure_386_; uint8_t v___x_387_; uint8_t v___y_389_; uint8_t v___x_399_; 
v___x_379_ = l_Lean_KVMap_instValueBool;
v_toApplicative_380_ = lean_ctor_get(v_inst_371_, 0);
lean_inc_ref(v_toApplicative_380_);
v_toBind_381_ = lean_ctor_get(v_inst_371_, 1);
lean_inc(v_toBind_381_);
lean_dec_ref(v_inst_371_);
v_toMonadFileMap_382_ = lean_ctor_get(v_inst_372_, 0);
lean_inc(v_toMonadFileMap_382_);
v_getRef_383_ = lean_ctor_get(v_inst_372_, 1);
lean_inc(v_getRef_383_);
v_getFileName_384_ = lean_ctor_get(v_inst_372_, 2);
lean_inc(v_getFileName_384_);
v_logMessage_385_ = lean_ctor_get(v_inst_372_, 4);
lean_inc(v_logMessage_385_);
lean_dec_ref(v_inst_372_);
v_toPure_386_ = lean_ctor_get(v_toApplicative_380_, 1);
lean_inc(v_toPure_386_);
lean_dec_ref(v_toApplicative_380_);
v___x_387_ = 2;
v___x_399_ = l_Lean_instBEqMessageSeverity_beq(v_severity_377_, v___x_387_);
if (v___x_399_ == 0)
{
v___y_389_ = v___x_399_;
goto v___jp_388_;
}
else
{
uint8_t v___x_400_; 
lean_inc_ref(v_msgData_376_);
v___x_400_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_376_);
v___y_389_ = v___x_400_;
goto v___jp_388_;
}
v___jp_388_:
{
if (v___y_389_ == 0)
{
lean_object* v_getOptions_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___f_395_; lean_object* v___x_396_; 
lean_dec(v_toPure_386_);
v_getOptions_390_ = lean_ctor_get(v_inst_374_, 0);
lean_inc(v_getOptions_390_);
lean_dec_ref(v_inst_374_);
v___x_391_ = lean_box(v___y_389_);
v___x_392_ = lean_box(v_isSilent_378_);
v___x_393_ = lean_box(v_severity_377_);
v___x_394_ = lean_box(v___x_387_);
lean_inc(v_toBind_381_);
v___f_395_ = lean_alloc_closure((void*)(l_Lean_logAt___redArg___lam__4___boxed), 14, 13);
lean_closure_set(v___f_395_, 0, v_ref_375_);
lean_closure_set(v___f_395_, 1, v___x_391_);
lean_closure_set(v___f_395_, 2, v___x_392_);
lean_closure_set(v___f_395_, 3, v_logMessage_385_);
lean_closure_set(v___f_395_, 4, v_toBind_381_);
lean_closure_set(v___f_395_, 5, v_getFileName_384_);
lean_closure_set(v___f_395_, 6, v_msgData_376_);
lean_closure_set(v___f_395_, 7, v_inst_373_);
lean_closure_set(v___f_395_, 8, v_toMonadFileMap_382_);
lean_closure_set(v___f_395_, 9, v_getRef_383_);
lean_closure_set(v___f_395_, 10, v___x_393_);
lean_closure_set(v___f_395_, 11, v___x_394_);
lean_closure_set(v___f_395_, 12, v___x_379_);
v___x_396_ = lean_apply_4(v_toBind_381_, lean_box(0), lean_box(0), v_getOptions_390_, v___f_395_);
return v___x_396_;
}
else
{
lean_object* v___x_397_; lean_object* v___x_398_; 
lean_dec(v_logMessage_385_);
lean_dec(v_getFileName_384_);
lean_dec(v_getRef_383_);
lean_dec(v_toMonadFileMap_382_);
lean_dec(v_toBind_381_);
lean_dec_ref(v_msgData_376_);
lean_dec(v_ref_375_);
lean_dec_ref(v_inst_374_);
lean_dec(v_inst_373_);
v___x_397_ = lean_box(0);
v___x_398_ = lean_apply_2(v_toPure_386_, lean_box(0), v___x_397_);
return v___x_398_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___boxed(lean_object* v_inst_401_, lean_object* v_inst_402_, lean_object* v_inst_403_, lean_object* v_inst_404_, lean_object* v_ref_405_, lean_object* v_msgData_406_, lean_object* v_severity_407_, lean_object* v_isSilent_408_){
_start:
{
uint8_t v_severity_boxed_409_; uint8_t v_isSilent_boxed_410_; lean_object* v_res_411_; 
v_severity_boxed_409_ = lean_unbox(v_severity_407_);
v_isSilent_boxed_410_ = lean_unbox(v_isSilent_408_);
v_res_411_ = l_Lean_logAt___redArg(v_inst_401_, v_inst_402_, v_inst_403_, v_inst_404_, v_ref_405_, v_msgData_406_, v_severity_boxed_409_, v_isSilent_boxed_410_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt(lean_object* v_m_412_, lean_object* v_inst_413_, lean_object* v_inst_414_, lean_object* v_inst_415_, lean_object* v_inst_416_, lean_object* v_ref_417_, lean_object* v_msgData_418_, uint8_t v_severity_419_, uint8_t v_isSilent_420_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_Lean_logAt___redArg(v_inst_413_, v_inst_414_, v_inst_415_, v_inst_416_, v_ref_417_, v_msgData_418_, v_severity_419_, v_isSilent_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___boxed(lean_object* v_m_422_, lean_object* v_inst_423_, lean_object* v_inst_424_, lean_object* v_inst_425_, lean_object* v_inst_426_, lean_object* v_ref_427_, lean_object* v_msgData_428_, lean_object* v_severity_429_, lean_object* v_isSilent_430_){
_start:
{
uint8_t v_severity_boxed_431_; uint8_t v_isSilent_boxed_432_; lean_object* v_res_433_; 
v_severity_boxed_431_ = lean_unbox(v_severity_429_);
v_isSilent_boxed_432_ = lean_unbox(v_isSilent_430_);
v_res_433_ = l_Lean_logAt(v_m_422_, v_inst_423_, v_inst_424_, v_inst_425_, v_inst_426_, v_ref_427_, v_msgData_428_, v_severity_boxed_431_, v_isSilent_boxed_432_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___redArg(lean_object* v_inst_434_, lean_object* v_inst_435_, lean_object* v_inst_436_, lean_object* v_inst_437_, lean_object* v_ref_438_, lean_object* v_msgData_439_){
_start:
{
uint8_t v___x_440_; uint8_t v___x_441_; lean_object* v___x_442_; 
v___x_440_ = 2;
v___x_441_ = 0;
v___x_442_ = l_Lean_logAt___redArg(v_inst_434_, v_inst_435_, v_inst_436_, v_inst_437_, v_ref_438_, v_msgData_439_, v___x_440_, v___x_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt(lean_object* v_m_443_, lean_object* v_inst_444_, lean_object* v_inst_445_, lean_object* v_inst_446_, lean_object* v_inst_447_, lean_object* v_ref_448_, lean_object* v_msgData_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Lean_logErrorAt___redArg(v_inst_444_, v_inst_445_, v_inst_446_, v_inst_447_, v_ref_448_, v_msgData_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedErrorAt___redArg(lean_object* v_inst_451_, lean_object* v_inst_452_, lean_object* v_inst_453_, lean_object* v_inst_454_, lean_object* v_ref_455_, lean_object* v_name_456_, lean_object* v_msgData_457_){
_start:
{
lean_object* v___x_458_; uint8_t v___x_459_; uint8_t v___x_460_; lean_object* v___x_461_; 
v___x_458_ = l_Lean_MessageData_tagWithErrorName(v_msgData_457_, v_name_456_);
v___x_459_ = 2;
v___x_460_ = 0;
v___x_461_ = l_Lean_logAt___redArg(v_inst_451_, v_inst_452_, v_inst_453_, v_inst_454_, v_ref_455_, v___x_458_, v___x_459_, v___x_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedErrorAt(lean_object* v_m_462_, lean_object* v_inst_463_, lean_object* v_inst_464_, lean_object* v_inst_465_, lean_object* v_inst_466_, lean_object* v_ref_467_, lean_object* v_name_468_, lean_object* v_msgData_469_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l_Lean_logNamedErrorAt___redArg(v_inst_463_, v_inst_464_, v_inst_465_, v_inst_466_, v_ref_467_, v_name_468_, v_msgData_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___redArg(lean_object* v_inst_471_, lean_object* v_inst_472_, lean_object* v_inst_473_, lean_object* v_inst_474_, lean_object* v_ref_475_, lean_object* v_msgData_476_){
_start:
{
uint8_t v___x_477_; uint8_t v___x_478_; lean_object* v___x_479_; 
v___x_477_ = 1;
v___x_478_ = 0;
v___x_479_ = l_Lean_logAt___redArg(v_inst_471_, v_inst_472_, v_inst_473_, v_inst_474_, v_ref_475_, v_msgData_476_, v___x_477_, v___x_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt(lean_object* v_m_480_, lean_object* v_inst_481_, lean_object* v_inst_482_, lean_object* v_inst_483_, lean_object* v_inst_484_, lean_object* v_ref_485_, lean_object* v_msgData_486_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l_Lean_logWarningAt___redArg(v_inst_481_, v_inst_482_, v_inst_483_, v_inst_484_, v_ref_485_, v_msgData_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedWarningAt___redArg(lean_object* v_inst_488_, lean_object* v_inst_489_, lean_object* v_inst_490_, lean_object* v_inst_491_, lean_object* v_ref_492_, lean_object* v_name_493_, lean_object* v_msgData_494_){
_start:
{
lean_object* v___x_495_; uint8_t v___x_496_; uint8_t v___x_497_; lean_object* v___x_498_; 
v___x_495_ = l_Lean_MessageData_tagWithErrorName(v_msgData_494_, v_name_493_);
v___x_496_ = 1;
v___x_497_ = 0;
v___x_498_ = l_Lean_logAt___redArg(v_inst_488_, v_inst_489_, v_inst_490_, v_inst_491_, v_ref_492_, v___x_495_, v___x_496_, v___x_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedWarningAt(lean_object* v_m_499_, lean_object* v_inst_500_, lean_object* v_inst_501_, lean_object* v_inst_502_, lean_object* v_inst_503_, lean_object* v_ref_504_, lean_object* v_name_505_, lean_object* v_msgData_506_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l_Lean_logNamedWarningAt___redArg(v_inst_500_, v_inst_501_, v_inst_502_, v_inst_503_, v_ref_504_, v_name_505_, v_msgData_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___redArg(lean_object* v_inst_508_, lean_object* v_inst_509_, lean_object* v_inst_510_, lean_object* v_inst_511_, lean_object* v_ref_512_, lean_object* v_msgData_513_){
_start:
{
uint8_t v___x_514_; uint8_t v___x_515_; lean_object* v___x_516_; 
v___x_514_ = 0;
v___x_515_ = 0;
v___x_516_ = l_Lean_logAt___redArg(v_inst_508_, v_inst_509_, v_inst_510_, v_inst_511_, v_ref_512_, v_msgData_513_, v___x_514_, v___x_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt(lean_object* v_m_517_, lean_object* v_inst_518_, lean_object* v_inst_519_, lean_object* v_inst_520_, lean_object* v_inst_521_, lean_object* v_ref_522_, lean_object* v_msgData_523_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_Lean_logInfoAt___redArg(v_inst_518_, v_inst_519_, v_inst_520_, v_inst_521_, v_ref_522_, v_msgData_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___redArg___lam__0(lean_object* v_inst_525_, lean_object* v_inst_526_, lean_object* v_inst_527_, lean_object* v_inst_528_, lean_object* v_msgData_529_, uint8_t v_severity_530_, uint8_t v_isSilent_531_, lean_object* v_ref_532_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = l_Lean_logAt___redArg(v_inst_525_, v_inst_526_, v_inst_527_, v_inst_528_, v_ref_532_, v_msgData_529_, v_severity_530_, v_isSilent_531_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___redArg___lam__0___boxed(lean_object* v_inst_534_, lean_object* v_inst_535_, lean_object* v_inst_536_, lean_object* v_inst_537_, lean_object* v_msgData_538_, lean_object* v_severity_539_, lean_object* v_isSilent_540_, lean_object* v_ref_541_){
_start:
{
uint8_t v_severity_boxed_542_; uint8_t v_isSilent_boxed_543_; lean_object* v_res_544_; 
v_severity_boxed_542_ = lean_unbox(v_severity_539_);
v_isSilent_boxed_543_ = lean_unbox(v_isSilent_540_);
v_res_544_ = l_Lean_log___redArg___lam__0(v_inst_534_, v_inst_535_, v_inst_536_, v_inst_537_, v_msgData_538_, v_severity_boxed_542_, v_isSilent_boxed_543_, v_ref_541_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___redArg(lean_object* v_inst_545_, lean_object* v_inst_546_, lean_object* v_inst_547_, lean_object* v_inst_548_, lean_object* v_msgData_549_, uint8_t v_severity_550_, uint8_t v_isSilent_551_){
_start:
{
lean_object* v_toBind_552_; lean_object* v_getRef_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___f_556_; lean_object* v___x_557_; 
v_toBind_552_ = lean_ctor_get(v_inst_545_, 1);
lean_inc(v_toBind_552_);
v_getRef_553_ = lean_ctor_get(v_inst_546_, 1);
lean_inc(v_getRef_553_);
v___x_554_ = lean_box(v_severity_550_);
v___x_555_ = lean_box(v_isSilent_551_);
v___f_556_ = lean_alloc_closure((void*)(l_Lean_log___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_556_, 0, v_inst_545_);
lean_closure_set(v___f_556_, 1, v_inst_546_);
lean_closure_set(v___f_556_, 2, v_inst_547_);
lean_closure_set(v___f_556_, 3, v_inst_548_);
lean_closure_set(v___f_556_, 4, v_msgData_549_);
lean_closure_set(v___f_556_, 5, v___x_554_);
lean_closure_set(v___f_556_, 6, v___x_555_);
v___x_557_ = lean_apply_4(v_toBind_552_, lean_box(0), lean_box(0), v_getRef_553_, v___f_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___redArg___boxed(lean_object* v_inst_558_, lean_object* v_inst_559_, lean_object* v_inst_560_, lean_object* v_inst_561_, lean_object* v_msgData_562_, lean_object* v_severity_563_, lean_object* v_isSilent_564_){
_start:
{
uint8_t v_severity_boxed_565_; uint8_t v_isSilent_boxed_566_; lean_object* v_res_567_; 
v_severity_boxed_565_ = lean_unbox(v_severity_563_);
v_isSilent_boxed_566_ = lean_unbox(v_isSilent_564_);
v_res_567_ = l_Lean_log___redArg(v_inst_558_, v_inst_559_, v_inst_560_, v_inst_561_, v_msgData_562_, v_severity_boxed_565_, v_isSilent_boxed_566_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_log(lean_object* v_m_568_, lean_object* v_inst_569_, lean_object* v_inst_570_, lean_object* v_inst_571_, lean_object* v_inst_572_, lean_object* v_msgData_573_, uint8_t v_severity_574_, uint8_t v_isSilent_575_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = l_Lean_log___redArg(v_inst_569_, v_inst_570_, v_inst_571_, v_inst_572_, v_msgData_573_, v_severity_574_, v_isSilent_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___boxed(lean_object* v_m_577_, lean_object* v_inst_578_, lean_object* v_inst_579_, lean_object* v_inst_580_, lean_object* v_inst_581_, lean_object* v_msgData_582_, lean_object* v_severity_583_, lean_object* v_isSilent_584_){
_start:
{
uint8_t v_severity_boxed_585_; uint8_t v_isSilent_boxed_586_; lean_object* v_res_587_; 
v_severity_boxed_585_ = lean_unbox(v_severity_583_);
v_isSilent_boxed_586_ = lean_unbox(v_isSilent_584_);
v_res_587_ = l_Lean_log(v_m_577_, v_inst_578_, v_inst_579_, v_inst_580_, v_inst_581_, v_msgData_582_, v_severity_boxed_585_, v_isSilent_boxed_586_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___redArg(lean_object* v_inst_588_, lean_object* v_inst_589_, lean_object* v_inst_590_, lean_object* v_inst_591_, lean_object* v_msgData_592_){
_start:
{
uint8_t v___x_593_; uint8_t v___x_594_; lean_object* v___x_595_; 
v___x_593_ = 2;
v___x_594_ = 0;
v___x_595_ = l_Lean_log___redArg(v_inst_588_, v_inst_589_, v_inst_590_, v_inst_591_, v_msgData_592_, v___x_593_, v___x_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError(lean_object* v_m_596_, lean_object* v_inst_597_, lean_object* v_inst_598_, lean_object* v_inst_599_, lean_object* v_inst_600_, lean_object* v_msgData_601_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l_Lean_logError___redArg(v_inst_597_, v_inst_598_, v_inst_599_, v_inst_600_, v_msgData_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedError___redArg(lean_object* v_inst_603_, lean_object* v_inst_604_, lean_object* v_inst_605_, lean_object* v_inst_606_, lean_object* v_name_607_, lean_object* v_msgData_608_){
_start:
{
lean_object* v___x_609_; uint8_t v___x_610_; uint8_t v___x_611_; lean_object* v___x_612_; 
v___x_609_ = l_Lean_MessageData_tagWithErrorName(v_msgData_608_, v_name_607_);
v___x_610_ = 2;
v___x_611_ = 0;
v___x_612_ = l_Lean_log___redArg(v_inst_603_, v_inst_604_, v_inst_605_, v_inst_606_, v___x_609_, v___x_610_, v___x_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedError(lean_object* v_m_613_, lean_object* v_inst_614_, lean_object* v_inst_615_, lean_object* v_inst_616_, lean_object* v_inst_617_, lean_object* v_name_618_, lean_object* v_msgData_619_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = l_Lean_logNamedError___redArg(v_inst_614_, v_inst_615_, v_inst_616_, v_inst_617_, v_name_618_, v_msgData_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___redArg(lean_object* v_inst_621_, lean_object* v_inst_622_, lean_object* v_inst_623_, lean_object* v_inst_624_, lean_object* v_msgData_625_){
_start:
{
uint8_t v___x_626_; uint8_t v___x_627_; lean_object* v___x_628_; 
v___x_626_ = 1;
v___x_627_ = 0;
v___x_628_ = l_Lean_log___redArg(v_inst_621_, v_inst_622_, v_inst_623_, v_inst_624_, v_msgData_625_, v___x_626_, v___x_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning(lean_object* v_m_629_, lean_object* v_inst_630_, lean_object* v_inst_631_, lean_object* v_inst_632_, lean_object* v_inst_633_, lean_object* v_msgData_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_Lean_logWarning___redArg(v_inst_630_, v_inst_631_, v_inst_632_, v_inst_633_, v_msgData_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedWarning___redArg(lean_object* v_inst_636_, lean_object* v_inst_637_, lean_object* v_inst_638_, lean_object* v_inst_639_, lean_object* v_name_640_, lean_object* v_msgData_641_){
_start:
{
lean_object* v___x_642_; uint8_t v___x_643_; uint8_t v___x_644_; lean_object* v___x_645_; 
v___x_642_ = l_Lean_MessageData_tagWithErrorName(v_msgData_641_, v_name_640_);
v___x_643_ = 1;
v___x_644_ = 0;
v___x_645_ = l_Lean_log___redArg(v_inst_636_, v_inst_637_, v_inst_638_, v_inst_639_, v___x_642_, v___x_643_, v___x_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedWarning(lean_object* v_m_646_, lean_object* v_inst_647_, lean_object* v_inst_648_, lean_object* v_inst_649_, lean_object* v_inst_650_, lean_object* v_name_651_, lean_object* v_msgData_652_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l_Lean_logNamedWarning___redArg(v_inst_647_, v_inst_648_, v_inst_649_, v_inst_650_, v_name_651_, v_msgData_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___redArg(lean_object* v_inst_654_, lean_object* v_inst_655_, lean_object* v_inst_656_, lean_object* v_inst_657_, lean_object* v_msgData_658_){
_start:
{
uint8_t v___x_659_; uint8_t v___x_660_; lean_object* v___x_661_; 
v___x_659_ = 0;
v___x_660_ = 0;
v___x_661_ = l_Lean_log___redArg(v_inst_654_, v_inst_655_, v_inst_656_, v_inst_657_, v_msgData_658_, v___x_659_, v___x_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo(lean_object* v_m_662_, lean_object* v_inst_663_, lean_object* v_inst_664_, lean_object* v_inst_665_, lean_object* v_inst_666_, lean_object* v_msgData_667_){
_start:
{
lean_object* v___x_668_; 
v___x_668_ = l_Lean_logInfo___redArg(v_inst_663_, v_inst_664_, v_inst_665_, v_inst_666_, v_msgData_667_);
return v___x_668_;
}
}
static lean_object* _init_l_Lean_logUnknownDecl___redArg___closed__1(void){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = ((lean_object*)(l_Lean_logUnknownDecl___redArg___closed__0));
v___x_671_ = l_Lean_stringToMessageData(v___x_670_);
return v___x_671_;
}
}
static lean_object* _init_l_Lean_logUnknownDecl___redArg___closed__3(void){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = ((lean_object*)(l_Lean_logUnknownDecl___redArg___closed__2));
v___x_674_ = l_Lean_stringToMessageData(v___x_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_logUnknownDecl___redArg(lean_object* v_inst_675_, lean_object* v_inst_676_, lean_object* v_inst_677_, lean_object* v_inst_678_, lean_object* v_declName_679_){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_680_ = lean_obj_once(&l_Lean_logUnknownDecl___redArg___closed__1, &l_Lean_logUnknownDecl___redArg___closed__1_once, _init_l_Lean_logUnknownDecl___redArg___closed__1);
v___x_681_ = l_Lean_MessageData_ofName(v_declName_679_);
v___x_682_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_682_, 0, v___x_680_);
lean_ctor_set(v___x_682_, 1, v___x_681_);
v___x_683_ = lean_obj_once(&l_Lean_logUnknownDecl___redArg___closed__3, &l_Lean_logUnknownDecl___redArg___closed__3_once, _init_l_Lean_logUnknownDecl___redArg___closed__3);
v___x_684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_684_, 0, v___x_682_);
lean_ctor_set(v___x_684_, 1, v___x_683_);
v___x_685_ = l_Lean_logError___redArg(v_inst_675_, v_inst_676_, v_inst_677_, v_inst_678_, v___x_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_logUnknownDecl(lean_object* v_m_686_, lean_object* v_inst_687_, lean_object* v_inst_688_, lean_object* v_inst_689_, lean_object* v_inst_690_, lean_object* v_declName_691_){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = l_Lean_logUnknownDecl___redArg(v_inst_687_, v_inst_688_, v_inst_689_, v_inst_690_, v_declName_691_);
return v___x_692_;
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
