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
lean_object* l_Lean_Option_register___at___00__private_Lean_Log_0__Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__spec__0(lean_object* v_name_82_, lean_object* v_decl_83_, lean_object* v_ref_84_){
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
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Log_0__Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_82_ = stack[0].m_obj;
lean_object* v_decl_83_ = stack[1].m_obj;
lean_object* v_ref_84_ = stack[2].m_obj;
lean_object* v_res_110_;
v_res_110_ = l_Lean_Option_register___at___00__private_Lean_Log_0__Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__spec__0(v_name_82_, v_decl_83_, v_ref_84_);
stack->m_obj
 = v_res_110_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Log_0__Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_111_, lean_object* v_decl_112_, lean_object* v_ref_113_, lean_object* v_a_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lean_Option_register___at___00__private_Lean_Log_0__Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__spec__0(v_name_111_, v_decl_112_, v_ref_113_);
lean_dec_ref(v_decl_112_);
return v_res_115_;
}
}
lean_object* l___private_Lean_Log_0__Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_130_ = ((lean_object*)(l___private_Lean_Log_0__Lean_initFn___closed__1_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_));
v___x_131_ = ((lean_object*)(l___private_Lean_Log_0__Lean_initFn___closed__3_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_));
v___x_132_ = ((lean_object*)(l___private_Lean_Log_0__Lean_initFn___closed__5_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_));
v___x_133_ = l_Lean_Option_register___at___00__private_Lean_Log_0__Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__spec__0(v___x_130_, v___x_131_, v___x_132_);
return v___x_133_;
}
}
LEAN_EXPORT void l___private_Lean_Log_0__Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_134_;
v_res_134_ = l___private_Lean_Log_0__Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_();
stack->m_obj
 = v_res_134_;
}
LEAN_EXPORT lean_object* l___private_Lean_Log_0__Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4____boxed(lean_object* v_a_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l___private_Lean_Log_0__Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_();
return v_res_136_;
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
v___x_166_ = ((lean_object*)(l_Lean_errorDescriptionWidget));
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
lean_object* l_Lean_logAt___redArg___lam__0(lean_object* v_fileMap_194_, lean_object* v___y_195_, lean_object* v___y_196_, uint8_t v___y_197_, uint8_t v___y_198_, uint8_t v_isSilent_199_, lean_object* v_msgData_200_, lean_object* v_logMessage_201_, lean_object* v_____do__lift_202_){
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
LEAN_EXPORT void l_Lean_logAt___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fileMap_194_ = stack[0].m_obj;
lean_object* v___y_195_ = stack[1].m_obj;
lean_object* v___y_196_ = stack[2].m_obj;
uint8_t v___y_197_ = stack[3].m_num;
uint8_t v___y_198_ = stack[4].m_num;
uint8_t v_isSilent_199_ = stack[5].m_num;
lean_object* v_msgData_200_ = stack[6].m_obj;
lean_object* v_logMessage_201_ = stack[7].m_obj;
lean_object* v_____do__lift_202_ = stack[8].m_obj;
lean_object* v_res_209_;
v_res_209_ = l_Lean_logAt___redArg___lam__0(v_fileMap_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v_isSilent_199_, v_msgData_200_, v_logMessage_201_, v_____do__lift_202_);
stack->m_obj
 = v_res_209_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__0___boxed(lean_object* v_fileMap_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v_isSilent_215_, lean_object* v_msgData_216_, lean_object* v_logMessage_217_, lean_object* v_____do__lift_218_){
_start:
{
uint8_t v___y_230__boxed_219_; uint8_t v___y_231__boxed_220_; uint8_t v_isSilent_boxed_221_; lean_object* v_res_222_; 
v___y_230__boxed_219_ = lean_unbox(v___y_213_);
v___y_231__boxed_220_ = lean_unbox(v___y_214_);
v_isSilent_boxed_221_ = lean_unbox(v_isSilent_215_);
v_res_222_ = l_Lean_logAt___redArg___lam__0(v_fileMap_210_, v___y_211_, v___y_212_, v___y_230__boxed_219_, v___y_231__boxed_220_, v_isSilent_boxed_221_, v_msgData_216_, v_logMessage_217_, v_____do__lift_218_);
lean_dec(v___y_212_);
lean_dec(v___y_211_);
return v_res_222_;
}
}
lean_object* l_Lean_logAt___redArg___lam__1(lean_object* v_fileMap_223_, lean_object* v___y_224_, lean_object* v___y_225_, uint8_t v___y_226_, uint8_t v___y_227_, uint8_t v_isSilent_228_, lean_object* v_logMessage_229_, lean_object* v_toBind_230_, lean_object* v_getFileName_231_, lean_object* v_msgData_232_){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___f_236_; lean_object* v___x_237_; 
v___x_233_ = lean_box(v___y_226_);
v___x_234_ = lean_box(v___y_227_);
v___x_235_ = lean_box(v_isSilent_228_);
v___f_236_ = lean_alloc_closure((void*)(l_Lean_logAt___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_236_, 0, v_fileMap_223_);
lean_closure_set(v___f_236_, 1, v___y_224_);
lean_closure_set(v___f_236_, 2, v___y_225_);
lean_closure_set(v___f_236_, 3, v___x_233_);
lean_closure_set(v___f_236_, 4, v___x_234_);
lean_closure_set(v___f_236_, 5, v___x_235_);
lean_closure_set(v___f_236_, 6, v_msgData_232_);
lean_closure_set(v___f_236_, 7, v_logMessage_229_);
v___x_237_ = lean_apply_4(v_toBind_230_, lean_box(0), lean_box(0), v_getFileName_231_, v___f_236_);
return v___x_237_;
}
}
LEAN_EXPORT void l_Lean_logAt___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_fileMap_223_ = stack[0].m_obj;
lean_object* v___y_224_ = stack[1].m_obj;
lean_object* v___y_225_ = stack[2].m_obj;
uint8_t v___y_226_ = stack[3].m_num;
uint8_t v___y_227_ = stack[4].m_num;
uint8_t v_isSilent_228_ = stack[5].m_num;
lean_object* v_logMessage_229_ = stack[6].m_obj;
lean_object* v_toBind_230_ = stack[7].m_obj;
lean_object* v_getFileName_231_ = stack[8].m_obj;
lean_object* v_msgData_232_ = stack[9].m_obj;
lean_object* v_res_238_;
v_res_238_ = l_Lean_logAt___redArg___lam__1(v_fileMap_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_, v_isSilent_228_, v_logMessage_229_, v_toBind_230_, v_getFileName_231_, v_msgData_232_);
stack->m_obj
 = v_res_238_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__1___boxed(lean_object* v_fileMap_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v_isSilent_244_, lean_object* v_logMessage_245_, lean_object* v_toBind_246_, lean_object* v_getFileName_247_, lean_object* v_msgData_248_){
_start:
{
uint8_t v___y_275__boxed_249_; uint8_t v___y_276__boxed_250_; uint8_t v_isSilent_boxed_251_; lean_object* v_res_252_; 
v___y_275__boxed_249_ = lean_unbox(v___y_242_);
v___y_276__boxed_250_ = lean_unbox(v___y_243_);
v_isSilent_boxed_251_ = lean_unbox(v_isSilent_244_);
v_res_252_ = l_Lean_logAt___redArg___lam__1(v_fileMap_239_, v___y_240_, v___y_241_, v___y_275__boxed_249_, v___y_276__boxed_250_, v_isSilent_boxed_251_, v_logMessage_245_, v_toBind_246_, v_getFileName_247_, v_msgData_248_);
return v_res_252_;
}
}
lean_object* l_Lean_logAt___redArg___lam__2(lean_object* v___y_253_, lean_object* v___y_254_, uint8_t v___y_255_, uint8_t v___y_256_, uint8_t v_isSilent_257_, lean_object* v_logMessage_258_, lean_object* v_toBind_259_, lean_object* v_getFileName_260_, lean_object* v_msgData_261_, lean_object* v_inst_262_, lean_object* v_fileMap_263_){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___f_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_264_ = lean_box(v___y_255_);
v___x_265_ = lean_box(v___y_256_);
v___x_266_ = lean_box(v_isSilent_257_);
lean_inc(v_toBind_259_);
v___f_267_ = lean_alloc_closure((void*)(l_Lean_logAt___redArg___lam__1___boxed), 10, 9);
lean_closure_set(v___f_267_, 0, v_fileMap_263_);
lean_closure_set(v___f_267_, 1, v___y_253_);
lean_closure_set(v___f_267_, 2, v___y_254_);
lean_closure_set(v___f_267_, 3, v___x_264_);
lean_closure_set(v___f_267_, 4, v___x_265_);
lean_closure_set(v___f_267_, 5, v___x_266_);
lean_closure_set(v___f_267_, 6, v_logMessage_258_);
lean_closure_set(v___f_267_, 7, v_toBind_259_);
lean_closure_set(v___f_267_, 8, v_getFileName_260_);
v___x_268_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_261_);
v___x_269_ = lean_apply_1(v_inst_262_, v___x_268_);
v___x_270_ = lean_apply_4(v_toBind_259_, lean_box(0), lean_box(0), v___x_269_, v___f_267_);
return v___x_270_;
}
}
LEAN_EXPORT void l_Lean_logAt___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_253_ = stack[0].m_obj;
lean_object* v___y_254_ = stack[1].m_obj;
uint8_t v___y_255_ = stack[2].m_num;
uint8_t v___y_256_ = stack[3].m_num;
uint8_t v_isSilent_257_ = stack[4].m_num;
lean_object* v_logMessage_258_ = stack[5].m_obj;
lean_object* v_toBind_259_ = stack[6].m_obj;
lean_object* v_getFileName_260_ = stack[7].m_obj;
lean_object* v_msgData_261_ = stack[8].m_obj;
lean_object* v_inst_262_ = stack[9].m_obj;
lean_object* v_fileMap_263_ = stack[10].m_obj;
lean_object* v_res_271_;
v_res_271_ = l_Lean_logAt___redArg___lam__2(v___y_253_, v___y_254_, v___y_255_, v___y_256_, v_isSilent_257_, v_logMessage_258_, v_toBind_259_, v_getFileName_260_, v_msgData_261_, v_inst_262_, v_fileMap_263_);
stack->m_obj
 = v_res_271_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__2___boxed(lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v_isSilent_276_, lean_object* v_logMessage_277_, lean_object* v_toBind_278_, lean_object* v_getFileName_279_, lean_object* v_msgData_280_, lean_object* v_inst_281_, lean_object* v_fileMap_282_){
_start:
{
uint8_t v___y_310__boxed_283_; uint8_t v___y_311__boxed_284_; uint8_t v_isSilent_boxed_285_; lean_object* v_res_286_; 
v___y_310__boxed_283_ = lean_unbox(v___y_274_);
v___y_311__boxed_284_ = lean_unbox(v___y_275_);
v_isSilent_boxed_285_ = lean_unbox(v_isSilent_276_);
v_res_286_ = l_Lean_logAt___redArg___lam__2(v___y_272_, v___y_273_, v___y_310__boxed_283_, v___y_311__boxed_284_, v_isSilent_boxed_285_, v_logMessage_277_, v_toBind_278_, v_getFileName_279_, v_msgData_280_, v_inst_281_, v_fileMap_282_);
return v_res_286_;
}
}
lean_object* l_Lean_logAt___redArg___lam__3(lean_object* v_ref_287_, uint8_t v___y_288_, uint8_t v___y_289_, uint8_t v_isSilent_290_, lean_object* v_logMessage_291_, lean_object* v_toBind_292_, lean_object* v_getFileName_293_, lean_object* v_msgData_294_, lean_object* v_inst_295_, lean_object* v_toMonadFileMap_296_, lean_object* v_____do__lift_297_){
_start:
{
lean_object* v___y_299_; lean_object* v___y_300_; lean_object* v_ref_306_; lean_object* v___y_308_; lean_object* v___x_311_; 
v_ref_306_ = l_Lean_replaceRef(v_ref_287_, v_____do__lift_297_);
v___x_311_ = l_Lean_Syntax_getPos_x3f(v_ref_306_, v___y_288_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v___x_312_; 
v___x_312_ = lean_unsigned_to_nat(0u);
v___y_308_ = v___x_312_;
goto v___jp_307_;
}
else
{
lean_object* v_val_313_; 
v_val_313_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_val_313_);
lean_dec_ref_known(v___x_311_, 1);
v___y_308_ = v_val_313_;
goto v___jp_307_;
}
v___jp_298_:
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___f_304_; lean_object* v___x_305_; 
v___x_301_ = lean_box(v___y_288_);
v___x_302_ = lean_box(v___y_289_);
v___x_303_ = lean_box(v_isSilent_290_);
lean_inc(v_toBind_292_);
v___f_304_ = lean_alloc_closure((void*)(l_Lean_logAt___redArg___lam__2___boxed), 11, 10);
lean_closure_set(v___f_304_, 0, v___y_299_);
lean_closure_set(v___f_304_, 1, v___y_300_);
lean_closure_set(v___f_304_, 2, v___x_301_);
lean_closure_set(v___f_304_, 3, v___x_302_);
lean_closure_set(v___f_304_, 4, v___x_303_);
lean_closure_set(v___f_304_, 5, v_logMessage_291_);
lean_closure_set(v___f_304_, 6, v_toBind_292_);
lean_closure_set(v___f_304_, 7, v_getFileName_293_);
lean_closure_set(v___f_304_, 8, v_msgData_294_);
lean_closure_set(v___f_304_, 9, v_inst_295_);
v___x_305_ = lean_apply_4(v_toBind_292_, lean_box(0), lean_box(0), v_toMonadFileMap_296_, v___f_304_);
return v___x_305_;
}
v___jp_307_:
{
lean_object* v___x_309_; 
v___x_309_ = l_Lean_Syntax_getTailPos_x3f(v_ref_306_, v___y_288_);
lean_dec(v_ref_306_);
if (lean_obj_tag(v___x_309_) == 0)
{
lean_inc(v___y_308_);
v___y_299_ = v___y_308_;
v___y_300_ = v___y_308_;
goto v___jp_298_;
}
else
{
lean_object* v_val_310_; 
v_val_310_ = lean_ctor_get(v___x_309_, 0);
lean_inc(v_val_310_);
lean_dec_ref_known(v___x_309_, 1);
v___y_299_ = v___y_308_;
v___y_300_ = v_val_310_;
goto v___jp_298_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_287_ = stack[0].m_obj;
uint8_t v___y_288_ = stack[1].m_num;
uint8_t v___y_289_ = stack[2].m_num;
uint8_t v_isSilent_290_ = stack[3].m_num;
lean_object* v_logMessage_291_ = stack[4].m_obj;
lean_object* v_toBind_292_ = stack[5].m_obj;
lean_object* v_getFileName_293_ = stack[6].m_obj;
lean_object* v_msgData_294_ = stack[7].m_obj;
lean_object* v_inst_295_ = stack[8].m_obj;
lean_object* v_toMonadFileMap_296_ = stack[9].m_obj;
lean_object* v_____do__lift_297_ = stack[10].m_obj;
lean_object* v_res_314_;
v_res_314_ = l_Lean_logAt___redArg___lam__3(v_ref_287_, v___y_288_, v___y_289_, v_isSilent_290_, v_logMessage_291_, v_toBind_292_, v_getFileName_293_, v_msgData_294_, v_inst_295_, v_toMonadFileMap_296_, v_____do__lift_297_);
stack->m_obj
 = v_res_314_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__3___boxed(lean_object* v_ref_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v_isSilent_318_, lean_object* v_logMessage_319_, lean_object* v_toBind_320_, lean_object* v_getFileName_321_, lean_object* v_msgData_322_, lean_object* v_inst_323_, lean_object* v_toMonadFileMap_324_, lean_object* v_____do__lift_325_){
_start:
{
uint8_t v___y_355__boxed_326_; uint8_t v___y_356__boxed_327_; uint8_t v_isSilent_boxed_328_; lean_object* v_res_329_; 
v___y_355__boxed_326_ = lean_unbox(v___y_316_);
v___y_356__boxed_327_ = lean_unbox(v___y_317_);
v_isSilent_boxed_328_ = lean_unbox(v_isSilent_318_);
v_res_329_ = l_Lean_logAt___redArg___lam__3(v_ref_315_, v___y_355__boxed_326_, v___y_356__boxed_327_, v_isSilent_boxed_328_, v_logMessage_319_, v_toBind_320_, v_getFileName_321_, v_msgData_322_, v_inst_323_, v_toMonadFileMap_324_, v_____do__lift_325_);
lean_dec(v_____do__lift_325_);
lean_dec(v_ref_315_);
return v_res_329_;
}
}
lean_object* l_Lean_logAt___redArg___lam__4(lean_object* v_ref_330_, uint8_t v___y_331_, uint8_t v_isSilent_332_, lean_object* v_logMessage_333_, lean_object* v_toBind_334_, lean_object* v_getFileName_335_, lean_object* v_msgData_336_, lean_object* v_inst_337_, lean_object* v_toMonadFileMap_338_, lean_object* v_getRef_339_, uint8_t v_severity_340_, uint8_t v___x_341_, lean_object* v___x_342_, lean_object* v_____do__lift_343_){
_start:
{
uint8_t v___y_345_; uint8_t v___y_352_; uint8_t v___x_353_; uint8_t v___x_354_; 
v___x_353_ = 1;
v___x_354_ = l_Lean_instBEqMessageSeverity_beq(v_severity_340_, v___x_353_);
if (v___x_354_ == 0)
{
lean_dec_ref(v___x_342_);
v___y_352_ = v___x_354_;
goto v___jp_351_;
}
else
{
lean_object* v___x_355_; lean_object* v___x_356_; uint8_t v___x_357_; 
v___x_355_ = l_Lean_warningAsError;
v___x_356_ = l_Lean_Option_get___redArg(v___x_342_, v_____do__lift_343_, v___x_355_);
v___x_357_ = lean_unbox(v___x_356_);
lean_dec(v___x_356_);
v___y_352_ = v___x_357_;
goto v___jp_351_;
}
v___jp_344_:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___f_349_; lean_object* v___x_350_; 
v___x_346_ = lean_box(v___y_331_);
v___x_347_ = lean_box(v___y_345_);
v___x_348_ = lean_box(v_isSilent_332_);
lean_inc(v_toBind_334_);
v___f_349_ = lean_alloc_closure((void*)(l_Lean_logAt___redArg___lam__3___boxed), 11, 10);
lean_closure_set(v___f_349_, 0, v_ref_330_);
lean_closure_set(v___f_349_, 1, v___x_346_);
lean_closure_set(v___f_349_, 2, v___x_347_);
lean_closure_set(v___f_349_, 3, v___x_348_);
lean_closure_set(v___f_349_, 4, v_logMessage_333_);
lean_closure_set(v___f_349_, 5, v_toBind_334_);
lean_closure_set(v___f_349_, 6, v_getFileName_335_);
lean_closure_set(v___f_349_, 7, v_msgData_336_);
lean_closure_set(v___f_349_, 8, v_inst_337_);
lean_closure_set(v___f_349_, 9, v_toMonadFileMap_338_);
v___x_350_ = lean_apply_4(v_toBind_334_, lean_box(0), lean_box(0), v_getRef_339_, v___f_349_);
return v___x_350_;
}
v___jp_351_:
{
if (v___y_352_ == 0)
{
v___y_345_ = v_severity_340_;
goto v___jp_344_;
}
else
{
v___y_345_ = v___x_341_;
goto v___jp_344_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_330_ = stack[0].m_obj;
uint8_t v___y_331_ = stack[1].m_num;
uint8_t v_isSilent_332_ = stack[2].m_num;
lean_object* v_logMessage_333_ = stack[3].m_obj;
lean_object* v_toBind_334_ = stack[4].m_obj;
lean_object* v_getFileName_335_ = stack[5].m_obj;
lean_object* v_msgData_336_ = stack[6].m_obj;
lean_object* v_inst_337_ = stack[7].m_obj;
lean_object* v_toMonadFileMap_338_ = stack[8].m_obj;
lean_object* v_getRef_339_ = stack[9].m_obj;
uint8_t v_severity_340_ = stack[10].m_num;
uint8_t v___x_341_ = stack[11].m_num;
lean_object* v___x_342_ = stack[12].m_obj;
lean_object* v_____do__lift_343_ = stack[13].m_obj;
lean_object* v_res_358_;
v_res_358_ = l_Lean_logAt___redArg___lam__4(v_ref_330_, v___y_331_, v_isSilent_332_, v_logMessage_333_, v_toBind_334_, v_getFileName_335_, v_msgData_336_, v_inst_337_, v_toMonadFileMap_338_, v_getRef_339_, v_severity_340_, v___x_341_, v___x_342_, v_____do__lift_343_);
stack->m_obj
 = v_res_358_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__4___boxed(lean_object* v_ref_359_, lean_object* v___y_360_, lean_object* v_isSilent_361_, lean_object* v_logMessage_362_, lean_object* v_toBind_363_, lean_object* v_getFileName_364_, lean_object* v_msgData_365_, lean_object* v_inst_366_, lean_object* v_toMonadFileMap_367_, lean_object* v_getRef_368_, lean_object* v_severity_369_, lean_object* v___x_370_, lean_object* v___x_371_, lean_object* v_____do__lift_372_){
_start:
{
uint8_t v___y_420__boxed_373_; uint8_t v_isSilent_boxed_374_; uint8_t v_severity_boxed_375_; uint8_t v___x_422__boxed_376_; lean_object* v_res_377_; 
v___y_420__boxed_373_ = lean_unbox(v___y_360_);
v_isSilent_boxed_374_ = lean_unbox(v_isSilent_361_);
v_severity_boxed_375_ = lean_unbox(v_severity_369_);
v___x_422__boxed_376_ = lean_unbox(v___x_370_);
v_res_377_ = l_Lean_logAt___redArg___lam__4(v_ref_359_, v___y_420__boxed_373_, v_isSilent_boxed_374_, v_logMessage_362_, v_toBind_363_, v_getFileName_364_, v_msgData_365_, v_inst_366_, v_toMonadFileMap_367_, v_getRef_368_, v_severity_boxed_375_, v___x_422__boxed_376_, v___x_371_, v_____do__lift_372_);
lean_dec_ref(v_____do__lift_372_);
return v_res_377_;
}
}
lean_object* l_Lean_logAt___redArg(lean_object* v_inst_378_, lean_object* v_inst_379_, lean_object* v_inst_380_, lean_object* v_inst_381_, lean_object* v_ref_382_, lean_object* v_msgData_383_, uint8_t v_severity_384_, uint8_t v_isSilent_385_){
_start:
{
lean_object* v___x_386_; lean_object* v_toApplicative_387_; lean_object* v_toBind_388_; lean_object* v_toMonadFileMap_389_; lean_object* v_getRef_390_; lean_object* v_getFileName_391_; lean_object* v_logMessage_392_; lean_object* v_toPure_393_; uint8_t v___x_394_; uint8_t v___y_396_; uint8_t v___x_406_; 
v___x_386_ = l_Lean_KVMap_instValueBool;
v_toApplicative_387_ = lean_ctor_get(v_inst_378_, 0);
lean_inc_ref(v_toApplicative_387_);
v_toBind_388_ = lean_ctor_get(v_inst_378_, 1);
lean_inc(v_toBind_388_);
lean_dec_ref(v_inst_378_);
v_toMonadFileMap_389_ = lean_ctor_get(v_inst_379_, 0);
lean_inc(v_toMonadFileMap_389_);
v_getRef_390_ = lean_ctor_get(v_inst_379_, 1);
lean_inc(v_getRef_390_);
v_getFileName_391_ = lean_ctor_get(v_inst_379_, 2);
lean_inc(v_getFileName_391_);
v_logMessage_392_ = lean_ctor_get(v_inst_379_, 4);
lean_inc(v_logMessage_392_);
lean_dec_ref(v_inst_379_);
v_toPure_393_ = lean_ctor_get(v_toApplicative_387_, 1);
lean_inc(v_toPure_393_);
lean_dec_ref(v_toApplicative_387_);
v___x_394_ = 2;
v___x_406_ = l_Lean_instBEqMessageSeverity_beq(v_severity_384_, v___x_394_);
if (v___x_406_ == 0)
{
v___y_396_ = v___x_406_;
goto v___jp_395_;
}
else
{
uint8_t v___x_407_; 
lean_inc_ref(v_msgData_383_);
v___x_407_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_383_);
v___y_396_ = v___x_407_;
goto v___jp_395_;
}
v___jp_395_:
{
if (v___y_396_ == 0)
{
lean_object* v_getOptions_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___f_402_; lean_object* v___x_403_; 
lean_dec(v_toPure_393_);
v_getOptions_397_ = lean_ctor_get(v_inst_381_, 0);
lean_inc(v_getOptions_397_);
lean_dec_ref(v_inst_381_);
v___x_398_ = lean_box(v___y_396_);
v___x_399_ = lean_box(v_isSilent_385_);
v___x_400_ = lean_box(v_severity_384_);
v___x_401_ = lean_box(v___x_394_);
lean_inc(v_toBind_388_);
v___f_402_ = lean_alloc_closure((void*)(l_Lean_logAt___redArg___lam__4___boxed), 14, 13);
lean_closure_set(v___f_402_, 0, v_ref_382_);
lean_closure_set(v___f_402_, 1, v___x_398_);
lean_closure_set(v___f_402_, 2, v___x_399_);
lean_closure_set(v___f_402_, 3, v_logMessage_392_);
lean_closure_set(v___f_402_, 4, v_toBind_388_);
lean_closure_set(v___f_402_, 5, v_getFileName_391_);
lean_closure_set(v___f_402_, 6, v_msgData_383_);
lean_closure_set(v___f_402_, 7, v_inst_380_);
lean_closure_set(v___f_402_, 8, v_toMonadFileMap_389_);
lean_closure_set(v___f_402_, 9, v_getRef_390_);
lean_closure_set(v___f_402_, 10, v___x_400_);
lean_closure_set(v___f_402_, 11, v___x_401_);
lean_closure_set(v___f_402_, 12, v___x_386_);
v___x_403_ = lean_apply_4(v_toBind_388_, lean_box(0), lean_box(0), v_getOptions_397_, v___f_402_);
return v___x_403_;
}
else
{
lean_object* v___x_404_; lean_object* v___x_405_; 
lean_dec(v_logMessage_392_);
lean_dec(v_getFileName_391_);
lean_dec(v_getRef_390_);
lean_dec(v_toMonadFileMap_389_);
lean_dec(v_toBind_388_);
lean_dec_ref(v_msgData_383_);
lean_dec(v_ref_382_);
lean_dec_ref(v_inst_381_);
lean_dec(v_inst_380_);
v___x_404_ = lean_box(0);
v___x_405_ = lean_apply_2(v_toPure_393_, lean_box(0), v___x_404_);
return v___x_405_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_378_ = stack[0].m_obj;
lean_object* v_inst_379_ = stack[1].m_obj;
lean_object* v_inst_380_ = stack[2].m_obj;
lean_object* v_inst_381_ = stack[3].m_obj;
lean_object* v_ref_382_ = stack[4].m_obj;
lean_object* v_msgData_383_ = stack[5].m_obj;
uint8_t v_severity_384_ = stack[6].m_num;
uint8_t v_isSilent_385_ = stack[7].m_num;
lean_object* v_res_408_;
v_res_408_ = l_Lean_logAt___redArg(v_inst_378_, v_inst_379_, v_inst_380_, v_inst_381_, v_ref_382_, v_msgData_383_, v_severity_384_, v_isSilent_385_);
stack->m_obj
 = v_res_408_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___boxed(lean_object* v_inst_409_, lean_object* v_inst_410_, lean_object* v_inst_411_, lean_object* v_inst_412_, lean_object* v_ref_413_, lean_object* v_msgData_414_, lean_object* v_severity_415_, lean_object* v_isSilent_416_){
_start:
{
uint8_t v_severity_boxed_417_; uint8_t v_isSilent_boxed_418_; lean_object* v_res_419_; 
v_severity_boxed_417_ = lean_unbox(v_severity_415_);
v_isSilent_boxed_418_ = lean_unbox(v_isSilent_416_);
v_res_419_ = l_Lean_logAt___redArg(v_inst_409_, v_inst_410_, v_inst_411_, v_inst_412_, v_ref_413_, v_msgData_414_, v_severity_boxed_417_, v_isSilent_boxed_418_);
return v_res_419_;
}
}
lean_object* l_Lean_logAt(lean_object* v_m_420_, lean_object* v_inst_421_, lean_object* v_inst_422_, lean_object* v_inst_423_, lean_object* v_inst_424_, lean_object* v_ref_425_, lean_object* v_msgData_426_, uint8_t v_severity_427_, uint8_t v_isSilent_428_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Lean_logAt___redArg(v_inst_421_, v_inst_422_, v_inst_423_, v_inst_424_, v_ref_425_, v_msgData_426_, v_severity_427_, v_isSilent_428_);
return v___x_429_;
}
}
LEAN_EXPORT void l_Lean_logAt_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_421_ = stack[1].m_obj;
lean_object* v_inst_422_ = stack[2].m_obj;
lean_object* v_inst_423_ = stack[3].m_obj;
lean_object* v_inst_424_ = stack[4].m_obj;
lean_object* v_ref_425_ = stack[5].m_obj;
lean_object* v_msgData_426_ = stack[6].m_obj;
uint8_t v_severity_427_ = stack[7].m_num;
uint8_t v_isSilent_428_ = stack[8].m_num;
lean_object* v_res_430_;
v_res_430_ = l_Lean_logAt(lean_box(0), v_inst_421_, v_inst_422_, v_inst_423_, v_inst_424_, v_ref_425_, v_msgData_426_, v_severity_427_, v_isSilent_428_);
stack->m_obj
 = v_res_430_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___boxed(lean_object* v_m_431_, lean_object* v_inst_432_, lean_object* v_inst_433_, lean_object* v_inst_434_, lean_object* v_inst_435_, lean_object* v_ref_436_, lean_object* v_msgData_437_, lean_object* v_severity_438_, lean_object* v_isSilent_439_){
_start:
{
uint8_t v_severity_boxed_440_; uint8_t v_isSilent_boxed_441_; lean_object* v_res_442_; 
v_severity_boxed_440_ = lean_unbox(v_severity_438_);
v_isSilent_boxed_441_ = lean_unbox(v_isSilent_439_);
v_res_442_ = l_Lean_logAt(v_m_431_, v_inst_432_, v_inst_433_, v_inst_434_, v_inst_435_, v_ref_436_, v_msgData_437_, v_severity_boxed_440_, v_isSilent_boxed_441_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___redArg(lean_object* v_inst_443_, lean_object* v_inst_444_, lean_object* v_inst_445_, lean_object* v_inst_446_, lean_object* v_ref_447_, lean_object* v_msgData_448_){
_start:
{
uint8_t v___x_449_; uint8_t v___x_450_; lean_object* v___x_451_; 
v___x_449_ = 2;
v___x_450_ = 0;
v___x_451_ = l_Lean_logAt___redArg(v_inst_443_, v_inst_444_, v_inst_445_, v_inst_446_, v_ref_447_, v_msgData_448_, v___x_449_, v___x_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt(lean_object* v_m_452_, lean_object* v_inst_453_, lean_object* v_inst_454_, lean_object* v_inst_455_, lean_object* v_inst_456_, lean_object* v_ref_457_, lean_object* v_msgData_458_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_Lean_logErrorAt___redArg(v_inst_453_, v_inst_454_, v_inst_455_, v_inst_456_, v_ref_457_, v_msgData_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedErrorAt___redArg(lean_object* v_inst_460_, lean_object* v_inst_461_, lean_object* v_inst_462_, lean_object* v_inst_463_, lean_object* v_ref_464_, lean_object* v_name_465_, lean_object* v_msgData_466_){
_start:
{
lean_object* v___x_467_; uint8_t v___x_468_; uint8_t v___x_469_; lean_object* v___x_470_; 
v___x_467_ = l_Lean_MessageData_tagWithErrorName(v_msgData_466_, v_name_465_);
v___x_468_ = 2;
v___x_469_ = 0;
v___x_470_ = l_Lean_logAt___redArg(v_inst_460_, v_inst_461_, v_inst_462_, v_inst_463_, v_ref_464_, v___x_467_, v___x_468_, v___x_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedErrorAt(lean_object* v_m_471_, lean_object* v_inst_472_, lean_object* v_inst_473_, lean_object* v_inst_474_, lean_object* v_inst_475_, lean_object* v_ref_476_, lean_object* v_name_477_, lean_object* v_msgData_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Lean_logNamedErrorAt___redArg(v_inst_472_, v_inst_473_, v_inst_474_, v_inst_475_, v_ref_476_, v_name_477_, v_msgData_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___redArg(lean_object* v_inst_480_, lean_object* v_inst_481_, lean_object* v_inst_482_, lean_object* v_inst_483_, lean_object* v_ref_484_, lean_object* v_msgData_485_){
_start:
{
uint8_t v___x_486_; uint8_t v___x_487_; lean_object* v___x_488_; 
v___x_486_ = 1;
v___x_487_ = 0;
v___x_488_ = l_Lean_logAt___redArg(v_inst_480_, v_inst_481_, v_inst_482_, v_inst_483_, v_ref_484_, v_msgData_485_, v___x_486_, v___x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt(lean_object* v_m_489_, lean_object* v_inst_490_, lean_object* v_inst_491_, lean_object* v_inst_492_, lean_object* v_inst_493_, lean_object* v_ref_494_, lean_object* v_msgData_495_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l_Lean_logWarningAt___redArg(v_inst_490_, v_inst_491_, v_inst_492_, v_inst_493_, v_ref_494_, v_msgData_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedWarningAt___redArg(lean_object* v_inst_497_, lean_object* v_inst_498_, lean_object* v_inst_499_, lean_object* v_inst_500_, lean_object* v_ref_501_, lean_object* v_name_502_, lean_object* v_msgData_503_){
_start:
{
lean_object* v___x_504_; uint8_t v___x_505_; uint8_t v___x_506_; lean_object* v___x_507_; 
v___x_504_ = l_Lean_MessageData_tagWithErrorName(v_msgData_503_, v_name_502_);
v___x_505_ = 1;
v___x_506_ = 0;
v___x_507_ = l_Lean_logAt___redArg(v_inst_497_, v_inst_498_, v_inst_499_, v_inst_500_, v_ref_501_, v___x_504_, v___x_505_, v___x_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedWarningAt(lean_object* v_m_508_, lean_object* v_inst_509_, lean_object* v_inst_510_, lean_object* v_inst_511_, lean_object* v_inst_512_, lean_object* v_ref_513_, lean_object* v_name_514_, lean_object* v_msgData_515_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l_Lean_logNamedWarningAt___redArg(v_inst_509_, v_inst_510_, v_inst_511_, v_inst_512_, v_ref_513_, v_name_514_, v_msgData_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___redArg(lean_object* v_inst_517_, lean_object* v_inst_518_, lean_object* v_inst_519_, lean_object* v_inst_520_, lean_object* v_ref_521_, lean_object* v_msgData_522_){
_start:
{
uint8_t v___x_523_; uint8_t v___x_524_; lean_object* v___x_525_; 
v___x_523_ = 0;
v___x_524_ = 0;
v___x_525_ = l_Lean_logAt___redArg(v_inst_517_, v_inst_518_, v_inst_519_, v_inst_520_, v_ref_521_, v_msgData_522_, v___x_523_, v___x_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt(lean_object* v_m_526_, lean_object* v_inst_527_, lean_object* v_inst_528_, lean_object* v_inst_529_, lean_object* v_inst_530_, lean_object* v_ref_531_, lean_object* v_msgData_532_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = l_Lean_logInfoAt___redArg(v_inst_527_, v_inst_528_, v_inst_529_, v_inst_530_, v_ref_531_, v_msgData_532_);
return v___x_533_;
}
}
lean_object* l_Lean_log___redArg___lam__0(lean_object* v_inst_534_, lean_object* v_inst_535_, lean_object* v_inst_536_, lean_object* v_inst_537_, lean_object* v_msgData_538_, uint8_t v_severity_539_, uint8_t v_isSilent_540_, lean_object* v_ref_541_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = l_Lean_logAt___redArg(v_inst_534_, v_inst_535_, v_inst_536_, v_inst_537_, v_ref_541_, v_msgData_538_, v_severity_539_, v_isSilent_540_);
return v___x_542_;
}
}
LEAN_EXPORT void l_Lean_log___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_534_ = stack[0].m_obj;
lean_object* v_inst_535_ = stack[1].m_obj;
lean_object* v_inst_536_ = stack[2].m_obj;
lean_object* v_inst_537_ = stack[3].m_obj;
lean_object* v_msgData_538_ = stack[4].m_obj;
uint8_t v_severity_539_ = stack[5].m_num;
uint8_t v_isSilent_540_ = stack[6].m_num;
lean_object* v_ref_541_ = stack[7].m_obj;
lean_object* v_res_543_;
v_res_543_ = l_Lean_log___redArg___lam__0(v_inst_534_, v_inst_535_, v_inst_536_, v_inst_537_, v_msgData_538_, v_severity_539_, v_isSilent_540_, v_ref_541_);
stack->m_obj
 = v_res_543_;
}
LEAN_EXPORT lean_object* l_Lean_log___redArg___lam__0___boxed(lean_object* v_inst_544_, lean_object* v_inst_545_, lean_object* v_inst_546_, lean_object* v_inst_547_, lean_object* v_msgData_548_, lean_object* v_severity_549_, lean_object* v_isSilent_550_, lean_object* v_ref_551_){
_start:
{
uint8_t v_severity_boxed_552_; uint8_t v_isSilent_boxed_553_; lean_object* v_res_554_; 
v_severity_boxed_552_ = lean_unbox(v_severity_549_);
v_isSilent_boxed_553_ = lean_unbox(v_isSilent_550_);
v_res_554_ = l_Lean_log___redArg___lam__0(v_inst_544_, v_inst_545_, v_inst_546_, v_inst_547_, v_msgData_548_, v_severity_boxed_552_, v_isSilent_boxed_553_, v_ref_551_);
return v_res_554_;
}
}
lean_object* l_Lean_log___redArg(lean_object* v_inst_555_, lean_object* v_inst_556_, lean_object* v_inst_557_, lean_object* v_inst_558_, lean_object* v_msgData_559_, uint8_t v_severity_560_, uint8_t v_isSilent_561_){
_start:
{
lean_object* v_toBind_562_; lean_object* v_getRef_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___f_566_; lean_object* v___x_567_; 
v_toBind_562_ = lean_ctor_get(v_inst_555_, 1);
lean_inc(v_toBind_562_);
v_getRef_563_ = lean_ctor_get(v_inst_556_, 1);
lean_inc(v_getRef_563_);
v___x_564_ = lean_box(v_severity_560_);
v___x_565_ = lean_box(v_isSilent_561_);
v___f_566_ = lean_alloc_closure((void*)(l_Lean_log___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_566_, 0, v_inst_555_);
lean_closure_set(v___f_566_, 1, v_inst_556_);
lean_closure_set(v___f_566_, 2, v_inst_557_);
lean_closure_set(v___f_566_, 3, v_inst_558_);
lean_closure_set(v___f_566_, 4, v_msgData_559_);
lean_closure_set(v___f_566_, 5, v___x_564_);
lean_closure_set(v___f_566_, 6, v___x_565_);
v___x_567_ = lean_apply_4(v_toBind_562_, lean_box(0), lean_box(0), v_getRef_563_, v___f_566_);
return v___x_567_;
}
}
LEAN_EXPORT void l_Lean_log___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_555_ = stack[0].m_obj;
lean_object* v_inst_556_ = stack[1].m_obj;
lean_object* v_inst_557_ = stack[2].m_obj;
lean_object* v_inst_558_ = stack[3].m_obj;
lean_object* v_msgData_559_ = stack[4].m_obj;
uint8_t v_severity_560_ = stack[5].m_num;
uint8_t v_isSilent_561_ = stack[6].m_num;
lean_object* v_res_568_;
v_res_568_ = l_Lean_log___redArg(v_inst_555_, v_inst_556_, v_inst_557_, v_inst_558_, v_msgData_559_, v_severity_560_, v_isSilent_561_);
stack->m_obj
 = v_res_568_;
}
LEAN_EXPORT lean_object* l_Lean_log___redArg___boxed(lean_object* v_inst_569_, lean_object* v_inst_570_, lean_object* v_inst_571_, lean_object* v_inst_572_, lean_object* v_msgData_573_, lean_object* v_severity_574_, lean_object* v_isSilent_575_){
_start:
{
uint8_t v_severity_boxed_576_; uint8_t v_isSilent_boxed_577_; lean_object* v_res_578_; 
v_severity_boxed_576_ = lean_unbox(v_severity_574_);
v_isSilent_boxed_577_ = lean_unbox(v_isSilent_575_);
v_res_578_ = l_Lean_log___redArg(v_inst_569_, v_inst_570_, v_inst_571_, v_inst_572_, v_msgData_573_, v_severity_boxed_576_, v_isSilent_boxed_577_);
return v_res_578_;
}
}
lean_object* l_Lean_log(lean_object* v_m_579_, lean_object* v_inst_580_, lean_object* v_inst_581_, lean_object* v_inst_582_, lean_object* v_inst_583_, lean_object* v_msgData_584_, uint8_t v_severity_585_, uint8_t v_isSilent_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_log___redArg(v_inst_580_, v_inst_581_, v_inst_582_, v_inst_583_, v_msgData_584_, v_severity_585_, v_isSilent_586_);
return v___x_587_;
}
}
LEAN_EXPORT void l_Lean_log_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_580_ = stack[1].m_obj;
lean_object* v_inst_581_ = stack[2].m_obj;
lean_object* v_inst_582_ = stack[3].m_obj;
lean_object* v_inst_583_ = stack[4].m_obj;
lean_object* v_msgData_584_ = stack[5].m_obj;
uint8_t v_severity_585_ = stack[6].m_num;
uint8_t v_isSilent_586_ = stack[7].m_num;
lean_object* v_res_588_;
v_res_588_ = l_Lean_log(lean_box(0), v_inst_580_, v_inst_581_, v_inst_582_, v_inst_583_, v_msgData_584_, v_severity_585_, v_isSilent_586_);
stack->m_obj
 = v_res_588_;
}
LEAN_EXPORT lean_object* l_Lean_log___boxed(lean_object* v_m_589_, lean_object* v_inst_590_, lean_object* v_inst_591_, lean_object* v_inst_592_, lean_object* v_inst_593_, lean_object* v_msgData_594_, lean_object* v_severity_595_, lean_object* v_isSilent_596_){
_start:
{
uint8_t v_severity_boxed_597_; uint8_t v_isSilent_boxed_598_; lean_object* v_res_599_; 
v_severity_boxed_597_ = lean_unbox(v_severity_595_);
v_isSilent_boxed_598_ = lean_unbox(v_isSilent_596_);
v_res_599_ = l_Lean_log(v_m_589_, v_inst_590_, v_inst_591_, v_inst_592_, v_inst_593_, v_msgData_594_, v_severity_boxed_597_, v_isSilent_boxed_598_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___redArg(lean_object* v_inst_600_, lean_object* v_inst_601_, lean_object* v_inst_602_, lean_object* v_inst_603_, lean_object* v_msgData_604_){
_start:
{
uint8_t v___x_605_; uint8_t v___x_606_; lean_object* v___x_607_; 
v___x_605_ = 2;
v___x_606_ = 0;
v___x_607_ = l_Lean_log___redArg(v_inst_600_, v_inst_601_, v_inst_602_, v_inst_603_, v_msgData_604_, v___x_605_, v___x_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError(lean_object* v_m_608_, lean_object* v_inst_609_, lean_object* v_inst_610_, lean_object* v_inst_611_, lean_object* v_inst_612_, lean_object* v_msgData_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Lean_logError___redArg(v_inst_609_, v_inst_610_, v_inst_611_, v_inst_612_, v_msgData_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedError___redArg(lean_object* v_inst_615_, lean_object* v_inst_616_, lean_object* v_inst_617_, lean_object* v_inst_618_, lean_object* v_name_619_, lean_object* v_msgData_620_){
_start:
{
lean_object* v___x_621_; uint8_t v___x_622_; uint8_t v___x_623_; lean_object* v___x_624_; 
v___x_621_ = l_Lean_MessageData_tagWithErrorName(v_msgData_620_, v_name_619_);
v___x_622_ = 2;
v___x_623_ = 0;
v___x_624_ = l_Lean_log___redArg(v_inst_615_, v_inst_616_, v_inst_617_, v_inst_618_, v___x_621_, v___x_622_, v___x_623_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedError(lean_object* v_m_625_, lean_object* v_inst_626_, lean_object* v_inst_627_, lean_object* v_inst_628_, lean_object* v_inst_629_, lean_object* v_name_630_, lean_object* v_msgData_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_Lean_logNamedError___redArg(v_inst_626_, v_inst_627_, v_inst_628_, v_inst_629_, v_name_630_, v_msgData_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___redArg(lean_object* v_inst_633_, lean_object* v_inst_634_, lean_object* v_inst_635_, lean_object* v_inst_636_, lean_object* v_msgData_637_){
_start:
{
uint8_t v___x_638_; uint8_t v___x_639_; lean_object* v___x_640_; 
v___x_638_ = 1;
v___x_639_ = 0;
v___x_640_ = l_Lean_log___redArg(v_inst_633_, v_inst_634_, v_inst_635_, v_inst_636_, v_msgData_637_, v___x_638_, v___x_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning(lean_object* v_m_641_, lean_object* v_inst_642_, lean_object* v_inst_643_, lean_object* v_inst_644_, lean_object* v_inst_645_, lean_object* v_msgData_646_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Lean_logWarning___redArg(v_inst_642_, v_inst_643_, v_inst_644_, v_inst_645_, v_msgData_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedWarning___redArg(lean_object* v_inst_648_, lean_object* v_inst_649_, lean_object* v_inst_650_, lean_object* v_inst_651_, lean_object* v_name_652_, lean_object* v_msgData_653_){
_start:
{
lean_object* v___x_654_; uint8_t v___x_655_; uint8_t v___x_656_; lean_object* v___x_657_; 
v___x_654_ = l_Lean_MessageData_tagWithErrorName(v_msgData_653_, v_name_652_);
v___x_655_ = 1;
v___x_656_ = 0;
v___x_657_ = l_Lean_log___redArg(v_inst_648_, v_inst_649_, v_inst_650_, v_inst_651_, v___x_654_, v___x_655_, v___x_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedWarning(lean_object* v_m_658_, lean_object* v_inst_659_, lean_object* v_inst_660_, lean_object* v_inst_661_, lean_object* v_inst_662_, lean_object* v_name_663_, lean_object* v_msgData_664_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = l_Lean_logNamedWarning___redArg(v_inst_659_, v_inst_660_, v_inst_661_, v_inst_662_, v_name_663_, v_msgData_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___redArg(lean_object* v_inst_666_, lean_object* v_inst_667_, lean_object* v_inst_668_, lean_object* v_inst_669_, lean_object* v_msgData_670_){
_start:
{
uint8_t v___x_671_; uint8_t v___x_672_; lean_object* v___x_673_; 
v___x_671_ = 0;
v___x_672_ = 0;
v___x_673_ = l_Lean_log___redArg(v_inst_666_, v_inst_667_, v_inst_668_, v_inst_669_, v_msgData_670_, v___x_671_, v___x_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo(lean_object* v_m_674_, lean_object* v_inst_675_, lean_object* v_inst_676_, lean_object* v_inst_677_, lean_object* v_inst_678_, lean_object* v_msgData_679_){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = l_Lean_logInfo___redArg(v_inst_675_, v_inst_676_, v_inst_677_, v_inst_678_, v_msgData_679_);
return v___x_680_;
}
}
static lean_object* _init_l_Lean_logUnknownDecl___redArg___closed__1(void){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = ((lean_object*)(l_Lean_logUnknownDecl___redArg___closed__0));
v___x_683_ = l_Lean_stringToMessageData(v___x_682_);
return v___x_683_;
}
}
static lean_object* _init_l_Lean_logUnknownDecl___redArg___closed__3(void){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = ((lean_object*)(l_Lean_logUnknownDecl___redArg___closed__2));
v___x_686_ = l_Lean_stringToMessageData(v___x_685_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_logUnknownDecl___redArg(lean_object* v_inst_687_, lean_object* v_inst_688_, lean_object* v_inst_689_, lean_object* v_inst_690_, lean_object* v_declName_691_){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_692_ = lean_obj_once(&l_Lean_logUnknownDecl___redArg___closed__1, &l_Lean_logUnknownDecl___redArg___closed__1_once, _init_l_Lean_logUnknownDecl___redArg___closed__1);
v___x_693_ = l_Lean_MessageData_ofName(v_declName_691_);
v___x_694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_694_, 0, v___x_692_);
lean_ctor_set(v___x_694_, 1, v___x_693_);
v___x_695_ = lean_obj_once(&l_Lean_logUnknownDecl___redArg___closed__3, &l_Lean_logUnknownDecl___redArg___closed__3_once, _init_l_Lean_logUnknownDecl___redArg___closed__3);
v___x_696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_694_);
lean_ctor_set(v___x_696_, 1, v___x_695_);
v___x_697_ = l_Lean_logError___redArg(v_inst_687_, v_inst_688_, v_inst_689_, v_inst_690_, v___x_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_logUnknownDecl(lean_object* v_m_698_, lean_object* v_inst_699_, lean_object* v_inst_700_, lean_object* v_inst_701_, lean_object* v_inst_702_, lean_object* v_declName_703_){
_start:
{
lean_object* v___x_704_; 
v___x_704_ = l_Lean_logUnknownDecl___redArg(v_inst_699_, v_inst_700_, v_inst_701_, v_inst_702_, v_declName_703_);
return v___x_704_;
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
