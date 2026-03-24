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
extern lean_object* l_Lean_KVMap_instValueBool;
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_initFn___closed__0_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "warningAsError"};
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__1_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(67, 210, 29, 118, 39, 158, 180, 72)}};
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__2_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "treat warnings as errors"};
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__3_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__4_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_initFn___closed__4_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__5_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__5_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(82, 127, 119, 5, 244, 162, 222, 133)}};
static const lean_object* l_Lean_initFn___closed__5_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4____boxed(lean_object*);
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
static const lean_ctor_object l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__4(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc(v_inst_6_);
v___f_16_ = lean_alloc_closure((void*)(l_Lean_instMonadLogOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_16_, 0, v_logMessage_12_);
lean_closure_set(v___f_16_, 1, v_inst_6_);
lean_inc(v_inst_6_);
v___x_17_ = lean_apply_2(v_inst_6_, lean_box(0), v_toMonadFileMap_8_);
lean_inc(v_inst_6_);
v___x_18_ = lean_apply_2(v_inst_6_, lean_box(0), v_getRef_9_);
lean_inc(v_inst_6_);
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
lean_dec_ref(v___x_33_);
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
lean_inc(v_toBind_73_);
v_toMonadFileMap_74_ = lean_ctor_get(v_inst_71_, 0);
lean_inc(v_toMonadFileMap_74_);
v_toPure_75_ = lean_ctor_get(v_toApplicative_72_, 1);
lean_inc(v_toPure_75_);
lean_inc(v_toBind_73_);
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__spec__0(lean_object* v_name_82_, lean_object* v_decl_83_, lean_object* v_ref_84_){
_start:
{
lean_object* v_defValue_86_; lean_object* v_descr_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_114_; 
v_defValue_86_ = lean_ctor_get(v_decl_83_, 0);
v_descr_87_ = lean_ctor_get(v_decl_83_, 1);
v_isSharedCheck_114_ = !lean_is_exclusive(v_decl_83_);
if (v_isSharedCheck_114_ == 0)
{
v___x_89_ = v_decl_83_;
v_isShared_90_ = v_isSharedCheck_114_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_descr_87_);
lean_inc(v_defValue_86_);
lean_dec(v_decl_83_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_114_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_91_; uint8_t v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_91_ = lean_alloc_ctor(1, 0, 1);
v___x_92_ = lean_unbox(v_defValue_86_);
lean_ctor_set_uint8(v___x_91_, 0, v___x_92_);
lean_inc(v_name_82_);
v___x_93_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_93_, 0, v_name_82_);
lean_ctor_set(v___x_93_, 1, v_ref_84_);
lean_ctor_set(v___x_93_, 2, v___x_91_);
lean_ctor_set(v___x_93_, 3, v_descr_87_);
lean_inc(v_name_82_);
v___x_94_ = lean_register_option(v_name_82_, v___x_93_);
if (lean_obj_tag(v___x_94_) == 0)
{
lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_104_; 
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_104_ == 0)
{
lean_object* v_unused_105_; 
v_unused_105_ = lean_ctor_get(v___x_94_, 0);
lean_dec(v_unused_105_);
v___x_96_ = v___x_94_;
v_isShared_97_ = v_isSharedCheck_104_;
goto v_resetjp_95_;
}
else
{
lean_dec(v___x_94_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_104_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_99_; 
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 1, v_defValue_86_);
lean_ctor_set(v___x_89_, 0, v_name_82_);
v___x_99_ = v___x_89_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_name_82_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v_defValue_86_);
v___x_99_ = v_reuseFailAlloc_103_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
lean_object* v___x_101_; 
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 0, v___x_99_);
v___x_101_ = v___x_96_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v___x_99_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
}
}
else
{
lean_object* v_a_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_113_; 
lean_del_object(v___x_89_);
lean_dec(v_defValue_86_);
lean_dec(v_name_82_);
v_a_106_ = lean_ctor_get(v___x_94_, 0);
v_isSharedCheck_113_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_113_ == 0)
{
v___x_108_ = v___x_94_;
v_isShared_109_ = v_isSharedCheck_113_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_a_106_);
lean_dec(v___x_94_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_113_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_111_; 
if (v_isShared_109_ == 0)
{
v___x_111_ = v___x_108_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_a_106_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_115_, lean_object* v_decl_116_, lean_object* v_ref_117_, lean_object* v_a_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__spec__0(v_name_115_, v_decl_116_, v_ref_117_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_133_ = ((lean_object*)(l_Lean_initFn___closed__1_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_));
v___x_134_ = ((lean_object*)(l_Lean_initFn___closed__3_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_));
v___x_135_ = ((lean_object*)(l_Lean_initFn___closed__5_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_));
v___x_136_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__spec__0(v___x_133_, v___x_134_, v___x_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4____boxed(lean_object* v_a_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_();
return v_res_138_;
}
}
static uint64_t _init_l_Lean_errorDescriptionWidget___closed__1(void){
_start:
{
lean_object* v___x_140_; uint64_t v___x_141_; 
v___x_140_ = ((lean_object*)(l_Lean_errorDescriptionWidget___closed__0));
v___x_141_ = lean_string_hash(v___x_140_);
return v___x_141_;
}
}
static lean_object* _init_l_Lean_errorDescriptionWidget___closed__2(void){
_start:
{
uint64_t v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_142_ = lean_uint64_once(&l_Lean_errorDescriptionWidget___closed__1, &l_Lean_errorDescriptionWidget___closed__1_once, _init_l_Lean_errorDescriptionWidget___closed__1);
v___x_143_ = ((lean_object*)(l_Lean_errorDescriptionWidget___closed__0));
v___x_144_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_144_, 0, v___x_143_);
lean_ctor_set_uint64(v___x_144_, sizeof(void*)*1, v___x_142_);
return v___x_144_;
}
}
static lean_object* _init_l_Lean_errorDescriptionWidget(void){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = lean_obj_once(&l_Lean_errorDescriptionWidget___closed__2, &l_Lean_errorDescriptionWidget___closed__2_once, _init_l_Lean_errorDescriptionWidget___closed__2);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___lam__0(lean_object* v___x_146_, lean_object* v___y_147_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_148_, 0, v___x_146_);
lean_ctor_set(v___x_148_, 1, v___y_147_);
return v___x_148_;
}
}
static lean_object* _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__1(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_150_ = l_Lean_errorExplanationManualDomain;
v___x_151_ = ((lean_object*)(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__0));
v___x_152_ = lean_string_append(v___x_151_, v___x_150_);
return v___x_152_;
}
}
static lean_object* _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__3(void){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_154_ = ((lean_object*)(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__2));
v___x_155_ = lean_obj_once(&l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__1, &l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__1_once, _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__1);
v___x_156_ = lean_string_append(v___x_155_, v___x_154_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object* v_msg_163_){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; 
lean_inc_ref(v_msg_163_);
v___x_164_ = l_Lean_MessageData_stripNestedTags(v_msg_163_);
v___x_165_ = l_Lean_MessageData_errorName_x3f(v___x_164_);
lean_dec_ref(v___x_164_);
if (lean_obj_tag(v___x_165_) == 0)
{
return v_msg_163_;
}
else
{
lean_object* v_val_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_196_; 
v_val_166_ = lean_ctor_get(v___x_165_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v___x_165_);
if (v_isSharedCheck_196_ == 0)
{
v___x_168_ = v___x_165_;
v_isShared_169_ = v_isSharedCheck_196_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_val_166_);
lean_dec(v___x_165_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_196_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v___x_170_; uint64_t v_javascriptHash_171_; lean_object* v___x_172_; lean_object* v___x_173_; uint8_t v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v_url_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_181_; 
v___x_170_ = l_Lean_errorDescriptionWidget;
v_javascriptHash_171_ = lean_ctor_get_uint64(v___x_170_, sizeof(void*)*1);
v___x_172_ = l_Lean_manualRoot;
v___x_173_ = lean_obj_once(&l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__3, &l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__3_once, _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__3);
v___x_174_ = 1;
v___x_175_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_166_, v___x_174_);
v___x_176_ = lean_string_append(v___x_173_, v___x_175_);
v_url_177_ = lean_string_append(v___x_172_, v___x_176_);
lean_dec_ref(v___x_176_);
v___x_178_ = ((lean_object*)(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__5));
v___x_179_ = ((lean_object*)(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__6));
if (v_isShared_169_ == 0)
{
lean_ctor_set_tag(v___x_168_, 3);
lean_ctor_set(v___x_168_, 0, v___x_175_);
v___x_181_ = v___x_168_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v___x_175_);
v___x_181_ = v_reuseFailAlloc_195_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___f_190_; lean_object* v_inst_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_179_);
lean_ctor_set(v___x_182_, 1, v___x_181_);
v___x_183_ = ((lean_object*)(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__7));
v___x_184_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_184_, 0, v_url_177_);
v___x_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_183_);
lean_ctor_set(v___x_185_, 1, v___x_184_);
v___x_186_ = lean_box(0);
v___x_187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_185_);
lean_ctor_set(v___x_187_, 1, v___x_186_);
v___x_188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_188_, 0, v___x_182_);
lean_ctor_set(v___x_188_, 1, v___x_187_);
v___x_189_ = l_Lean_Json_mkObj(v___x_188_);
v___f_190_ = lean_alloc_closure((void*)(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___lam__0), 2, 1);
lean_closure_set(v___f_190_, 0, v___x_189_);
v_inst_191_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v_inst_191_, 0, v___x_178_);
lean_ctor_set(v_inst_191_, 1, v___f_190_);
lean_ctor_set_uint64(v_inst_191_, sizeof(void*)*2, v_javascriptHash_171_);
v___x_192_ = l_Lean_MessageData_nil;
v___x_193_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_193_, 0, v_inst_191_);
lean_ctor_set(v___x_193_, 1, v___x_192_);
v___x_194_ = l_Lean_MessageData_composePreservingKind(v_msg_163_, v___x_193_);
return v___x_194_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__0(lean_object* v_fileMap_198_, lean_object* v___y_199_, lean_object* v___y_200_, uint8_t v___y_201_, uint8_t v___y_202_, uint8_t v_isSilent_203_, lean_object* v_msgData_204_, lean_object* v_logMessage_205_, lean_object* v_____do__lift_206_){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
lean_inc_ref(v_fileMap_198_);
v___x_207_ = l_Lean_FileMap_toPosition(v_fileMap_198_, v___y_199_);
v___x_208_ = l_Lean_FileMap_toPosition(v_fileMap_198_, v___y_200_);
v___x_209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_209_, 0, v___x_208_);
v___x_210_ = ((lean_object*)(l_Lean_logAt___redArg___lam__0___closed__0));
v___x_211_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_211_, 0, v_____do__lift_206_);
lean_ctor_set(v___x_211_, 1, v___x_207_);
lean_ctor_set(v___x_211_, 2, v___x_209_);
lean_ctor_set(v___x_211_, 3, v___x_210_);
lean_ctor_set(v___x_211_, 4, v_msgData_204_);
lean_ctor_set_uint8(v___x_211_, sizeof(void*)*5, v___y_201_);
lean_ctor_set_uint8(v___x_211_, sizeof(void*)*5 + 1, v___y_202_);
lean_ctor_set_uint8(v___x_211_, sizeof(void*)*5 + 2, v_isSilent_203_);
v___x_212_ = lean_apply_1(v_logMessage_205_, v___x_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__0___boxed(lean_object* v_fileMap_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v_isSilent_218_, lean_object* v_msgData_219_, lean_object* v_logMessage_220_, lean_object* v_____do__lift_221_){
_start:
{
uint8_t v___y_374__boxed_222_; uint8_t v___y_375__boxed_223_; uint8_t v_isSilent_boxed_224_; lean_object* v_res_225_; 
v___y_374__boxed_222_ = lean_unbox(v___y_216_);
v___y_375__boxed_223_ = lean_unbox(v___y_217_);
v_isSilent_boxed_224_ = lean_unbox(v_isSilent_218_);
v_res_225_ = l_Lean_logAt___redArg___lam__0(v_fileMap_213_, v___y_214_, v___y_215_, v___y_374__boxed_222_, v___y_375__boxed_223_, v_isSilent_boxed_224_, v_msgData_219_, v_logMessage_220_, v_____do__lift_221_);
lean_dec(v___y_215_);
lean_dec(v___y_214_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__1(lean_object* v_fileMap_226_, lean_object* v___y_227_, lean_object* v___y_228_, uint8_t v___y_229_, uint8_t v___y_230_, uint8_t v_isSilent_231_, lean_object* v_logMessage_232_, lean_object* v_toBind_233_, lean_object* v_getFileName_234_, lean_object* v_msgData_235_){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___f_239_; lean_object* v___x_240_; 
v___x_236_ = lean_box(v___y_229_);
v___x_237_ = lean_box(v___y_230_);
v___x_238_ = lean_box(v_isSilent_231_);
v___f_239_ = lean_alloc_closure((void*)(l_Lean_logAt___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_239_, 0, v_fileMap_226_);
lean_closure_set(v___f_239_, 1, v___y_227_);
lean_closure_set(v___f_239_, 2, v___y_228_);
lean_closure_set(v___f_239_, 3, v___x_236_);
lean_closure_set(v___f_239_, 4, v___x_237_);
lean_closure_set(v___f_239_, 5, v___x_238_);
lean_closure_set(v___f_239_, 6, v_msgData_235_);
lean_closure_set(v___f_239_, 7, v_logMessage_232_);
v___x_240_ = lean_apply_4(v_toBind_233_, lean_box(0), lean_box(0), v_getFileName_234_, v___f_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__1___boxed(lean_object* v_fileMap_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v_isSilent_246_, lean_object* v_logMessage_247_, lean_object* v_toBind_248_, lean_object* v_getFileName_249_, lean_object* v_msgData_250_){
_start:
{
uint8_t v___y_402__boxed_251_; uint8_t v___y_403__boxed_252_; uint8_t v_isSilent_boxed_253_; lean_object* v_res_254_; 
v___y_402__boxed_251_ = lean_unbox(v___y_244_);
v___y_403__boxed_252_ = lean_unbox(v___y_245_);
v_isSilent_boxed_253_ = lean_unbox(v_isSilent_246_);
v_res_254_ = l_Lean_logAt___redArg___lam__1(v_fileMap_241_, v___y_242_, v___y_243_, v___y_402__boxed_251_, v___y_403__boxed_252_, v_isSilent_boxed_253_, v_logMessage_247_, v_toBind_248_, v_getFileName_249_, v_msgData_250_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__2(lean_object* v___y_255_, lean_object* v___y_256_, uint8_t v___y_257_, uint8_t v___y_258_, uint8_t v_isSilent_259_, lean_object* v_logMessage_260_, lean_object* v_toBind_261_, lean_object* v_getFileName_262_, lean_object* v_msgData_263_, lean_object* v_inst_264_, lean_object* v_fileMap_265_){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___f_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_266_ = lean_box(v___y_257_);
v___x_267_ = lean_box(v___y_258_);
v___x_268_ = lean_box(v_isSilent_259_);
lean_inc(v_toBind_261_);
v___f_269_ = lean_alloc_closure((void*)(l_Lean_logAt___redArg___lam__1___boxed), 10, 9);
lean_closure_set(v___f_269_, 0, v_fileMap_265_);
lean_closure_set(v___f_269_, 1, v___y_255_);
lean_closure_set(v___f_269_, 2, v___y_256_);
lean_closure_set(v___f_269_, 3, v___x_266_);
lean_closure_set(v___f_269_, 4, v___x_267_);
lean_closure_set(v___f_269_, 5, v___x_268_);
lean_closure_set(v___f_269_, 6, v_logMessage_260_);
lean_closure_set(v___f_269_, 7, v_toBind_261_);
lean_closure_set(v___f_269_, 8, v_getFileName_262_);
v___x_270_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_263_);
v___x_271_ = lean_apply_1(v_inst_264_, v___x_270_);
v___x_272_ = lean_apply_4(v_toBind_261_, lean_box(0), lean_box(0), v___x_271_, v___f_269_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__2___boxed(lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v_isSilent_277_, lean_object* v_logMessage_278_, lean_object* v_toBind_279_, lean_object* v_getFileName_280_, lean_object* v_msgData_281_, lean_object* v_inst_282_, lean_object* v_fileMap_283_){
_start:
{
uint8_t v___y_424__boxed_284_; uint8_t v___y_425__boxed_285_; uint8_t v_isSilent_boxed_286_; lean_object* v_res_287_; 
v___y_424__boxed_284_ = lean_unbox(v___y_275_);
v___y_425__boxed_285_ = lean_unbox(v___y_276_);
v_isSilent_boxed_286_ = lean_unbox(v_isSilent_277_);
v_res_287_ = l_Lean_logAt___redArg___lam__2(v___y_273_, v___y_274_, v___y_424__boxed_284_, v___y_425__boxed_285_, v_isSilent_boxed_286_, v_logMessage_278_, v_toBind_279_, v_getFileName_280_, v_msgData_281_, v_inst_282_, v_fileMap_283_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__3(lean_object* v_ref_288_, uint8_t v___y_289_, uint8_t v___y_290_, uint8_t v_isSilent_291_, lean_object* v_logMessage_292_, lean_object* v_toBind_293_, lean_object* v_getFileName_294_, lean_object* v_msgData_295_, lean_object* v_inst_296_, lean_object* v_toMonadFileMap_297_, lean_object* v_____do__lift_298_){
_start:
{
lean_object* v___y_300_; lean_object* v___y_301_; lean_object* v_ref_307_; lean_object* v___y_309_; lean_object* v___x_312_; 
v_ref_307_ = l_Lean_replaceRef(v_ref_288_, v_____do__lift_298_);
v___x_312_ = l_Lean_Syntax_getPos_x3f(v_ref_307_, v___y_289_);
if (lean_obj_tag(v___x_312_) == 0)
{
lean_object* v___x_313_; 
v___x_313_ = lean_unsigned_to_nat(0u);
v___y_309_ = v___x_313_;
goto v___jp_308_;
}
else
{
lean_object* v_val_314_; 
v_val_314_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_val_314_);
lean_dec_ref(v___x_312_);
v___y_309_ = v_val_314_;
goto v___jp_308_;
}
v___jp_299_:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___f_305_; lean_object* v___x_306_; 
v___x_302_ = lean_box(v___y_289_);
v___x_303_ = lean_box(v___y_290_);
v___x_304_ = lean_box(v_isSilent_291_);
lean_inc(v_toBind_293_);
v___f_305_ = lean_alloc_closure((void*)(l_Lean_logAt___redArg___lam__2___boxed), 11, 10);
lean_closure_set(v___f_305_, 0, v___y_300_);
lean_closure_set(v___f_305_, 1, v___y_301_);
lean_closure_set(v___f_305_, 2, v___x_302_);
lean_closure_set(v___f_305_, 3, v___x_303_);
lean_closure_set(v___f_305_, 4, v___x_304_);
lean_closure_set(v___f_305_, 5, v_logMessage_292_);
lean_closure_set(v___f_305_, 6, v_toBind_293_);
lean_closure_set(v___f_305_, 7, v_getFileName_294_);
lean_closure_set(v___f_305_, 8, v_msgData_295_);
lean_closure_set(v___f_305_, 9, v_inst_296_);
v___x_306_ = lean_apply_4(v_toBind_293_, lean_box(0), lean_box(0), v_toMonadFileMap_297_, v___f_305_);
return v___x_306_;
}
v___jp_308_:
{
lean_object* v___x_310_; 
v___x_310_ = l_Lean_Syntax_getTailPos_x3f(v_ref_307_, v___y_289_);
lean_dec(v_ref_307_);
if (lean_obj_tag(v___x_310_) == 0)
{
lean_inc(v___y_309_);
v___y_300_ = v___y_309_;
v___y_301_ = v___y_309_;
goto v___jp_299_;
}
else
{
lean_object* v_val_311_; 
v_val_311_ = lean_ctor_get(v___x_310_, 0);
lean_inc(v_val_311_);
lean_dec_ref(v___x_310_);
v___y_300_ = v___y_309_;
v___y_301_ = v_val_311_;
goto v___jp_299_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__3___boxed(lean_object* v_ref_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v_isSilent_318_, lean_object* v_logMessage_319_, lean_object* v_toBind_320_, lean_object* v_getFileName_321_, lean_object* v_msgData_322_, lean_object* v_inst_323_, lean_object* v_toMonadFileMap_324_, lean_object* v_____do__lift_325_){
_start:
{
uint8_t v___y_452__boxed_326_; uint8_t v___y_453__boxed_327_; uint8_t v_isSilent_boxed_328_; lean_object* v_res_329_; 
v___y_452__boxed_326_ = lean_unbox(v___y_316_);
v___y_453__boxed_327_ = lean_unbox(v___y_317_);
v_isSilent_boxed_328_ = lean_unbox(v_isSilent_318_);
v_res_329_ = l_Lean_logAt___redArg___lam__3(v_ref_315_, v___y_452__boxed_326_, v___y_453__boxed_327_, v_isSilent_boxed_328_, v_logMessage_319_, v_toBind_320_, v_getFileName_321_, v_msgData_322_, v_inst_323_, v_toMonadFileMap_324_, v_____do__lift_325_);
lean_dec(v_____do__lift_325_);
lean_dec(v_ref_315_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__4(lean_object* v_inst_330_, lean_object* v_ref_331_, uint8_t v___y_332_, uint8_t v_isSilent_333_, lean_object* v_toBind_334_, lean_object* v_msgData_335_, lean_object* v_inst_336_, uint8_t v_severity_337_, uint8_t v___x_338_, lean_object* v_____do__lift_339_){
_start:
{
uint8_t v___y_341_; uint8_t v___y_352_; uint8_t v___x_353_; uint8_t v___x_354_; 
v___x_353_ = 1;
v___x_354_ = l_Lean_instBEqMessageSeverity_beq(v_severity_337_, v___x_353_);
if (v___x_354_ == 0)
{
v___y_352_ = v___x_354_;
goto v___jp_351_;
}
else
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; uint8_t v___x_358_; 
v___x_355_ = l_Lean_KVMap_instValueBool;
v___x_356_ = l_Lean_warningAsError;
v___x_357_ = l_Lean_Option_get___redArg(v___x_355_, v_____do__lift_339_, v___x_356_);
v___x_358_ = lean_unbox(v___x_357_);
lean_dec(v___x_357_);
v___y_352_ = v___x_358_;
goto v___jp_351_;
}
v___jp_340_:
{
lean_object* v_toMonadFileMap_342_; lean_object* v_getRef_343_; lean_object* v_getFileName_344_; lean_object* v_logMessage_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___f_349_; lean_object* v___x_350_; 
v_toMonadFileMap_342_ = lean_ctor_get(v_inst_330_, 0);
lean_inc(v_toMonadFileMap_342_);
v_getRef_343_ = lean_ctor_get(v_inst_330_, 1);
lean_inc(v_getRef_343_);
v_getFileName_344_ = lean_ctor_get(v_inst_330_, 2);
lean_inc(v_getFileName_344_);
v_logMessage_345_ = lean_ctor_get(v_inst_330_, 4);
lean_inc(v_logMessage_345_);
lean_dec_ref(v_inst_330_);
v___x_346_ = lean_box(v___y_332_);
v___x_347_ = lean_box(v___y_341_);
v___x_348_ = lean_box(v_isSilent_333_);
lean_inc(v_toBind_334_);
v___f_349_ = lean_alloc_closure((void*)(l_Lean_logAt___redArg___lam__3___boxed), 11, 10);
lean_closure_set(v___f_349_, 0, v_ref_331_);
lean_closure_set(v___f_349_, 1, v___x_346_);
lean_closure_set(v___f_349_, 2, v___x_347_);
lean_closure_set(v___f_349_, 3, v___x_348_);
lean_closure_set(v___f_349_, 4, v_logMessage_345_);
lean_closure_set(v___f_349_, 5, v_toBind_334_);
lean_closure_set(v___f_349_, 6, v_getFileName_344_);
lean_closure_set(v___f_349_, 7, v_msgData_335_);
lean_closure_set(v___f_349_, 8, v_inst_336_);
lean_closure_set(v___f_349_, 9, v_toMonadFileMap_342_);
v___x_350_ = lean_apply_4(v_toBind_334_, lean_box(0), lean_box(0), v_getRef_343_, v___f_349_);
return v___x_350_;
}
v___jp_351_:
{
if (v___y_352_ == 0)
{
v___y_341_ = v_severity_337_;
goto v___jp_340_;
}
else
{
v___y_341_ = v___x_338_;
goto v___jp_340_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__4___boxed(lean_object* v_inst_359_, lean_object* v_ref_360_, lean_object* v___y_361_, lean_object* v_isSilent_362_, lean_object* v_toBind_363_, lean_object* v_msgData_364_, lean_object* v_inst_365_, lean_object* v_severity_366_, lean_object* v___x_367_, lean_object* v_____do__lift_368_){
_start:
{
uint8_t v___y_495__boxed_369_; uint8_t v_isSilent_boxed_370_; uint8_t v_severity_boxed_371_; uint8_t v___x_497__boxed_372_; lean_object* v_res_373_; 
v___y_495__boxed_369_ = lean_unbox(v___y_361_);
v_isSilent_boxed_370_ = lean_unbox(v_isSilent_362_);
v_severity_boxed_371_ = lean_unbox(v_severity_366_);
v___x_497__boxed_372_ = lean_unbox(v___x_367_);
v_res_373_ = l_Lean_logAt___redArg___lam__4(v_inst_359_, v_ref_360_, v___y_495__boxed_369_, v_isSilent_boxed_370_, v_toBind_363_, v_msgData_364_, v_inst_365_, v_severity_boxed_371_, v___x_497__boxed_372_, v_____do__lift_368_);
lean_dec_ref(v_____do__lift_368_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg(lean_object* v_inst_374_, lean_object* v_inst_375_, lean_object* v_inst_376_, lean_object* v_inst_377_, lean_object* v_ref_378_, lean_object* v_msgData_379_, uint8_t v_severity_380_, uint8_t v_isSilent_381_){
_start:
{
uint8_t v___x_382_; uint8_t v___y_384_; uint8_t v___x_396_; 
v___x_382_ = 2;
v___x_396_ = l_Lean_instBEqMessageSeverity_beq(v_severity_380_, v___x_382_);
if (v___x_396_ == 0)
{
v___y_384_ = v___x_396_;
goto v___jp_383_;
}
else
{
uint8_t v___x_397_; 
lean_inc_ref(v_msgData_379_);
v___x_397_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_379_);
v___y_384_ = v___x_397_;
goto v___jp_383_;
}
v___jp_383_:
{
if (v___y_384_ == 0)
{
lean_object* v_toBind_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___f_390_; lean_object* v___x_391_; 
v_toBind_385_ = lean_ctor_get(v_inst_374_, 1);
lean_inc(v_toBind_385_);
lean_dec_ref(v_inst_374_);
v___x_386_ = lean_box(v___y_384_);
v___x_387_ = lean_box(v_isSilent_381_);
v___x_388_ = lean_box(v_severity_380_);
v___x_389_ = lean_box(v___x_382_);
lean_inc(v_toBind_385_);
v___f_390_ = lean_alloc_closure((void*)(l_Lean_logAt___redArg___lam__4___boxed), 10, 9);
lean_closure_set(v___f_390_, 0, v_inst_375_);
lean_closure_set(v___f_390_, 1, v_ref_378_);
lean_closure_set(v___f_390_, 2, v___x_386_);
lean_closure_set(v___f_390_, 3, v___x_387_);
lean_closure_set(v___f_390_, 4, v_toBind_385_);
lean_closure_set(v___f_390_, 5, v_msgData_379_);
lean_closure_set(v___f_390_, 6, v_inst_376_);
lean_closure_set(v___f_390_, 7, v___x_388_);
lean_closure_set(v___f_390_, 8, v___x_389_);
v___x_391_ = lean_apply_4(v_toBind_385_, lean_box(0), lean_box(0), v_inst_377_, v___f_390_);
return v___x_391_;
}
else
{
lean_object* v_toApplicative_392_; lean_object* v_toPure_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
lean_dec_ref(v_msgData_379_);
lean_dec(v_ref_378_);
lean_dec(v_inst_377_);
lean_dec(v_inst_376_);
lean_dec_ref(v_inst_375_);
v_toApplicative_392_ = lean_ctor_get(v_inst_374_, 0);
lean_inc_ref(v_toApplicative_392_);
lean_dec_ref(v_inst_374_);
v_toPure_393_ = lean_ctor_get(v_toApplicative_392_, 1);
lean_inc(v_toPure_393_);
lean_dec_ref(v_toApplicative_392_);
v___x_394_ = lean_box(0);
v___x_395_ = lean_apply_2(v_toPure_393_, lean_box(0), v___x_394_);
return v___x_395_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___boxed(lean_object* v_inst_398_, lean_object* v_inst_399_, lean_object* v_inst_400_, lean_object* v_inst_401_, lean_object* v_ref_402_, lean_object* v_msgData_403_, lean_object* v_severity_404_, lean_object* v_isSilent_405_){
_start:
{
uint8_t v_severity_boxed_406_; uint8_t v_isSilent_boxed_407_; lean_object* v_res_408_; 
v_severity_boxed_406_ = lean_unbox(v_severity_404_);
v_isSilent_boxed_407_ = lean_unbox(v_isSilent_405_);
v_res_408_ = l_Lean_logAt___redArg(v_inst_398_, v_inst_399_, v_inst_400_, v_inst_401_, v_ref_402_, v_msgData_403_, v_severity_boxed_406_, v_isSilent_boxed_407_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt(lean_object* v_m_409_, lean_object* v_inst_410_, lean_object* v_inst_411_, lean_object* v_inst_412_, lean_object* v_inst_413_, lean_object* v_ref_414_, lean_object* v_msgData_415_, uint8_t v_severity_416_, uint8_t v_isSilent_417_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_logAt___redArg(v_inst_410_, v_inst_411_, v_inst_412_, v_inst_413_, v_ref_414_, v_msgData_415_, v_severity_416_, v_isSilent_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___boxed(lean_object* v_m_419_, lean_object* v_inst_420_, lean_object* v_inst_421_, lean_object* v_inst_422_, lean_object* v_inst_423_, lean_object* v_ref_424_, lean_object* v_msgData_425_, lean_object* v_severity_426_, lean_object* v_isSilent_427_){
_start:
{
uint8_t v_severity_boxed_428_; uint8_t v_isSilent_boxed_429_; lean_object* v_res_430_; 
v_severity_boxed_428_ = lean_unbox(v_severity_426_);
v_isSilent_boxed_429_ = lean_unbox(v_isSilent_427_);
v_res_430_ = l_Lean_logAt(v_m_419_, v_inst_420_, v_inst_421_, v_inst_422_, v_inst_423_, v_ref_424_, v_msgData_425_, v_severity_boxed_428_, v_isSilent_boxed_429_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___redArg(lean_object* v_inst_431_, lean_object* v_inst_432_, lean_object* v_inst_433_, lean_object* v_inst_434_, lean_object* v_ref_435_, lean_object* v_msgData_436_){
_start:
{
uint8_t v___x_437_; uint8_t v___x_438_; lean_object* v___x_439_; 
v___x_437_ = 2;
v___x_438_ = 0;
v___x_439_ = l_Lean_logAt___redArg(v_inst_431_, v_inst_432_, v_inst_433_, v_inst_434_, v_ref_435_, v_msgData_436_, v___x_437_, v___x_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt(lean_object* v_m_440_, lean_object* v_inst_441_, lean_object* v_inst_442_, lean_object* v_inst_443_, lean_object* v_inst_444_, lean_object* v_ref_445_, lean_object* v_msgData_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_logErrorAt___redArg(v_inst_441_, v_inst_442_, v_inst_443_, v_inst_444_, v_ref_445_, v_msgData_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedErrorAt___redArg(lean_object* v_inst_448_, lean_object* v_inst_449_, lean_object* v_inst_450_, lean_object* v_inst_451_, lean_object* v_ref_452_, lean_object* v_name_453_, lean_object* v_msgData_454_){
_start:
{
lean_object* v___x_455_; uint8_t v___x_456_; uint8_t v___x_457_; lean_object* v___x_458_; 
v___x_455_ = l_Lean_MessageData_tagWithErrorName(v_msgData_454_, v_name_453_);
v___x_456_ = 2;
v___x_457_ = 0;
v___x_458_ = l_Lean_logAt___redArg(v_inst_448_, v_inst_449_, v_inst_450_, v_inst_451_, v_ref_452_, v___x_455_, v___x_456_, v___x_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedErrorAt(lean_object* v_m_459_, lean_object* v_inst_460_, lean_object* v_inst_461_, lean_object* v_inst_462_, lean_object* v_inst_463_, lean_object* v_ref_464_, lean_object* v_name_465_, lean_object* v_msgData_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_Lean_logNamedErrorAt___redArg(v_inst_460_, v_inst_461_, v_inst_462_, v_inst_463_, v_ref_464_, v_name_465_, v_msgData_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___redArg(lean_object* v_inst_468_, lean_object* v_inst_469_, lean_object* v_inst_470_, lean_object* v_inst_471_, lean_object* v_ref_472_, lean_object* v_msgData_473_){
_start:
{
uint8_t v___x_474_; uint8_t v___x_475_; lean_object* v___x_476_; 
v___x_474_ = 1;
v___x_475_ = 0;
v___x_476_ = l_Lean_logAt___redArg(v_inst_468_, v_inst_469_, v_inst_470_, v_inst_471_, v_ref_472_, v_msgData_473_, v___x_474_, v___x_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt(lean_object* v_m_477_, lean_object* v_inst_478_, lean_object* v_inst_479_, lean_object* v_inst_480_, lean_object* v_inst_481_, lean_object* v_ref_482_, lean_object* v_msgData_483_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Lean_logWarningAt___redArg(v_inst_478_, v_inst_479_, v_inst_480_, v_inst_481_, v_ref_482_, v_msgData_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedWarningAt___redArg(lean_object* v_inst_485_, lean_object* v_inst_486_, lean_object* v_inst_487_, lean_object* v_inst_488_, lean_object* v_ref_489_, lean_object* v_name_490_, lean_object* v_msgData_491_){
_start:
{
lean_object* v___x_492_; uint8_t v___x_493_; uint8_t v___x_494_; lean_object* v___x_495_; 
v___x_492_ = l_Lean_MessageData_tagWithErrorName(v_msgData_491_, v_name_490_);
v___x_493_ = 1;
v___x_494_ = 0;
v___x_495_ = l_Lean_logAt___redArg(v_inst_485_, v_inst_486_, v_inst_487_, v_inst_488_, v_ref_489_, v___x_492_, v___x_493_, v___x_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedWarningAt(lean_object* v_m_496_, lean_object* v_inst_497_, lean_object* v_inst_498_, lean_object* v_inst_499_, lean_object* v_inst_500_, lean_object* v_ref_501_, lean_object* v_name_502_, lean_object* v_msgData_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Lean_logNamedWarningAt___redArg(v_inst_497_, v_inst_498_, v_inst_499_, v_inst_500_, v_ref_501_, v_name_502_, v_msgData_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___redArg(lean_object* v_inst_505_, lean_object* v_inst_506_, lean_object* v_inst_507_, lean_object* v_inst_508_, lean_object* v_ref_509_, lean_object* v_msgData_510_){
_start:
{
uint8_t v___x_511_; uint8_t v___x_512_; lean_object* v___x_513_; 
v___x_511_ = 0;
v___x_512_ = 0;
v___x_513_ = l_Lean_logAt___redArg(v_inst_505_, v_inst_506_, v_inst_507_, v_inst_508_, v_ref_509_, v_msgData_510_, v___x_511_, v___x_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt(lean_object* v_m_514_, lean_object* v_inst_515_, lean_object* v_inst_516_, lean_object* v_inst_517_, lean_object* v_inst_518_, lean_object* v_ref_519_, lean_object* v_msgData_520_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = l_Lean_logInfoAt___redArg(v_inst_515_, v_inst_516_, v_inst_517_, v_inst_518_, v_ref_519_, v_msgData_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___redArg___lam__0(lean_object* v_inst_522_, lean_object* v_inst_523_, lean_object* v_inst_524_, lean_object* v_inst_525_, lean_object* v_msgData_526_, uint8_t v_severity_527_, uint8_t v_isSilent_528_, lean_object* v_ref_529_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l_Lean_logAt___redArg(v_inst_522_, v_inst_523_, v_inst_524_, v_inst_525_, v_ref_529_, v_msgData_526_, v_severity_527_, v_isSilent_528_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___redArg___lam__0___boxed(lean_object* v_inst_531_, lean_object* v_inst_532_, lean_object* v_inst_533_, lean_object* v_inst_534_, lean_object* v_msgData_535_, lean_object* v_severity_536_, lean_object* v_isSilent_537_, lean_object* v_ref_538_){
_start:
{
uint8_t v_severity_boxed_539_; uint8_t v_isSilent_boxed_540_; lean_object* v_res_541_; 
v_severity_boxed_539_ = lean_unbox(v_severity_536_);
v_isSilent_boxed_540_ = lean_unbox(v_isSilent_537_);
v_res_541_ = l_Lean_log___redArg___lam__0(v_inst_531_, v_inst_532_, v_inst_533_, v_inst_534_, v_msgData_535_, v_severity_boxed_539_, v_isSilent_boxed_540_, v_ref_538_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___redArg(lean_object* v_inst_542_, lean_object* v_inst_543_, lean_object* v_inst_544_, lean_object* v_inst_545_, lean_object* v_msgData_546_, uint8_t v_severity_547_, uint8_t v_isSilent_548_){
_start:
{
lean_object* v_toBind_549_; lean_object* v_getRef_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___f_553_; lean_object* v___x_554_; 
v_toBind_549_ = lean_ctor_get(v_inst_542_, 1);
lean_inc(v_toBind_549_);
v_getRef_550_ = lean_ctor_get(v_inst_543_, 1);
lean_inc(v_getRef_550_);
v___x_551_ = lean_box(v_severity_547_);
v___x_552_ = lean_box(v_isSilent_548_);
v___f_553_ = lean_alloc_closure((void*)(l_Lean_log___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_553_, 0, v_inst_542_);
lean_closure_set(v___f_553_, 1, v_inst_543_);
lean_closure_set(v___f_553_, 2, v_inst_544_);
lean_closure_set(v___f_553_, 3, v_inst_545_);
lean_closure_set(v___f_553_, 4, v_msgData_546_);
lean_closure_set(v___f_553_, 5, v___x_551_);
lean_closure_set(v___f_553_, 6, v___x_552_);
v___x_554_ = lean_apply_4(v_toBind_549_, lean_box(0), lean_box(0), v_getRef_550_, v___f_553_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___redArg___boxed(lean_object* v_inst_555_, lean_object* v_inst_556_, lean_object* v_inst_557_, lean_object* v_inst_558_, lean_object* v_msgData_559_, lean_object* v_severity_560_, lean_object* v_isSilent_561_){
_start:
{
uint8_t v_severity_boxed_562_; uint8_t v_isSilent_boxed_563_; lean_object* v_res_564_; 
v_severity_boxed_562_ = lean_unbox(v_severity_560_);
v_isSilent_boxed_563_ = lean_unbox(v_isSilent_561_);
v_res_564_ = l_Lean_log___redArg(v_inst_555_, v_inst_556_, v_inst_557_, v_inst_558_, v_msgData_559_, v_severity_boxed_562_, v_isSilent_boxed_563_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_log(lean_object* v_m_565_, lean_object* v_inst_566_, lean_object* v_inst_567_, lean_object* v_inst_568_, lean_object* v_inst_569_, lean_object* v_msgData_570_, uint8_t v_severity_571_, uint8_t v_isSilent_572_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = l_Lean_log___redArg(v_inst_566_, v_inst_567_, v_inst_568_, v_inst_569_, v_msgData_570_, v_severity_571_, v_isSilent_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___boxed(lean_object* v_m_574_, lean_object* v_inst_575_, lean_object* v_inst_576_, lean_object* v_inst_577_, lean_object* v_inst_578_, lean_object* v_msgData_579_, lean_object* v_severity_580_, lean_object* v_isSilent_581_){
_start:
{
uint8_t v_severity_boxed_582_; uint8_t v_isSilent_boxed_583_; lean_object* v_res_584_; 
v_severity_boxed_582_ = lean_unbox(v_severity_580_);
v_isSilent_boxed_583_ = lean_unbox(v_isSilent_581_);
v_res_584_ = l_Lean_log(v_m_574_, v_inst_575_, v_inst_576_, v_inst_577_, v_inst_578_, v_msgData_579_, v_severity_boxed_582_, v_isSilent_boxed_583_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___redArg(lean_object* v_inst_585_, lean_object* v_inst_586_, lean_object* v_inst_587_, lean_object* v_inst_588_, lean_object* v_msgData_589_){
_start:
{
uint8_t v___x_590_; uint8_t v___x_591_; lean_object* v___x_592_; 
v___x_590_ = 2;
v___x_591_ = 0;
v___x_592_ = l_Lean_log___redArg(v_inst_585_, v_inst_586_, v_inst_587_, v_inst_588_, v_msgData_589_, v___x_590_, v___x_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError(lean_object* v_m_593_, lean_object* v_inst_594_, lean_object* v_inst_595_, lean_object* v_inst_596_, lean_object* v_inst_597_, lean_object* v_msgData_598_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l_Lean_logError___redArg(v_inst_594_, v_inst_595_, v_inst_596_, v_inst_597_, v_msgData_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedError___redArg(lean_object* v_inst_600_, lean_object* v_inst_601_, lean_object* v_inst_602_, lean_object* v_inst_603_, lean_object* v_name_604_, lean_object* v_msgData_605_){
_start:
{
lean_object* v___x_606_; uint8_t v___x_607_; uint8_t v___x_608_; lean_object* v___x_609_; 
v___x_606_ = l_Lean_MessageData_tagWithErrorName(v_msgData_605_, v_name_604_);
v___x_607_ = 2;
v___x_608_ = 0;
v___x_609_ = l_Lean_log___redArg(v_inst_600_, v_inst_601_, v_inst_602_, v_inst_603_, v___x_606_, v___x_607_, v___x_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedError(lean_object* v_m_610_, lean_object* v_inst_611_, lean_object* v_inst_612_, lean_object* v_inst_613_, lean_object* v_inst_614_, lean_object* v_name_615_, lean_object* v_msgData_616_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l_Lean_logNamedError___redArg(v_inst_611_, v_inst_612_, v_inst_613_, v_inst_614_, v_name_615_, v_msgData_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___redArg(lean_object* v_inst_618_, lean_object* v_inst_619_, lean_object* v_inst_620_, lean_object* v_inst_621_, lean_object* v_msgData_622_){
_start:
{
uint8_t v___x_623_; uint8_t v___x_624_; lean_object* v___x_625_; 
v___x_623_ = 1;
v___x_624_ = 0;
v___x_625_ = l_Lean_log___redArg(v_inst_618_, v_inst_619_, v_inst_620_, v_inst_621_, v_msgData_622_, v___x_623_, v___x_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning(lean_object* v_m_626_, lean_object* v_inst_627_, lean_object* v_inst_628_, lean_object* v_inst_629_, lean_object* v_inst_630_, lean_object* v_msgData_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_Lean_logWarning___redArg(v_inst_627_, v_inst_628_, v_inst_629_, v_inst_630_, v_msgData_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedWarning___redArg(lean_object* v_inst_633_, lean_object* v_inst_634_, lean_object* v_inst_635_, lean_object* v_inst_636_, lean_object* v_name_637_, lean_object* v_msgData_638_){
_start:
{
lean_object* v___x_639_; uint8_t v___x_640_; uint8_t v___x_641_; lean_object* v___x_642_; 
v___x_639_ = l_Lean_MessageData_tagWithErrorName(v_msgData_638_, v_name_637_);
v___x_640_ = 1;
v___x_641_ = 0;
v___x_642_ = l_Lean_log___redArg(v_inst_633_, v_inst_634_, v_inst_635_, v_inst_636_, v___x_639_, v___x_640_, v___x_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedWarning(lean_object* v_m_643_, lean_object* v_inst_644_, lean_object* v_inst_645_, lean_object* v_inst_646_, lean_object* v_inst_647_, lean_object* v_name_648_, lean_object* v_msgData_649_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l_Lean_logNamedWarning___redArg(v_inst_644_, v_inst_645_, v_inst_646_, v_inst_647_, v_name_648_, v_msgData_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___redArg(lean_object* v_inst_651_, lean_object* v_inst_652_, lean_object* v_inst_653_, lean_object* v_inst_654_, lean_object* v_msgData_655_){
_start:
{
uint8_t v___x_656_; uint8_t v___x_657_; lean_object* v___x_658_; 
v___x_656_ = 0;
v___x_657_ = 0;
v___x_658_ = l_Lean_log___redArg(v_inst_651_, v_inst_652_, v_inst_653_, v_inst_654_, v_msgData_655_, v___x_656_, v___x_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo(lean_object* v_m_659_, lean_object* v_inst_660_, lean_object* v_inst_661_, lean_object* v_inst_662_, lean_object* v_inst_663_, lean_object* v_msgData_664_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = l_Lean_logInfo___redArg(v_inst_660_, v_inst_661_, v_inst_662_, v_inst_663_, v_msgData_664_);
return v___x_665_;
}
}
static lean_object* _init_l_Lean_logUnknownDecl___redArg___closed__1(void){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = ((lean_object*)(l_Lean_logUnknownDecl___redArg___closed__0));
v___x_668_ = l_Lean_stringToMessageData(v___x_667_);
return v___x_668_;
}
}
static lean_object* _init_l_Lean_logUnknownDecl___redArg___closed__3(void){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = ((lean_object*)(l_Lean_logUnknownDecl___redArg___closed__2));
v___x_671_ = l_Lean_stringToMessageData(v___x_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_logUnknownDecl___redArg(lean_object* v_inst_672_, lean_object* v_inst_673_, lean_object* v_inst_674_, lean_object* v_inst_675_, lean_object* v_declName_676_){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_677_ = lean_obj_once(&l_Lean_logUnknownDecl___redArg___closed__1, &l_Lean_logUnknownDecl___redArg___closed__1_once, _init_l_Lean_logUnknownDecl___redArg___closed__1);
v___x_678_ = l_Lean_MessageData_ofName(v_declName_676_);
v___x_679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_679_, 0, v___x_677_);
lean_ctor_set(v___x_679_, 1, v___x_678_);
v___x_680_ = lean_obj_once(&l_Lean_logUnknownDecl___redArg___closed__3, &l_Lean_logUnknownDecl___redArg___closed__3_once, _init_l_Lean_logUnknownDecl___redArg___closed__3);
v___x_681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_681_, 0, v___x_679_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
v___x_682_ = l_Lean_logError___redArg(v_inst_672_, v_inst_673_, v_inst_674_, v_inst_675_, v___x_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_logUnknownDecl(lean_object* v_m_683_, lean_object* v_inst_684_, lean_object* v_inst_685_, lean_object* v_inst_686_, lean_object* v_inst_687_, lean_object* v_declName_688_){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = l_Lean_logUnknownDecl___redArg(v_inst_684_, v_inst_685_, v_inst_686_, v_inst_687_, v_declName_688_);
return v___x_689_;
}
}
lean_object* runtime_initialize_Lean_ErrorExplanation(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Log(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_ErrorExplanation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_();
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
