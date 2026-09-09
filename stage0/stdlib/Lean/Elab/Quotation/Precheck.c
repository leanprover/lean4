// Lean compiler output
// Module: Lean.Elab.Quotation.Precheck
// Imports: public import Lean.Elab.Quotation.Util import Lean.Elab.DeprecatedSyntax
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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Syntax_isAnyAntiquot(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Macro_expandMacro_x3f___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_sub(size_t, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_evalIdentKey(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_init___redArg(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_getValues___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
extern lean_object* l_Lean_Linter_linter_deprecated_syntax;
extern lean_object* l_Lean_Linter_linterSetsExt;
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
extern lean_object* l_Lean_Linter_linterMessageTag;
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
extern lean_object* l_Lean_Elab_deprecatedSyntaxExt;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesIdent(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Elab_realizeGlobalNameWithInfos(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resolveName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getQuotContent(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
extern lean_object* l_Lean_Elab_Term_Quotation_hygiene;
lean_object* l_Lean_Elab_Term_adaptExpander(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_withNewLocal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_withNewLocal___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_withNewLocal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_withNewLocal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Quotation_withNewLocals_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Quotation_withNewLocals_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_withNewLocals___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_withNewLocals___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_withNewLocals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_withNewLocals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "quotPrecheck"};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(232, 232, 129, 207, 165, 21, 210, 151)}};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 236, .m_capacity = 236, .m_length = 235, .m_data = "Enable eager name analysis on notations in order to find unbound identifiers early.\nNote that type-sensitive syntax (\"elaborators\") needs special support for this kind of check, so it might need to be turned off when using such syntax."};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Quotation"};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(14, 125, 73, 172, 99, 41, 123, 101)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(65, 56, 228, 97, 200, 215, 173, 209)}};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_quotPrecheck;
static const lean_string_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "allowSectionVars"};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(232, 232, 129, 207, 165, 21, 210, 151)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(88, 69, 101, 149, 23, 62, 51, 0)}};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 106, .m_capacity = 106, .m_length = 105, .m_data = "Allow occurrences of section variables in checked quotations, it is useful when declaring local notation."};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(14, 125, 73, 172, 99, 41, 123, 101)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(65, 56, 228, 97, 200, 215, 173, 209)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value_aux_4),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(37, 117, 254, 154, 34, 204, 1, 44)}};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_quotPrecheck_allowSectionVars;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___lam__0_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___lam__0_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___lam__1_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___lam__1_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___lam__0_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___lam__1_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2____boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "builtin_quot_precheck"};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(174, 247, 11, 123, 196, 4, 137, 247)}};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "quot_precheck"};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(136, 16, 194, 46, 122, 138, 84, 224)}};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "Register a double backtick syntax quotation pre-check."};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Precheck"};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(14, 125, 73, 172, 99, 41, 123, 101)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(169, 189, 97, 153, 33, 221, 10, 105)}};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__9_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__9_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__9_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__10_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "precheckAttribute"};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__10_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__10_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__11_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__11_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__11_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__11_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__11_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__11_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__11_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(14, 125, 73, 172, 99, 41, 123, 101)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__11_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__11_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__10_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(197, 91, 218, 200, 14, 173, 229, 62)}};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__11_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__11_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute;
static const lean_string_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 522, .m_capacity = 522, .m_length = 521, .m_data = "Registers a double backtick syntax quotation pre-check.\n\n`@[quot_precheck k]` registers a declaration of type `Lean.Elab.Term.Quotation.Precheck` for the\nsyntax node kind `k`. It should implement eager name analysis on the passed syntax by throwing an\nexception on unbound identifiers, and calling `precheck` recursively on nested terms, potentially\nwith an extended local context (`withNewLocal`). Macros without registered precheck hook are\nunfolded, and identifier-less syntax is ultimately assumed to be well-formed.\n"};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_docString__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(41) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(57) << 1) | 1)),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__1_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(51) << 1) | 1)),((lean_object*)(((size_t)(26) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(51) << 1) | 1)),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__3_value),((lean_object*)(((size_t)(26) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__4_value),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___closed__0 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___closed__0_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___closed__1 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___closed__1_value;
LEAN_EXPORT uint8_t l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__10_spec__15___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__10_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20_spec__22(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20_spec__22___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "This linter can be disabled with `set_option "};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11___closed__0 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11___closed__0_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11___closed__1;
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " false`"};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11___closed__2 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11___closed__2_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11___closed__3;
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___closed__0;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4___closed__0 = (const lean_object*)&l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16_spec__20___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__4;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__5;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__7_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__7_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__8_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__12;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__13;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__17_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__18;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__20_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__21 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__21_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__22 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__22_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6_spec__12___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 157, .m_data = "maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information"};
static const lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_Quotation_precheck___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "no macro or `[quot_precheck]` instance for syntax kind `"};
static const lean_object* l_Lean_Elab_Term_Quotation_precheck___closed__0 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheck___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Term_Quotation_precheck___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_Quotation_precheck___closed__1;
static const lean_string_object l_Lean_Elab_Term_Quotation_precheck___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "` found"};
static const lean_object* l_Lean_Elab_Term_Quotation_precheck___closed__2 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheck___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Term_Quotation_precheck___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_Quotation_precheck___closed__3;
static const lean_string_object l_Lean_Elab_Term_Quotation_precheck___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 152, .m_capacity = 152, .m_length = 151, .m_data = "\nThis means we cannot eagerly check your notation/quotation for unbound identifiers; you can use `set_option quotPrecheck false` to disable this check."};
static const lean_object* l_Lean_Elab_Term_Quotation_precheck___closed__4 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheck___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Term_Quotation_precheck___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_Quotation_precheck___closed__5;
static const lean_string_object l_Lean_Elab_Term_Quotation_precheck___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "quotation uses deprecated syntax '"};
static const lean_object* l_Lean_Elab_Term_Quotation_precheck___closed__6 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheck___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Term_Quotation_precheck___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_Quotation_precheck___closed__7;
static const lean_string_object l_Lean_Elab_Term_Quotation_precheck___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Elab_Term_Quotation_precheck___closed__8 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheck___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Term_Quotation_precheck___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_Quotation_precheck___closed__9;
static const lean_string_object l_Lean_Elab_Term_Quotation_precheck___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Elab_Term_Quotation_precheck___closed__10 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheck___closed__10_value;
static lean_once_cell_t l_Lean_Elab_Term_Quotation_precheck___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_Quotation_precheck___closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheck___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__10_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__10_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_runPrecheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_runPrecheck___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable_spec__0___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___closed__1_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_Quotation_precheckIdent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Unknown identifier `"};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___closed__0 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckIdent___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Term_Quotation_precheckIdent___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___closed__1;
static const lean_string_object l_Lean_Elab_Term_Quotation_precheckIdent___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "` at quotation precheck"};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___closed__2 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckIdent___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Term_Quotation_precheckIdent___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___closed__3;
static const lean_string_object l_Lean_Elab_Term_Quotation_precheckIdent___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "You can use `set_option quotPrecheck false` to disable this check."};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___closed__4 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckIdent___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckIdent___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckIdent___closed__4_value)}};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___closed__5 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckIdent___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Term_Quotation_precheckIdent___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___closed__6;
static lean_once_cell_t l_Lean_Elab_Term_Quotation_precheckIdent___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckIdent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "precheckIdent"};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(14, 125, 73, 172, 99, 41, 123, 101)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(130, 137, 165, 162, 174, 93, 212, 1)}};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___boxed(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "namedArgument"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__2_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(226, 89, 129, 113, 173, 121, 169, 188)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ellipsis"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(101, 52, 71, 179, 21, 116, 195, 217)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__4_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_Quotation_precheckApp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckApp___closed__0 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckApp___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckApp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckApp___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckApp___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckApp___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckApp___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckApp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckApp___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_Quotation_precheckApp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckApp___closed__1 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckApp___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "precheckApp"};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(14, 125, 73, 172, 99, 41, 123, 101)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(163, 232, 133, 146, 248, 6, 112, 147)}};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "typeAscription"};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__0 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 209, 88, 141, 5, 195, 49, 74)}};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__1 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__1_value;
static const lean_string_object l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__2 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__2_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__3 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckTypeAscription(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckTypeAscription___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "precheckTypeAscription"};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(14, 125, 73, 172, 99, 41, 123, 101)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 182, 167, 232, 99, 17, 44, 94)}};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Term_Quotation_precheckExplicit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "explicit"};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckExplicit___closed__0 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckExplicit___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckExplicit___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckExplicit___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckExplicit___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckExplicit___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckExplicit___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckExplicit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckExplicit___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_Quotation_precheckExplicit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(141, 201, 75, 195, 250, 223, 114, 184)}};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckExplicit___closed__1 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckExplicit___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckExplicit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckExplicit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "precheckExplicit"};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(14, 125, 73, 172, 99, 41, 123, 101)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(186, 174, 145, 115, 15, 112, 132, 151)}};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___boxed(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_Quotation_precheckChoice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 110, .m_capacity = 110, .m_length = 109, .m_data = "ambiguous notation with at least one interpretation that failed quotation precheck, possible interpretations "};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckChoice___closed__0 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckChoice___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Term_Quotation_precheckChoice___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_Quotation_precheckChoice___closed__1;
static const lean_string_object l_Lean_Elab_Term_Quotation_precheckChoice___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\n\n"};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckChoice___closed__2 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckChoice___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Term_Quotation_precheckChoice___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_Quotation_precheckChoice___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckChoice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckChoice___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "choice"};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 66, 148, 42, 181, 100, 85, 166)}};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "precheckChoice"};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(14, 125, 73, 172, 99, 41, 123, 101)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(219, 120, 91, 227, 172, 108, 142, 184)}};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "precheckedQuot"};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(110, 214, 3, 29, 194, 190, 3, 97)}};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "elabPrecheckedQuot"};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(14, 125, 73, 172, 99, 41, 123, 101)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(60, 249, 149, 118, 59, 253, 255, 197)}};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(139) << 1) | 1)),((lean_object*)(((size_t)(36) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(142) << 1) | 1)),((lean_object*)(((size_t)(60) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__0_value),((lean_object*)(((size_t)(36) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__1_value),((lean_object*)(((size_t)(60) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(139) << 1) | 1)),((lean_object*)(((size_t)(40) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(139) << 1) | 1)),((lean_object*)(((size_t)(58) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__3_value),((lean_object*)(((size_t)(40) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__4_value),((lean_object*)(((size_t)(58) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Term_Quotation_precheckBinrel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "binrel"};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckBinrel___closed__0 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinrel___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinrel___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinrel___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinrel___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinrel___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinrel___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinrel___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinrel___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinrel___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 238, 75, 93, 70, 164, 233, 165)}};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckBinrel___closed__1 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinrel___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinrel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinrel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "precheckBinrel"};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(14, 125, 73, 172, 99, 41, 123, 101)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(83, 230, 82, 89, 81, 213, 228, 178)}};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "binrel_no_prop"};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__0 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 122, 90, 92, 171, 187, 176, 37)}};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__1 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinrelNoProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "precheckBinrelNoProp"};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(14, 125, 73, 172, 99, 41, 123, 101)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(225, 10, 254, 77, 93, 46, 3, 51)}};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Term_Quotation_precheckBinop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "binop"};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckBinop___closed__0 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinop___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinop___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinop___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinop___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinop___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinop___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinop___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinop___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinop___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 253, 231, 222, 243, 42, 73, 191)}};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckBinop___closed__1 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinop___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "precheckBinop"};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(14, 125, 73, 172, 99, 41, 123, 101)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(208, 17, 13, 13, 42, 64, 96, 27)}};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "binop_lazy"};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__0 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__0_value),LEAN_SCALAR_PTR_LITERAL(35, 222, 106, 2, 24, 145, 254, 163)}};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__1 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinopLazy(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinopLazy___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "precheckBinopLazy"};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(14, 125, 73, 172, 99, 41, 123, 101)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(220, 63, 127, 230, 166, 233, 146, 124)}};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Term_Quotation_precheckLeftact___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "leftact"};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckLeftact___closed__0 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckLeftact___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckLeftact___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckLeftact___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckLeftact___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckLeftact___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckLeftact___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckLeftact___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckLeftact___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_Quotation_precheckLeftact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(235, 190, 22, 58, 115, 190, 112, 107)}};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckLeftact___closed__1 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckLeftact___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckLeftact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckLeftact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "precheckLeftact"};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(14, 125, 73, 172, 99, 41, 123, 101)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 14, 84, 189, 210, 228, 161, 228)}};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Term_Quotation_precheckRightact___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "rightact"};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckRightact___closed__0 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckRightact___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckRightact___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckRightact___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckRightact___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckRightact___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckRightact___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckRightact___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckRightact___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_Quotation_precheckRightact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(147, 6, 66, 125, 81, 188, 156, 70)}};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckRightact___closed__1 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckRightact___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckRightact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckRightact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "precheckRightact"};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(14, 125, 73, 172, 99, 41, 123, 101)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(110, 63, 207, 226, 148, 187, 163, 109)}};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Term_Quotation_precheckUnop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "unop"};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckUnop___closed__0 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckUnop___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckUnop___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckUnop___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckUnop___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckUnop___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckUnop___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckUnop___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckUnop___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_Quotation_precheckUnop___closed__0_value),LEAN_SCALAR_PTR_LITERAL(68, 253, 109, 39, 185, 175, 169, 133)}};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckUnop___closed__1 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckUnop___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckUnop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckUnop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "precheckUnop"};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(14, 125, 73, 172, 99, 41, 123, 101)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 68, 33, 200, 202, 154, 57, 80)}};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckHygieneInfo___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckHygieneInfo___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckHygieneInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckHygieneInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__0_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__0_value_aux_2),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___closed__0_value),LEAN_SCALAR_PTR_LITERAL(11, 171, 53, 55, 110, 181, 251, 200)}};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "precheckHygieneInfo"};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(14, 125, 73, 172, 99, 41, 123, 101)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__2_value_aux_3),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 51, 232, 44, 217, 70, 133, 185)}};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_withNewLocal___redArg(lean_object* v_l_1_, lean_object* v_x_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
lean_inc(v_a_3_);
v___x_11_ = l_Lean_NameSet_insert(v_a_3_, v_l_1_);
lean_inc(v_a_9_);
lean_inc_ref(v_a_8_);
lean_inc(v_a_7_);
lean_inc_ref(v_a_6_);
lean_inc(v_a_5_);
lean_inc_ref(v_a_4_);
v___x_12_ = lean_apply_8(v_x_2_, v___x_11_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, lean_box(0));
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_withNewLocal___redArg___boxed(lean_object* v_l_13_, lean_object* v_x_14_, lean_object* v_a_15_, lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_Elab_Term_Quotation_withNewLocal___redArg(v_l_13_, v_x_14_, v_a_15_, v_a_16_, v_a_17_, v_a_18_, v_a_19_, v_a_20_, v_a_21_);
lean_dec(v_a_21_);
lean_dec_ref(v_a_20_);
lean_dec(v_a_19_);
lean_dec_ref(v_a_18_);
lean_dec(v_a_17_);
lean_dec_ref(v_a_16_);
lean_dec(v_a_15_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_withNewLocal(lean_object* v_00_u03b1_24_, lean_object* v_l_25_, lean_object* v_x_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Lean_Elab_Term_Quotation_withNewLocal___redArg(v_l_25_, v_x_26_, v_a_27_, v_a_28_, v_a_29_, v_a_30_, v_a_31_, v_a_32_, v_a_33_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_withNewLocal___boxed(lean_object* v_00_u03b1_36_, lean_object* v_l_37_, lean_object* v_x_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lean_Elab_Term_Quotation_withNewLocal(v_00_u03b1_36_, v_l_37_, v_x_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_);
lean_dec(v_a_45_);
lean_dec_ref(v_a_44_);
lean_dec(v_a_43_);
lean_dec_ref(v_a_42_);
lean_dec(v_a_41_);
lean_dec_ref(v_a_40_);
lean_dec(v_a_39_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Quotation_withNewLocals_spec__0(lean_object* v_as_48_, size_t v_i_49_, size_t v_stop_50_, lean_object* v_b_51_){
_start:
{
uint8_t v___x_52_; 
v___x_52_ = lean_usize_dec_eq(v_i_49_, v_stop_50_);
if (v___x_52_ == 0)
{
lean_object* v___x_53_; lean_object* v___x_54_; size_t v___x_55_; size_t v___x_56_; 
v___x_53_ = lean_array_uget_borrowed(v_as_48_, v_i_49_);
lean_inc(v___x_53_);
v___x_54_ = l_Lean_NameSet_insert(v_b_51_, v___x_53_);
v___x_55_ = ((size_t)1ULL);
v___x_56_ = lean_usize_add(v_i_49_, v___x_55_);
v_i_49_ = v___x_56_;
v_b_51_ = v___x_54_;
goto _start;
}
else
{
return v_b_51_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Quotation_withNewLocals_spec__0___boxed(lean_object* v_as_58_, lean_object* v_i_59_, lean_object* v_stop_60_, lean_object* v_b_61_){
_start:
{
size_t v_i_boxed_62_; size_t v_stop_boxed_63_; lean_object* v_res_64_; 
v_i_boxed_62_ = lean_unbox_usize(v_i_59_);
lean_dec(v_i_59_);
v_stop_boxed_63_ = lean_unbox_usize(v_stop_60_);
lean_dec(v_stop_60_);
v_res_64_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Quotation_withNewLocals_spec__0(v_as_58_, v_i_boxed_62_, v_stop_boxed_63_, v_b_61_);
lean_dec_ref(v_as_58_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_withNewLocals___redArg(lean_object* v_ls_65_, lean_object* v_x_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; uint8_t v___x_77_; 
v___x_75_ = lean_unsigned_to_nat(0u);
v___x_76_ = lean_array_get_size(v_ls_65_);
v___x_77_ = lean_nat_dec_lt(v___x_75_, v___x_76_);
if (v___x_77_ == 0)
{
lean_object* v___x_78_; 
lean_inc(v_a_73_);
lean_inc_ref(v_a_72_);
lean_inc(v_a_71_);
lean_inc_ref(v_a_70_);
lean_inc(v_a_69_);
lean_inc_ref(v_a_68_);
lean_inc(v_a_67_);
v___x_78_ = lean_apply_8(v_x_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_, lean_box(0));
return v___x_78_;
}
else
{
uint8_t v___x_79_; 
v___x_79_ = lean_nat_dec_le(v___x_76_, v___x_76_);
if (v___x_79_ == 0)
{
if (v___x_77_ == 0)
{
lean_object* v___x_80_; 
lean_inc(v_a_73_);
lean_inc_ref(v_a_72_);
lean_inc(v_a_71_);
lean_inc_ref(v_a_70_);
lean_inc(v_a_69_);
lean_inc_ref(v_a_68_);
lean_inc(v_a_67_);
v___x_80_ = lean_apply_8(v_x_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_, lean_box(0));
return v___x_80_;
}
else
{
size_t v___x_81_; size_t v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_81_ = ((size_t)0ULL);
v___x_82_ = lean_usize_of_nat(v___x_76_);
lean_inc(v_a_67_);
v___x_83_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Quotation_withNewLocals_spec__0(v_ls_65_, v___x_81_, v___x_82_, v_a_67_);
lean_inc(v_a_73_);
lean_inc_ref(v_a_72_);
lean_inc(v_a_71_);
lean_inc_ref(v_a_70_);
lean_inc(v_a_69_);
lean_inc_ref(v_a_68_);
v___x_84_ = lean_apply_8(v_x_66_, v___x_83_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_, lean_box(0));
return v___x_84_;
}
}
else
{
size_t v___x_85_; size_t v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_85_ = ((size_t)0ULL);
v___x_86_ = lean_usize_of_nat(v___x_76_);
lean_inc(v_a_67_);
v___x_87_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Quotation_withNewLocals_spec__0(v_ls_65_, v___x_85_, v___x_86_, v_a_67_);
lean_inc(v_a_73_);
lean_inc_ref(v_a_72_);
lean_inc(v_a_71_);
lean_inc_ref(v_a_70_);
lean_inc(v_a_69_);
lean_inc_ref(v_a_68_);
v___x_88_ = lean_apply_8(v_x_66_, v___x_87_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_, lean_box(0));
return v___x_88_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_withNewLocals___redArg___boxed(lean_object* v_ls_89_, lean_object* v_x_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lean_Elab_Term_Quotation_withNewLocals___redArg(v_ls_89_, v_x_90_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_);
lean_dec(v_a_97_);
lean_dec_ref(v_a_96_);
lean_dec(v_a_95_);
lean_dec_ref(v_a_94_);
lean_dec(v_a_93_);
lean_dec_ref(v_a_92_);
lean_dec(v_a_91_);
lean_dec_ref(v_ls_89_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_withNewLocals(lean_object* v_00_u03b1_100_, lean_object* v_ls_101_, lean_object* v_x_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_Lean_Elab_Term_Quotation_withNewLocals___redArg(v_ls_101_, v_x_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_withNewLocals___boxed(lean_object* v_00_u03b1_112_, lean_object* v_ls_113_, lean_object* v_x_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Lean_Elab_Term_Quotation_withNewLocals(v_00_u03b1_112_, v_ls_113_, v_x_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_);
lean_dec(v_a_121_);
lean_dec_ref(v_a_120_);
lean_dec(v_a_119_);
lean_dec_ref(v_a_118_);
lean_dec(v_a_117_);
lean_dec_ref(v_a_116_);
lean_dec(v_a_115_);
lean_dec_ref(v_ls_113_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__spec__0(lean_object* v_name_124_, lean_object* v_decl_125_, lean_object* v_ref_126_){
_start:
{
lean_object* v_defValue_128_; lean_object* v_descr_129_; lean_object* v_deprecation_x3f_130_; lean_object* v___x_131_; uint8_t v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v_defValue_128_ = lean_ctor_get(v_decl_125_, 0);
v_descr_129_ = lean_ctor_get(v_decl_125_, 1);
v_deprecation_x3f_130_ = lean_ctor_get(v_decl_125_, 2);
v___x_131_ = lean_alloc_ctor(1, 0, 1);
v___x_132_ = lean_unbox(v_defValue_128_);
lean_ctor_set_uint8(v___x_131_, 0, v___x_132_);
lean_inc(v_deprecation_x3f_130_);
lean_inc_ref(v_descr_129_);
lean_inc_n(v_name_124_, 2);
v___x_133_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_133_, 0, v_name_124_);
lean_ctor_set(v___x_133_, 1, v_ref_126_);
lean_ctor_set(v___x_133_, 2, v___x_131_);
lean_ctor_set(v___x_133_, 3, v_descr_129_);
lean_ctor_set(v___x_133_, 4, v_deprecation_x3f_130_);
v___x_134_ = lean_register_option(v_name_124_, v___x_133_);
if (lean_obj_tag(v___x_134_) == 0)
{
lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_142_; 
v_isSharedCheck_142_ = !lean_is_exclusive(v___x_134_);
if (v_isSharedCheck_142_ == 0)
{
lean_object* v_unused_143_; 
v_unused_143_ = lean_ctor_get(v___x_134_, 0);
lean_dec(v_unused_143_);
v___x_136_ = v___x_134_;
v_isShared_137_ = v_isSharedCheck_142_;
goto v_resetjp_135_;
}
else
{
lean_dec(v___x_134_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_142_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_138_; lean_object* v___x_140_; 
lean_inc(v_defValue_128_);
v___x_138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_138_, 0, v_name_124_);
lean_ctor_set(v___x_138_, 1, v_defValue_128_);
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 0, v___x_138_);
v___x_140_ = v___x_136_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v___x_138_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
return v___x_140_;
}
}
}
else
{
lean_object* v_a_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_151_; 
lean_dec(v_name_124_);
v_a_144_ = lean_ctor_get(v___x_134_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v___x_134_);
if (v_isSharedCheck_151_ == 0)
{
v___x_146_ = v___x_134_;
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_a_144_);
lean_dec(v___x_134_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_149_; 
if (v_isShared_147_ == 0)
{
v___x_149_ = v___x_146_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_a_144_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_152_, lean_object* v_decl_153_, lean_object* v_ref_154_, lean_object* v_a_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lean_Option_register___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__spec__0(v_name_152_, v_decl_153_, v_ref_154_);
lean_dec_ref(v_decl_153_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_177_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_));
v___x_178_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_));
v___x_179_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_));
v___x_180_ = l_Lean_Option_register___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__spec__0(v___x_177_, v___x_178_, v___x_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4____boxed(lean_object* v_a_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_();
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_201_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4_));
v___x_202_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4_));
v___x_203_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4_));
v___x_204_ = l_Lean_Option_register___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__spec__0(v___x_201_, v___x_202_, v___x_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4____boxed(lean_object* v_a_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4_();
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___lam__0_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_(uint8_t v_builtin_207_, lean_object* v_stx_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_KeyedDeclsAttribute_evalIdentKey(v_stx_208_, v___y_209_, v___y_210_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___lam__0_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2____boxed(lean_object* v_builtin_213_, lean_object* v_stx_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_){
_start:
{
uint8_t v_builtin_boxed_218_; lean_object* v_res_219_; 
v_builtin_boxed_218_ = lean_unbox(v_builtin_213_);
v_res_219_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___lam__0_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_(v_builtin_boxed_218_, v_stx_214_, v___y_215_, v___y_216_);
lean_dec(v___y_216_);
lean_dec_ref(v___y_215_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___lam__1_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_(uint8_t v_builtin_220_, lean_object* v_declName_221_, lean_object* v_key_222_, lean_object* v___y_223_, lean_object* v___y_224_){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = lean_box(0);
v___x_227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___lam__1_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2____boxed(lean_object* v_builtin_228_, lean_object* v_declName_229_, lean_object* v_key_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_){
_start:
{
uint8_t v_builtin_boxed_234_; lean_object* v_res_235_; 
v_builtin_boxed_234_ = lean_unbox(v_builtin_228_);
v_res_235_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___lam__1_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_(v_builtin_boxed_234_, v_declName_229_, v_key_230_, v___y_231_, v___y_232_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
lean_dec(v_key_230_);
lean_dec(v_declName_229_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_267_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__9_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_));
v___x_268_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__11_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_));
v___x_269_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_267_, v___x_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2____boxed(lean_object* v_a_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_();
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_docString__1(){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_274_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__11_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_));
v___x_275_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_docString__1___closed__0));
v___x_276_ = l_Lean_addBuiltinDocString(v___x_274_, v___x_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_docString__1___boxed(lean_object* v_a_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_docString__1();
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3(){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_305_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__11_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_));
v___x_306_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__6));
v___x_307_ = l_Lean_addBuiltinDeclarationRanges(v___x_305_, v___x_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___boxed(lean_object* v_a_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3();
return v_res_309_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent(lean_object* v_x_313_){
_start:
{
if (lean_obj_tag(v_x_313_) == 3)
{
uint8_t v___x_314_; 
lean_dec_ref_known(v_x_313_, 4);
v___x_314_ = 1;
return v___x_314_;
}
else
{
uint8_t v___x_315_; 
lean_inc(v_x_313_);
v___x_315_ = l_Lean_Syntax_isAnyAntiquot(v_x_313_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; uint8_t v___x_317_; 
v___x_316_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___closed__1));
lean_inc(v_x_313_);
v___x_317_ = l_Lean_Syntax_isOfKind(v_x_313_, v___x_316_);
if (v___x_317_ == 0)
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; uint8_t v___x_321_; 
v___x_318_ = l_Lean_Syntax_getArgs(v_x_313_);
lean_dec(v_x_313_);
v___x_319_ = lean_unsigned_to_nat(0u);
v___x_320_ = lean_array_get_size(v___x_318_);
v___x_321_ = lean_nat_dec_lt(v___x_319_, v___x_320_);
if (v___x_321_ == 0)
{
lean_dec_ref(v___x_318_);
return v___x_321_;
}
else
{
if (v___x_321_ == 0)
{
lean_dec_ref(v___x_318_);
return v___x_321_;
}
else
{
size_t v___x_322_; size_t v___x_323_; uint8_t v___x_324_; 
v___x_322_ = ((size_t)0ULL);
v___x_323_ = lean_usize_of_nat(v___x_320_);
v___x_324_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent_spec__0(v___x_318_, v___x_322_, v___x_323_);
lean_dec_ref(v___x_318_);
return v___x_324_;
}
}
}
else
{
lean_dec(v_x_313_);
return v___x_315_;
}
}
else
{
uint8_t v___x_325_; 
lean_dec(v_x_313_);
v___x_325_ = 0;
return v___x_325_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent_spec__0(lean_object* v_as_326_, size_t v_i_327_, size_t v_stop_328_){
_start:
{
uint8_t v___x_329_; 
v___x_329_ = lean_usize_dec_eq(v_i_327_, v_stop_328_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; uint8_t v___x_331_; 
v___x_330_ = lean_array_uget_borrowed(v_as_326_, v_i_327_);
lean_inc(v___x_330_);
v___x_331_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent(v___x_330_);
if (v___x_331_ == 0)
{
size_t v___x_332_; size_t v___x_333_; 
v___x_332_ = ((size_t)1ULL);
v___x_333_ = lean_usize_add(v_i_327_, v___x_332_);
v_i_327_ = v___x_333_;
goto _start;
}
else
{
return v___x_331_;
}
}
else
{
uint8_t v___x_335_; 
v___x_335_ = 0;
return v___x_335_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent_spec__0___boxed(lean_object* v_as_336_, lean_object* v_i_337_, lean_object* v_stop_338_){
_start:
{
size_t v_i_boxed_339_; size_t v_stop_boxed_340_; uint8_t v_res_341_; lean_object* v_r_342_; 
v_i_boxed_339_ = lean_unbox_usize(v_i_337_);
lean_dec(v_i_337_);
v_stop_boxed_340_ = lean_unbox_usize(v_stop_338_);
lean_dec(v_stop_338_);
v_res_341_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent_spec__0(v_as_336_, v_i_boxed_339_, v_stop_boxed_340_);
lean_dec_ref(v_as_336_);
v_r_342_ = lean_box(v_res_341_);
return v_r_342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___boxed(lean_object* v_x_343_){
_start:
{
uint8_t v_res_344_; lean_object* v_r_345_; 
v_res_344_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent(v_x_343_);
v_r_345_ = lean_box(v_res_344_);
return v_r_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__10_spec__15___redArg(lean_object* v_o_346_, lean_object* v___y_347_){
_start:
{
lean_object* v___x_349_; lean_object* v_env_350_; lean_object* v___x_351_; lean_object* v_toEnvExtension_352_; lean_object* v_asyncMode_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v_merged_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_365_; 
v___x_349_ = lean_st_ref_get(v___y_347_);
v_env_350_ = lean_ctor_get(v___x_349_, 0);
lean_inc_ref(v_env_350_);
lean_dec(v___x_349_);
v___x_351_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_352_ = lean_ctor_get(v___x_351_, 0);
v_asyncMode_353_ = lean_ctor_get(v_toEnvExtension_352_, 2);
v___x_354_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_355_ = lean_box(0);
v___x_356_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_354_, v___x_351_, v_env_350_, v_asyncMode_353_, v___x_355_);
v_merged_357_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_365_ == 0)
{
lean_object* v_unused_366_; 
v_unused_366_ = lean_ctor_get(v___x_356_, 1);
lean_dec(v_unused_366_);
v___x_359_ = v___x_356_;
v_isShared_360_ = v_isSharedCheck_365_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_merged_357_);
lean_dec(v___x_356_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_365_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_362_; 
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 1, v_merged_357_);
lean_ctor_set(v___x_359_, 0, v_o_346_);
v___x_362_ = v___x_359_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_o_346_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v_merged_357_);
v___x_362_ = v_reuseFailAlloc_364_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
lean_object* v___x_363_; 
v___x_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
return v___x_363_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__10_spec__15___redArg___boxed(lean_object* v_o_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__10_spec__15___redArg(v_o_367_, v___y_368_);
lean_dec(v___y_368_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__10(lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v_options_379_; lean_object* v___x_380_; 
v_options_379_ = lean_ctor_get(v___y_376_, 1);
lean_inc_ref(v_options_379_);
v___x_380_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__10_spec__15___redArg(v_options_379_, v___y_377_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__10___boxed(lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__10(v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec(v___y_381_);
return v_res_389_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20_spec__22(lean_object* v_opts_390_, lean_object* v_opt_391_){
_start:
{
lean_object* v_name_392_; lean_object* v_defValue_393_; lean_object* v_map_394_; lean_object* v___x_395_; 
v_name_392_ = lean_ctor_get(v_opt_391_, 0);
v_defValue_393_ = lean_ctor_get(v_opt_391_, 1);
v_map_394_ = lean_ctor_get(v_opts_390_, 0);
v___x_395_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_394_, v_name_392_);
if (lean_obj_tag(v___x_395_) == 0)
{
uint8_t v___x_396_; 
v___x_396_ = lean_unbox(v_defValue_393_);
return v___x_396_;
}
else
{
lean_object* v_val_397_; 
v_val_397_ = lean_ctor_get(v___x_395_, 0);
lean_inc(v_val_397_);
lean_dec_ref_known(v___x_395_, 1);
if (lean_obj_tag(v_val_397_) == 1)
{
uint8_t v_v_398_; 
v_v_398_ = lean_ctor_get_uint8(v_val_397_, 0);
lean_dec_ref_known(v_val_397_, 0);
return v_v_398_;
}
else
{
uint8_t v___x_399_; 
lean_dec(v_val_397_);
v___x_399_ = lean_unbox(v_defValue_393_);
return v___x_399_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20_spec__22___boxed(lean_object* v_opts_400_, lean_object* v_opt_401_){
_start:
{
uint8_t v_res_402_; lean_object* v_r_403_; 
v_res_402_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20_spec__22(v_opts_400_, v_opt_401_);
lean_dec_ref(v_opt_401_);
lean_dec_ref(v_opts_400_);
v_r_403_ = lean_box(v_res_402_);
return v_r_403_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0(uint8_t v_suppressElabErrors_411_, uint8_t v___y_412_, lean_object* v_x_413_){
_start:
{
if (lean_obj_tag(v_x_413_) == 1)
{
lean_object* v_pre_414_; 
v_pre_414_ = lean_ctor_get(v_x_413_, 0);
switch(lean_obj_tag(v_pre_414_))
{
case 1:
{
lean_object* v_pre_415_; 
v_pre_415_ = lean_ctor_get(v_pre_414_, 0);
switch(lean_obj_tag(v_pre_415_))
{
case 0:
{
lean_object* v_str_416_; lean_object* v_str_417_; lean_object* v___x_418_; uint8_t v___x_419_; 
v_str_416_ = lean_ctor_get(v_x_413_, 1);
v_str_417_ = lean_ctor_get(v_pre_414_, 1);
v___x_418_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_));
v___x_419_ = lean_string_dec_eq(v_str_417_, v___x_418_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; uint8_t v___x_421_; 
v___x_420_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__0));
v___x_421_ = lean_string_dec_eq(v_str_417_, v___x_420_);
if (v___x_421_ == 0)
{
return v___x_421_;
}
else
{
lean_object* v___x_422_; uint8_t v___x_423_; 
v___x_422_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__1));
v___x_423_ = lean_string_dec_eq(v_str_416_, v___x_422_);
if (v___x_423_ == 0)
{
return v___x_423_;
}
else
{
return v_suppressElabErrors_411_;
}
}
}
else
{
lean_object* v___x_424_; uint8_t v___x_425_; 
v___x_424_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__2));
v___x_425_ = lean_string_dec_eq(v_str_416_, v___x_424_);
if (v___x_425_ == 0)
{
return v___x_425_;
}
else
{
return v_suppressElabErrors_411_;
}
}
}
case 1:
{
lean_object* v_pre_426_; 
v_pre_426_ = lean_ctor_get(v_pre_415_, 0);
if (lean_obj_tag(v_pre_426_) == 0)
{
lean_object* v_str_427_; lean_object* v_str_428_; lean_object* v_str_429_; lean_object* v___x_430_; uint8_t v___x_431_; 
v_str_427_ = lean_ctor_get(v_x_413_, 1);
v_str_428_ = lean_ctor_get(v_pre_414_, 1);
v_str_429_ = lean_ctor_get(v_pre_415_, 1);
v___x_430_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__3));
v___x_431_ = lean_string_dec_eq(v_str_429_, v___x_430_);
if (v___x_431_ == 0)
{
return v___x_431_;
}
else
{
lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_432_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__4));
v___x_433_ = lean_string_dec_eq(v_str_428_, v___x_432_);
if (v___x_433_ == 0)
{
return v___x_433_;
}
else
{
lean_object* v___x_434_; uint8_t v___x_435_; 
v___x_434_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__5));
v___x_435_ = lean_string_dec_eq(v_str_427_, v___x_434_);
if (v___x_435_ == 0)
{
return v___x_435_;
}
else
{
return v_suppressElabErrors_411_;
}
}
}
}
else
{
return v___y_412_;
}
}
default: 
{
return v___y_412_;
}
}
}
case 0:
{
lean_object* v_str_436_; lean_object* v___x_437_; uint8_t v___x_438_; 
v_str_436_ = lean_ctor_get(v_x_413_, 1);
v___x_437_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__6));
v___x_438_ = lean_string_dec_eq(v_str_436_, v___x_437_);
if (v___x_438_ == 0)
{
return v___x_438_;
}
else
{
return v_suppressElabErrors_411_;
}
}
default: 
{
return v___y_412_;
}
}
}
else
{
return v___y_412_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_439_, lean_object* v___y_440_, lean_object* v_x_441_){
_start:
{
uint8_t v_suppressElabErrors_boxed_442_; uint8_t v___y_35878__boxed_443_; uint8_t v_res_444_; lean_object* v_r_445_; 
v_suppressElabErrors_boxed_442_ = lean_unbox(v_suppressElabErrors_439_);
v___y_35878__boxed_443_ = lean_unbox(v___y_440_);
v_res_444_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0(v_suppressElabErrors_boxed_442_, v___y_35878__boxed_443_, v_x_441_);
lean_dec(v_x_441_);
v_r_445_ = lean_box(v_res_444_);
return v_r_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0_spec__1(lean_object* v_msgData_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
lean_object* v___x_452_; lean_object* v_env_453_; lean_object* v___x_454_; lean_object* v_mctx_455_; lean_object* v_lctx_456_; lean_object* v_options_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_452_ = lean_st_ref_get(v___y_450_);
v_env_453_ = lean_ctor_get(v___x_452_, 0);
lean_inc_ref(v_env_453_);
lean_dec(v___x_452_);
v___x_454_ = lean_st_ref_get(v___y_448_);
v_mctx_455_ = lean_ctor_get(v___x_454_, 0);
lean_inc_ref(v_mctx_455_);
lean_dec(v___x_454_);
v_lctx_456_ = lean_ctor_get(v___y_447_, 2);
v_options_457_ = lean_ctor_get(v___y_449_, 1);
lean_inc_ref(v_options_457_);
lean_inc_ref(v_lctx_456_);
v___x_458_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_458_, 0, v_env_453_);
lean_ctor_set(v___x_458_, 1, v_mctx_455_);
lean_ctor_set(v___x_458_, 2, v_lctx_456_);
lean_ctor_set(v___x_458_, 3, v_options_457_);
v___x_459_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
lean_ctor_set(v___x_459_, 1, v_msgData_446_);
v___x_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0_spec__1(v_msgData_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
lean_dec(v___y_463_);
lean_dec_ref(v___y_462_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg(lean_object* v_ref_469_, lean_object* v_msgData_470_, uint8_t v_severity_471_, uint8_t v_isSilent_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
lean_object* v___y_479_; lean_object* v___y_480_; lean_object* v___y_481_; uint8_t v___y_482_; uint8_t v___y_483_; lean_object* v___y_484_; lean_object* v___y_485_; lean_object* v___y_486_; lean_object* v___y_487_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; uint8_t v___y_518_; uint8_t v___y_519_; uint8_t v___y_520_; lean_object* v___y_521_; lean_object* v___y_541_; lean_object* v___y_542_; uint8_t v___y_543_; uint8_t v___y_544_; uint8_t v___y_545_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_551_; lean_object* v___y_552_; uint8_t v___y_553_; uint8_t v___y_554_; lean_object* v___y_555_; uint8_t v___y_556_; uint8_t v___x_561_; lean_object* v___y_563_; lean_object* v___y_564_; uint8_t v___y_565_; lean_object* v___y_566_; uint8_t v___y_567_; uint8_t v___y_568_; uint8_t v___y_570_; uint8_t v___x_584_; 
v___x_561_ = 2;
v___x_584_ = l_Lean_instBEqMessageSeverity_beq(v_severity_471_, v___x_561_);
if (v___x_584_ == 0)
{
v___y_570_ = v___x_584_;
goto v___jp_569_;
}
else
{
uint8_t v___x_585_; 
lean_inc_ref(v_msgData_470_);
v___x_585_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_470_);
v___y_570_ = v___x_585_;
goto v___jp_569_;
}
v___jp_478_:
{
lean_object* v___x_488_; lean_object* v_currNamespace_489_; lean_object* v_openDecls_490_; lean_object* v_env_491_; lean_object* v_nextMacroScope_492_; lean_object* v_ngen_493_; lean_object* v_auxDeclNGen_494_; lean_object* v_traceState_495_; lean_object* v_cache_496_; lean_object* v_messages_497_; lean_object* v_infoState_498_; lean_object* v_snapshotTasks_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_513_; 
v___x_488_ = lean_st_ref_take(v___y_487_);
v_currNamespace_489_ = lean_ctor_get(v___y_486_, 5);
v_openDecls_490_ = lean_ctor_get(v___y_486_, 6);
v_env_491_ = lean_ctor_get(v___x_488_, 0);
v_nextMacroScope_492_ = lean_ctor_get(v___x_488_, 1);
v_ngen_493_ = lean_ctor_get(v___x_488_, 2);
v_auxDeclNGen_494_ = lean_ctor_get(v___x_488_, 3);
v_traceState_495_ = lean_ctor_get(v___x_488_, 4);
v_cache_496_ = lean_ctor_get(v___x_488_, 5);
v_messages_497_ = lean_ctor_get(v___x_488_, 6);
v_infoState_498_ = lean_ctor_get(v___x_488_, 7);
v_snapshotTasks_499_ = lean_ctor_get(v___x_488_, 8);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_513_ == 0)
{
v___x_501_ = v___x_488_;
v_isShared_502_ = v_isSharedCheck_513_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_snapshotTasks_499_);
lean_inc(v_infoState_498_);
lean_inc(v_messages_497_);
lean_inc(v_cache_496_);
lean_inc(v_traceState_495_);
lean_inc(v_auxDeclNGen_494_);
lean_inc(v_ngen_493_);
lean_inc(v_nextMacroScope_492_);
lean_inc(v_env_491_);
lean_dec(v___x_488_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_513_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_508_; 
lean_inc(v_openDecls_490_);
lean_inc(v_currNamespace_489_);
v___x_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_503_, 0, v_currNamespace_489_);
lean_ctor_set(v___x_503_, 1, v_openDecls_490_);
v___x_504_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
lean_ctor_set(v___x_504_, 1, v___y_481_);
lean_inc_ref(v___y_484_);
lean_inc_ref(v___y_480_);
v___x_505_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_505_, 0, v___y_480_);
lean_ctor_set(v___x_505_, 1, v___y_485_);
lean_ctor_set(v___x_505_, 2, v___y_479_);
lean_ctor_set(v___x_505_, 3, v___y_484_);
lean_ctor_set(v___x_505_, 4, v___x_504_);
lean_ctor_set_uint8(v___x_505_, sizeof(void*)*5, v___y_483_);
lean_ctor_set_uint8(v___x_505_, sizeof(void*)*5 + 1, v___y_482_);
lean_ctor_set_uint8(v___x_505_, sizeof(void*)*5 + 2, v_isSilent_472_);
v___x_506_ = l_Lean_MessageLog_add(v___x_505_, v_messages_497_);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 6, v___x_506_);
v___x_508_ = v___x_501_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_env_491_);
lean_ctor_set(v_reuseFailAlloc_512_, 1, v_nextMacroScope_492_);
lean_ctor_set(v_reuseFailAlloc_512_, 2, v_ngen_493_);
lean_ctor_set(v_reuseFailAlloc_512_, 3, v_auxDeclNGen_494_);
lean_ctor_set(v_reuseFailAlloc_512_, 4, v_traceState_495_);
lean_ctor_set(v_reuseFailAlloc_512_, 5, v_cache_496_);
lean_ctor_set(v_reuseFailAlloc_512_, 6, v___x_506_);
lean_ctor_set(v_reuseFailAlloc_512_, 7, v_infoState_498_);
lean_ctor_set(v_reuseFailAlloc_512_, 8, v_snapshotTasks_499_);
v___x_508_ = v_reuseFailAlloc_512_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_509_ = lean_st_ref_put(v___y_487_, v___x_508_);
v___x_510_ = lean_box(0);
v___x_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
return v___x_511_;
}
}
}
v___jp_514_:
{
lean_object* v_fileName_522_; lean_object* v_fileMap_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_539_; 
v_fileName_522_ = lean_ctor_get(v___y_516_, 0);
v_fileMap_523_ = lean_ctor_get(v___y_516_, 1);
v___x_524_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_470_);
v___x_525_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0_spec__1(v___x_524_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
v_a_526_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_539_ == 0)
{
v___x_528_ = v___x_525_;
v_isShared_529_ = v_isSharedCheck_539_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_525_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_539_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
lean_inc_ref_n(v_fileMap_523_, 2);
v___x_530_ = l_Lean_FileMap_toPosition(v_fileMap_523_, v___y_517_);
lean_dec(v___y_517_);
v___x_531_ = l_Lean_FileMap_toPosition(v_fileMap_523_, v___y_521_);
lean_dec(v___y_521_);
v___x_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
v___x_533_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___closed__0));
if (v___y_518_ == 0)
{
lean_del_object(v___x_528_);
lean_dec_ref(v___y_515_);
v___y_479_ = v___x_532_;
v___y_480_ = v_fileName_522_;
v___y_481_ = v_a_526_;
v___y_482_ = v___y_520_;
v___y_483_ = v___y_519_;
v___y_484_ = v___x_533_;
v___y_485_ = v___x_530_;
v___y_486_ = v___y_475_;
v___y_487_ = v___y_476_;
goto v___jp_478_;
}
else
{
uint8_t v___x_534_; 
lean_inc(v_a_526_);
v___x_534_ = l_Lean_MessageData_hasTag(v___y_515_, v_a_526_);
if (v___x_534_ == 0)
{
lean_object* v___x_535_; lean_object* v___x_537_; 
lean_dec_ref_known(v___x_532_, 1);
lean_dec_ref(v___x_530_);
lean_dec(v_a_526_);
v___x_535_ = lean_box(0);
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 0, v___x_535_);
v___x_537_ = v___x_528_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_535_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
else
{
lean_del_object(v___x_528_);
v___y_479_ = v___x_532_;
v___y_480_ = v_fileName_522_;
v___y_481_ = v_a_526_;
v___y_482_ = v___y_520_;
v___y_483_ = v___y_519_;
v___y_484_ = v___x_533_;
v___y_485_ = v___x_530_;
v___y_486_ = v___y_475_;
v___y_487_ = v___y_476_;
goto v___jp_478_;
}
}
}
}
v___jp_540_:
{
lean_object* v___x_548_; 
v___x_548_ = l_Lean_Syntax_getTailPos_x3f(v___y_546_, v___y_544_);
lean_dec(v___y_546_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_inc(v___y_547_);
v___y_515_ = v___y_541_;
v___y_516_ = v___y_542_;
v___y_517_ = v___y_547_;
v___y_518_ = v___y_545_;
v___y_519_ = v___y_544_;
v___y_520_ = v___y_543_;
v___y_521_ = v___y_547_;
goto v___jp_514_;
}
else
{
lean_object* v_val_549_; 
v_val_549_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_val_549_);
lean_dec_ref_known(v___x_548_, 1);
v___y_515_ = v___y_541_;
v___y_516_ = v___y_542_;
v___y_517_ = v___y_547_;
v___y_518_ = v___y_545_;
v___y_519_ = v___y_544_;
v___y_520_ = v___y_543_;
v___y_521_ = v_val_549_;
goto v___jp_514_;
}
}
v___jp_550_:
{
lean_object* v_ref_557_; lean_object* v___x_558_; 
v_ref_557_ = l_Lean_replaceRef(v_ref_469_, v___y_555_);
v___x_558_ = l_Lean_Syntax_getPos_x3f(v_ref_557_, v___y_554_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v___x_559_; 
v___x_559_ = lean_unsigned_to_nat(0u);
v___y_541_ = v___y_551_;
v___y_542_ = v___y_552_;
v___y_543_ = v___y_556_;
v___y_544_ = v___y_554_;
v___y_545_ = v___y_553_;
v___y_546_ = v_ref_557_;
v___y_547_ = v___x_559_;
goto v___jp_540_;
}
else
{
lean_object* v_val_560_; 
v_val_560_ = lean_ctor_get(v___x_558_, 0);
lean_inc(v_val_560_);
lean_dec_ref_known(v___x_558_, 1);
v___y_541_ = v___y_551_;
v___y_542_ = v___y_552_;
v___y_543_ = v___y_556_;
v___y_544_ = v___y_554_;
v___y_545_ = v___y_553_;
v___y_546_ = v_ref_557_;
v___y_547_ = v_val_560_;
goto v___jp_540_;
}
}
v___jp_562_:
{
if (v___y_568_ == 0)
{
v___y_551_ = v___y_564_;
v___y_552_ = v___y_563_;
v___y_553_ = v___y_565_;
v___y_554_ = v___y_567_;
v___y_555_ = v___y_566_;
v___y_556_ = v_severity_471_;
goto v___jp_550_;
}
else
{
v___y_551_ = v___y_564_;
v___y_552_ = v___y_563_;
v___y_553_ = v___y_565_;
v___y_554_ = v___y_567_;
v___y_555_ = v___y_566_;
v___y_556_ = v___x_561_;
goto v___jp_550_;
}
}
v___jp_569_:
{
if (v___y_570_ == 0)
{
lean_object* v_toCold_571_; lean_object* v_options_572_; lean_object* v_ref_573_; uint8_t v_suppressElabErrors_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___f_577_; uint8_t v___x_578_; uint8_t v___x_579_; 
v_toCold_571_ = lean_ctor_get(v___y_475_, 0);
v_options_572_ = lean_ctor_get(v___y_475_, 1);
v_ref_573_ = lean_ctor_get(v___y_475_, 4);
v_suppressElabErrors_574_ = lean_ctor_get_uint8(v___y_475_, sizeof(void*)*10 + 1);
v___x_575_ = lean_box(v_suppressElabErrors_574_);
v___x_576_ = lean_box(v___y_570_);
v___f_577_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_577_, 0, v___x_575_);
lean_closure_set(v___f_577_, 1, v___x_576_);
v___x_578_ = 1;
v___x_579_ = l_Lean_instBEqMessageSeverity_beq(v_severity_471_, v___x_578_);
if (v___x_579_ == 0)
{
v___y_563_ = v_toCold_571_;
v___y_564_ = v___f_577_;
v___y_565_ = v_suppressElabErrors_574_;
v___y_566_ = v_ref_573_;
v___y_567_ = v___y_570_;
v___y_568_ = v___x_579_;
goto v___jp_562_;
}
else
{
lean_object* v___x_580_; uint8_t v___x_581_; 
v___x_580_ = l_Lean_warningAsError;
v___x_581_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20_spec__22(v_options_572_, v___x_580_);
v___y_563_ = v_toCold_571_;
v___y_564_ = v___f_577_;
v___y_565_ = v_suppressElabErrors_574_;
v___y_566_ = v_ref_573_;
v___y_567_ = v___y_570_;
v___y_568_ = v___x_581_;
goto v___jp_562_;
}
}
else
{
lean_object* v___x_582_; lean_object* v___x_583_; 
lean_dec_ref(v_msgData_470_);
v___x_582_ = lean_box(0);
v___x_583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
return v___x_583_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___boxed(lean_object* v_ref_586_, lean_object* v_msgData_587_, lean_object* v_severity_588_, lean_object* v_isSilent_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_){
_start:
{
uint8_t v_severity_boxed_595_; uint8_t v_isSilent_boxed_596_; lean_object* v_res_597_; 
v_severity_boxed_595_ = lean_unbox(v_severity_588_);
v_isSilent_boxed_596_ = lean_unbox(v_isSilent_589_);
v_res_597_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg(v_ref_586_, v_msgData_587_, v_severity_boxed_595_, v_isSilent_boxed_596_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec(v_ref_586_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17(lean_object* v_ref_598_, lean_object* v_msgData_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
uint8_t v___x_608_; uint8_t v___x_609_; lean_object* v___x_610_; 
v___x_608_ = 1;
v___x_609_ = 0;
v___x_610_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg(v_ref_598_, v_msgData_599_, v___x_608_, v___x_609_, v___y_603_, v___y_604_, v___y_605_, v___y_606_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17___boxed(lean_object* v_ref_611_, lean_object* v_msgData_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17(v_ref_611_, v_msgData_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec(v___y_613_);
lean_dec(v_ref_611_);
return v_res_621_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11___closed__1(void){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11___closed__0));
v___x_624_ = l_Lean_stringToMessageData(v___x_623_);
return v___x_624_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11___closed__3(void){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11___closed__2));
v___x_627_ = l_Lean_stringToMessageData(v___x_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11(lean_object* v_linterOption_628_, lean_object* v_stx_629_, lean_object* v_msg_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
lean_object* v_name_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_657_; 
v_name_639_ = lean_ctor_get(v_linterOption_628_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v_linterOption_628_);
if (v_isSharedCheck_657_ == 0)
{
lean_object* v_unused_658_; 
v_unused_658_ = lean_ctor_get(v_linterOption_628_, 1);
lean_dec(v_unused_658_);
v___x_641_ = v_linterOption_628_;
v_isShared_642_ = v_isSharedCheck_657_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_name_639_);
lean_dec(v_linterOption_628_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_657_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_646_; 
v___x_643_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11___closed__1);
lean_inc(v_name_639_);
v___x_644_ = l_Lean_MessageData_ofName(v_name_639_);
if (v_isShared_642_ == 0)
{
lean_ctor_set_tag(v___x_641_, 7);
lean_ctor_set(v___x_641_, 1, v___x_644_);
lean_ctor_set(v___x_641_, 0, v___x_643_);
v___x_646_ = v___x_641_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v___x_643_);
lean_ctor_set(v_reuseFailAlloc_656_, 1, v___x_644_);
v___x_646_ = v_reuseFailAlloc_656_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v_disable_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_647_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11___closed__3);
v___x_648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_648_, 0, v___x_646_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
v_disable_649_ = l_Lean_MessageData_note(v___x_648_);
v___x_650_ = l_Lean_Linter_linterMessageTag;
v___x_651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_651_, 0, v_msg_630_);
lean_ctor_set(v___x_651_, 1, v_disable_649_);
v___x_652_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_650_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
v___x_653_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_653_, 0, v_name_639_);
lean_ctor_set(v___x_653_, 1, v___x_652_);
lean_inc(v_stx_629_);
v___x_654_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_654_, 0, v_stx_629_);
lean_ctor_set(v___x_654_, 1, v___x_653_);
v___x_655_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17(v_stx_629_, v___x_654_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
lean_dec(v_stx_629_);
return v___x_655_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11___boxed(lean_object* v_linterOption_659_, lean_object* v_stx_660_, lean_object* v_msg_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11(v_linterOption_659_, v_stx_660_, v_msg_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
lean_dec(v___y_662_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2(lean_object* v_linterOption_671_, lean_object* v_stx_672_, lean_object* v_msg_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v___x_682_; lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_693_; 
v___x_682_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__10(v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
v_a_683_ = lean_ctor_get(v___x_682_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_693_ == 0)
{
v___x_685_ = v___x_682_;
v_isShared_686_ = v_isSharedCheck_693_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_682_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_693_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
uint8_t v___x_687_; 
v___x_687_ = l_Lean_Linter_getLinterValue(v_linterOption_671_, v_a_683_);
lean_dec(v_a_683_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; lean_object* v___x_690_; 
lean_dec_ref(v_msg_673_);
lean_dec(v_stx_672_);
lean_dec_ref(v_linterOption_671_);
v___x_688_ = lean_box(0);
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 0, v___x_688_);
v___x_690_ = v___x_685_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v___x_688_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
else
{
lean_object* v___x_692_; 
lean_del_object(v___x_685_);
v___x_692_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11(v_linterOption_671_, v_stx_672_, v_msg_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
return v___x_692_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2___boxed(lean_object* v_linterOption_694_, lean_object* v_stx_695_, lean_object* v_msg_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2(v_linterOption_694_, v_stx_695_, v_msg_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec(v___y_697_);
return v_res_705_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_706_ = lean_box(0);
v___x_707_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_708_, 0, v___x_707_);
lean_ctor_set(v___x_708_, 1, v___x_706_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg(){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__0);
v___x_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___boxed(lean_object* v___y_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__3(lean_object* v_currNamespace_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_717_, 0, v_currNamespace_714_);
lean_ctor_set(v___x_717_, 1, v___y_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__3___boxed(lean_object* v_currNamespace_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__3(v_currNamespace_718_, v___y_719_, v___y_720_);
lean_dec_ref(v___y_719_);
return v_res_721_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_722_; double v___x_723_; 
v___x_722_ = lean_unsigned_to_nat(0u);
v___x_723_ = lean_float_of_nat(v___x_722_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg(lean_object* v_cls_726_, lean_object* v_msg_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v_ref_733_; lean_object* v___x_734_; lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_779_; 
v_ref_733_ = lean_ctor_get(v___y_730_, 4);
v___x_734_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0_spec__1(v_msg_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_);
v_a_735_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_779_ == 0)
{
v___x_737_ = v___x_734_;
v_isShared_738_ = v_isSharedCheck_779_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_734_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_779_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_739_; lean_object* v_traceState_740_; lean_object* v_env_741_; lean_object* v_nextMacroScope_742_; lean_object* v_ngen_743_; lean_object* v_auxDeclNGen_744_; lean_object* v_cache_745_; lean_object* v_messages_746_; lean_object* v_infoState_747_; lean_object* v_snapshotTasks_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_778_; 
v___x_739_ = lean_st_ref_take(v___y_731_);
v_traceState_740_ = lean_ctor_get(v___x_739_, 4);
v_env_741_ = lean_ctor_get(v___x_739_, 0);
v_nextMacroScope_742_ = lean_ctor_get(v___x_739_, 1);
v_ngen_743_ = lean_ctor_get(v___x_739_, 2);
v_auxDeclNGen_744_ = lean_ctor_get(v___x_739_, 3);
v_cache_745_ = lean_ctor_get(v___x_739_, 5);
v_messages_746_ = lean_ctor_get(v___x_739_, 6);
v_infoState_747_ = lean_ctor_get(v___x_739_, 7);
v_snapshotTasks_748_ = lean_ctor_get(v___x_739_, 8);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_778_ == 0)
{
v___x_750_ = v___x_739_;
v_isShared_751_ = v_isSharedCheck_778_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_snapshotTasks_748_);
lean_inc(v_infoState_747_);
lean_inc(v_messages_746_);
lean_inc(v_cache_745_);
lean_inc(v_traceState_740_);
lean_inc(v_auxDeclNGen_744_);
lean_inc(v_ngen_743_);
lean_inc(v_nextMacroScope_742_);
lean_inc(v_env_741_);
lean_dec(v___x_739_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_778_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
uint64_t v_tid_752_; lean_object* v_traces_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_777_; 
v_tid_752_ = lean_ctor_get_uint64(v_traceState_740_, sizeof(void*)*1);
v_traces_753_ = lean_ctor_get(v_traceState_740_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v_traceState_740_);
if (v_isSharedCheck_777_ == 0)
{
v___x_755_ = v_traceState_740_;
v_isShared_756_ = v_isSharedCheck_777_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_traces_753_);
lean_dec(v_traceState_740_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_777_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_757_; double v___x_758_; uint8_t v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_767_; 
v___x_757_ = lean_box(0);
v___x_758_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___closed__0);
v___x_759_ = 0;
v___x_760_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___closed__0));
v___x_761_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_761_, 0, v_cls_726_);
lean_ctor_set(v___x_761_, 1, v___x_757_);
lean_ctor_set(v___x_761_, 2, v___x_760_);
lean_ctor_set_float(v___x_761_, sizeof(void*)*3, v___x_758_);
lean_ctor_set_float(v___x_761_, sizeof(void*)*3 + 8, v___x_758_);
lean_ctor_set_uint8(v___x_761_, sizeof(void*)*3 + 16, v___x_759_);
v___x_762_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___closed__1));
v___x_763_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_763_, 0, v___x_761_);
lean_ctor_set(v___x_763_, 1, v_a_735_);
lean_ctor_set(v___x_763_, 2, v___x_762_);
lean_inc(v_ref_733_);
v___x_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_764_, 0, v_ref_733_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
v___x_765_ = l_Lean_PersistentArray_push___redArg(v_traces_753_, v___x_764_);
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 0, v___x_765_);
v___x_767_ = v___x_755_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_765_);
lean_ctor_set_uint64(v_reuseFailAlloc_776_, sizeof(void*)*1, v_tid_752_);
v___x_767_ = v_reuseFailAlloc_776_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
lean_object* v___x_769_; 
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 4, v___x_767_);
v___x_769_ = v___x_750_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_env_741_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v_nextMacroScope_742_);
lean_ctor_set(v_reuseFailAlloc_775_, 2, v_ngen_743_);
lean_ctor_set(v_reuseFailAlloc_775_, 3, v_auxDeclNGen_744_);
lean_ctor_set(v_reuseFailAlloc_775_, 4, v___x_767_);
lean_ctor_set(v_reuseFailAlloc_775_, 5, v_cache_745_);
lean_ctor_set(v_reuseFailAlloc_775_, 6, v_messages_746_);
lean_ctor_set(v_reuseFailAlloc_775_, 7, v_infoState_747_);
lean_ctor_set(v_reuseFailAlloc_775_, 8, v_snapshotTasks_748_);
v___x_769_ = v_reuseFailAlloc_775_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_773_; 
v___x_770_ = lean_st_ref_put(v___y_731_, v___x_769_);
v___x_771_ = lean_box(0);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 0, v___x_771_);
v___x_773_ = v___x_737_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_771_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___boxed(lean_object* v_cls_780_, lean_object* v_msg_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg(v_cls_780_, v_msg_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4(lean_object* v_as_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
if (lean_obj_tag(v_as_790_) == 0)
{
lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_799_ = lean_box(0);
v___x_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_800_, 0, v___x_799_);
return v___x_800_;
}
else
{
lean_object* v_options_801_; uint8_t v_hasTrace_802_; 
v_options_801_ = lean_ctor_get(v___y_796_, 1);
v_hasTrace_802_ = lean_ctor_get_uint8(v_options_801_, sizeof(void*)*1);
if (v_hasTrace_802_ == 0)
{
lean_object* v_tail_803_; 
v_tail_803_ = lean_ctor_get(v_as_790_, 1);
lean_inc(v_tail_803_);
lean_dec_ref_known(v_as_790_, 2);
v_as_790_ = v_tail_803_;
goto _start;
}
else
{
lean_object* v_head_805_; lean_object* v_toCold_806_; lean_object* v_tail_807_; lean_object* v_fst_808_; lean_object* v_snd_809_; lean_object* v_inheritedTraceOptions_810_; lean_object* v___x_811_; lean_object* v___x_812_; uint8_t v___x_813_; 
v_head_805_ = lean_ctor_get(v_as_790_, 0);
v_toCold_806_ = lean_ctor_get(v___y_796_, 0);
lean_inc(v_head_805_);
v_tail_807_ = lean_ctor_get(v_as_790_, 1);
lean_inc(v_tail_807_);
lean_dec_ref_known(v_as_790_, 2);
v_fst_808_ = lean_ctor_get(v_head_805_, 0);
lean_inc_n(v_fst_808_, 2);
v_snd_809_ = lean_ctor_get(v_head_805_, 1);
lean_inc(v_snd_809_);
lean_dec(v_head_805_);
v_inheritedTraceOptions_810_ = lean_ctor_get(v_toCold_806_, 4);
v___x_811_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4___closed__0));
v___x_812_ = l_Lean_Name_append(v___x_811_, v_fst_808_);
v___x_813_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_810_, v_options_801_, v___x_812_);
lean_dec(v___x_812_);
if (v___x_813_ == 0)
{
lean_dec(v_snd_809_);
lean_dec(v_fst_808_);
v_as_790_ = v_tail_807_;
goto _start;
}
else
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_815_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_815_, 0, v_snd_809_);
v___x_816_ = l_Lean_MessageData_ofFormat(v___x_815_);
v___x_817_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg(v_fst_808_, v___x_816_, v___y_794_, v___y_795_, v___y_796_, v___y_797_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_dec_ref_known(v___x_817_, 1);
v_as_790_ = v_tail_807_;
goto _start;
}
else
{
lean_dec(v_tail_807_);
return v___x_817_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4___boxed(lean_object* v_as_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4(v_as_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec(v___y_820_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__2(lean_object* v_env_829_, lean_object* v_currNamespace_830_, lean_object* v_openDecls_831_, lean_object* v_n_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_835_ = l_Lean_ResolveName_resolveNamespace(v_env_829_, v_currNamespace_830_, v_openDecls_831_, v_n_832_);
v___x_836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_836_, 0, v___x_835_);
lean_ctor_set(v___x_836_, 1, v___y_834_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__2___boxed(lean_object* v_env_837_, lean_object* v_currNamespace_838_, lean_object* v_openDecls_839_, lean_object* v_n_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__2(v_env_837_, v_currNamespace_838_, v_openDecls_839_, v_n_840_, v___y_841_, v___y_842_);
lean_dec_ref(v___y_841_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__1(lean_object* v_env_844_, lean_object* v_declName_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
uint8_t v___x_848_; lean_object* v_env_849_; lean_object* v___x_850_; uint8_t v___x_851_; uint8_t v___x_852_; 
v___x_848_ = 0;
v_env_849_ = l_Lean_Environment_setExporting(v_env_844_, v___x_848_);
lean_inc(v_declName_845_);
v___x_850_ = l_Lean_mkPrivateName(v_env_849_, v_declName_845_);
v___x_851_ = 1;
lean_inc_ref(v_env_849_);
v___x_852_ = l_Lean_Environment_contains(v_env_849_, v___x_850_, v___x_851_);
if (v___x_852_ == 0)
{
lean_object* v___x_853_; uint8_t v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_853_ = l_Lean_privateToUserName(v_declName_845_);
v___x_854_ = l_Lean_Environment_contains(v_env_849_, v___x_853_, v___x_851_);
v___x_855_ = lean_box(v___x_854_);
v___x_856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
lean_ctor_set(v___x_856_, 1, v___y_847_);
return v___x_856_;
}
else
{
lean_object* v___x_857_; lean_object* v___x_858_; 
lean_dec_ref(v_env_849_);
lean_dec(v_declName_845_);
v___x_857_ = lean_box(v___x_852_);
v___x_858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
lean_ctor_set(v___x_858_, 1, v___y_847_);
return v___x_858_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__1___boxed(lean_object* v_env_859_, lean_object* v_declName_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__1(v_env_859_, v_declName_860_, v___y_861_, v___y_862_);
lean_dec_ref(v___y_861_);
return v_res_863_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16_spec__20___redArg(lean_object* v_keys_864_, lean_object* v_i_865_, lean_object* v_k_866_){
_start:
{
lean_object* v___x_867_; uint8_t v___x_868_; 
v___x_867_ = lean_array_get_size(v_keys_864_);
v___x_868_ = lean_nat_dec_lt(v_i_865_, v___x_867_);
if (v___x_868_ == 0)
{
lean_dec(v_i_865_);
return v___x_868_;
}
else
{
lean_object* v_k_x27_869_; uint8_t v___x_870_; 
v_k_x27_869_ = lean_array_fget_borrowed(v_keys_864_, v_i_865_);
v___x_870_ = l_Lean_instBEqExtraModUse_beq(v_k_866_, v_k_x27_869_);
if (v___x_870_ == 0)
{
lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_871_ = lean_unsigned_to_nat(1u);
v___x_872_ = lean_nat_add(v_i_865_, v___x_871_);
lean_dec(v_i_865_);
v_i_865_ = v___x_872_;
goto _start;
}
else
{
lean_dec(v_i_865_);
return v___x_868_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16_spec__20___redArg___boxed(lean_object* v_keys_874_, lean_object* v_i_875_, lean_object* v_k_876_){
_start:
{
uint8_t v_res_877_; lean_object* v_r_878_; 
v_res_877_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16_spec__20___redArg(v_keys_874_, v_i_875_, v_k_876_);
lean_dec_ref(v_k_876_);
lean_dec_ref(v_keys_874_);
v_r_878_ = lean_box(v_res_877_);
return v_r_878_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16___redArg(lean_object* v_x_879_, size_t v_x_880_, lean_object* v_x_881_){
_start:
{
if (lean_obj_tag(v_x_879_) == 0)
{
lean_object* v_es_882_; lean_object* v___x_883_; size_t v___x_884_; size_t v___x_885_; lean_object* v_j_886_; lean_object* v___x_887_; 
v_es_882_ = lean_ctor_get(v_x_879_, 0);
v___x_883_ = lean_box(2);
v___x_884_ = ((size_t)31ULL);
v___x_885_ = lean_usize_land(v_x_880_, v___x_884_);
v_j_886_ = lean_usize_to_nat(v___x_885_);
v___x_887_ = lean_array_get_borrowed(v___x_883_, v_es_882_, v_j_886_);
lean_dec(v_j_886_);
switch(lean_obj_tag(v___x_887_))
{
case 0:
{
lean_object* v_key_888_; uint8_t v___x_889_; 
v_key_888_ = lean_ctor_get(v___x_887_, 0);
v___x_889_ = l_Lean_instBEqExtraModUse_beq(v_x_881_, v_key_888_);
return v___x_889_;
}
case 1:
{
lean_object* v_node_890_; size_t v___x_891_; size_t v___x_892_; 
v_node_890_ = lean_ctor_get(v___x_887_, 0);
v___x_891_ = ((size_t)5ULL);
v___x_892_ = lean_usize_shift_right(v_x_880_, v___x_891_);
v_x_879_ = v_node_890_;
v_x_880_ = v___x_892_;
goto _start;
}
default: 
{
uint8_t v___x_894_; 
v___x_894_ = 0;
return v___x_894_;
}
}
}
else
{
lean_object* v_ks_895_; lean_object* v___x_896_; uint8_t v___x_897_; 
v_ks_895_ = lean_ctor_get(v_x_879_, 0);
v___x_896_ = lean_unsigned_to_nat(0u);
v___x_897_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16_spec__20___redArg(v_ks_895_, v___x_896_, v_x_881_);
return v___x_897_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16___redArg___boxed(lean_object* v_x_898_, lean_object* v_x_899_, lean_object* v_x_900_){
_start:
{
size_t v_x_36566__boxed_901_; uint8_t v_res_902_; lean_object* v_r_903_; 
v_x_36566__boxed_901_ = lean_unbox_usize(v_x_899_);
lean_dec(v_x_899_);
v_res_902_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16___redArg(v_x_898_, v_x_36566__boxed_901_, v_x_900_);
lean_dec_ref(v_x_900_);
lean_dec_ref(v_x_898_);
v_r_903_ = lean_box(v_res_902_);
return v_r_903_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9___redArg(lean_object* v_x_904_, lean_object* v_x_905_){
_start:
{
uint64_t v___x_906_; size_t v___x_907_; uint8_t v___x_908_; 
v___x_906_ = l_Lean_instHashableExtraModUse_hash(v_x_905_);
v___x_907_ = lean_uint64_to_usize(v___x_906_);
v___x_908_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16___redArg(v_x_904_, v___x_907_, v_x_905_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9___redArg___boxed(lean_object* v_x_909_, lean_object* v_x_910_){
_start:
{
uint8_t v_res_911_; lean_object* v_r_912_; 
v_res_911_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9___redArg(v_x_909_, v_x_910_);
lean_dec_ref(v_x_910_);
lean_dec_ref(v_x_909_);
v_r_912_ = lean_box(v_res_911_);
return v_r_912_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__2(void){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_915_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__1));
v___x_916_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__0));
v___x_917_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_916_, v___x_915_);
return v___x_917_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_918_; 
v___x_918_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_918_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__4(void){
_start:
{
lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_919_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__3);
v___x_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_920_, 0, v___x_919_);
return v___x_920_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__5(void){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_921_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__4);
v___x_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_921_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
return v___x_922_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__6(void){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_923_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__4);
v___x_924_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_924_, 0, v___x_923_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
lean_ctor_set(v___x_924_, 2, v___x_923_);
lean_ctor_set(v___x_924_, 3, v___x_923_);
lean_ctor_set(v___x_924_, 4, v___x_923_);
lean_ctor_set(v___x_924_, 5, v___x_923_);
return v___x_924_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__10(void){
_start:
{
lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_929_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__9));
v___x_930_ = l_Lean_stringToMessageData(v___x_929_);
return v___x_930_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__12(void){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_932_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__11));
v___x_933_ = l_Lean_stringToMessageData(v___x_932_);
return v___x_933_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__13(void){
_start:
{
lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_934_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___closed__0));
v___x_935_ = l_Lean_stringToMessageData(v___x_934_);
return v___x_935_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__14(void){
_start:
{
lean_object* v_cls_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v_cls_936_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__8));
v___x_937_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4___closed__0));
v___x_938_ = l_Lean_Name_append(v___x_937_, v_cls_936_);
return v___x_938_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__16(void){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_940_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__15));
v___x_941_ = l_Lean_stringToMessageData(v___x_940_);
return v___x_941_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__18(void){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_943_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__17));
v___x_944_ = l_Lean_stringToMessageData(v___x_943_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4(lean_object* v_mod_949_, uint8_t v_isMeta_950_, lean_object* v_hint_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
lean_object* v___x_960_; lean_object* v_env_961_; uint8_t v_isExporting_962_; lean_object* v___x_963_; lean_object* v_env_964_; lean_object* v___x_965_; lean_object* v_entry_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___x_1012_; uint8_t v___x_1013_; 
v___x_960_ = lean_st_ref_get(v___y_958_);
v_env_961_ = lean_ctor_get(v___x_960_, 0);
lean_inc_ref(v_env_961_);
lean_dec(v___x_960_);
v_isExporting_962_ = lean_ctor_get_uint8(v_env_961_, sizeof(void*)*8);
lean_dec_ref(v_env_961_);
v___x_963_ = lean_st_ref_get(v___y_958_);
v_env_964_ = lean_ctor_get(v___x_963_, 0);
lean_inc_ref(v_env_964_);
lean_dec(v___x_963_);
v___x_965_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__2);
lean_inc(v_mod_949_);
v_entry_966_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_966_, 0, v_mod_949_);
lean_ctor_set_uint8(v_entry_966_, sizeof(void*)*1, v_isExporting_962_);
lean_ctor_set_uint8(v_entry_966_, sizeof(void*)*1 + 1, v_isMeta_950_);
v___x_967_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_968_ = lean_box(1);
v___x_969_ = lean_box(0);
v___x_1012_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_965_, v___x_967_, v_env_964_, v___x_968_, v___x_969_);
v___x_1013_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9___redArg(v___x_1012_, v_entry_966_);
lean_dec(v___x_1012_);
if (v___x_1013_ == 0)
{
lean_object* v_options_1014_; uint8_t v_hasTrace_1015_; 
v_options_1014_ = lean_ctor_get(v___y_957_, 1);
v_hasTrace_1015_ = lean_ctor_get_uint8(v_options_1014_, sizeof(void*)*1);
if (v_hasTrace_1015_ == 0)
{
lean_dec(v_hint_951_);
lean_dec(v_mod_949_);
v___y_971_ = v___y_956_;
v___y_972_ = v___y_958_;
goto v___jp_970_;
}
else
{
lean_object* v_toCold_1016_; lean_object* v_inheritedTraceOptions_1017_; lean_object* v_cls_1018_; lean_object* v___y_1020_; lean_object* v___y_1021_; lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v___x_1038_; uint8_t v___x_1039_; 
v_toCold_1016_ = lean_ctor_get(v___y_957_, 0);
v_inheritedTraceOptions_1017_ = lean_ctor_get(v_toCold_1016_, 4);
v_cls_1018_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__8));
v___x_1038_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__14);
v___x_1039_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1017_, v_options_1014_, v___x_1038_);
if (v___x_1039_ == 0)
{
lean_dec(v_hint_951_);
lean_dec(v_mod_949_);
v___y_971_ = v___y_956_;
v___y_972_ = v___y_958_;
goto v___jp_970_;
}
else
{
lean_object* v___x_1040_; lean_object* v___y_1042_; 
v___x_1040_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__16);
if (v_isExporting_962_ == 0)
{
lean_object* v___x_1049_; 
v___x_1049_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__21));
v___y_1042_ = v___x_1049_;
goto v___jp_1041_;
}
else
{
lean_object* v___x_1050_; 
v___x_1050_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__22));
v___y_1042_ = v___x_1050_;
goto v___jp_1041_;
}
v___jp_1041_:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
lean_inc_ref(v___y_1042_);
v___x_1043_ = l_Lean_stringToMessageData(v___y_1042_);
v___x_1044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1040_);
lean_ctor_set(v___x_1044_, 1, v___x_1043_);
v___x_1045_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__18);
v___x_1046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1044_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
if (v_isMeta_950_ == 0)
{
lean_object* v___x_1047_; 
v___x_1047_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__19));
v___y_1025_ = v___x_1046_;
v___y_1026_ = v___x_1047_;
goto v___jp_1024_;
}
else
{
lean_object* v___x_1048_; 
v___x_1048_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__20));
v___y_1025_ = v___x_1046_;
v___y_1026_ = v___x_1048_;
goto v___jp_1024_;
}
}
}
v___jp_1019_:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___y_1020_);
lean_ctor_set(v___x_1022_, 1, v___y_1021_);
v___x_1023_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg(v_cls_1018_, v___x_1022_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_dec_ref_known(v___x_1023_, 1);
v___y_971_ = v___y_956_;
v___y_972_ = v___y_958_;
goto v___jp_970_;
}
else
{
lean_dec_ref_known(v_entry_966_, 1);
return v___x_1023_;
}
}
v___jp_1024_:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; uint8_t v___x_1033_; 
lean_inc_ref(v___y_1026_);
v___x_1027_ = l_Lean_stringToMessageData(v___y_1026_);
v___x_1028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___y_1025_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__10);
v___x_1030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1028_);
lean_ctor_set(v___x_1030_, 1, v___x_1029_);
v___x_1031_ = l_Lean_MessageData_ofName(v_mod_949_);
v___x_1032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1030_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
v___x_1033_ = l_Lean_Name_isAnonymous(v_hint_951_);
if (v___x_1033_ == 0)
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1034_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__12);
v___x_1035_ = l_Lean_MessageData_ofName(v_hint_951_);
v___x_1036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1034_);
lean_ctor_set(v___x_1036_, 1, v___x_1035_);
v___y_1020_ = v___x_1032_;
v___y_1021_ = v___x_1036_;
goto v___jp_1019_;
}
else
{
lean_object* v___x_1037_; 
lean_dec(v_hint_951_);
v___x_1037_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__13);
v___y_1020_ = v___x_1032_;
v___y_1021_ = v___x_1037_;
goto v___jp_1019_;
}
}
}
}
else
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
lean_dec_ref_known(v_entry_966_, 1);
lean_dec(v_hint_951_);
lean_dec(v_mod_949_);
v___x_1051_ = lean_box(0);
v___x_1052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
return v___x_1052_;
}
v___jp_970_:
{
lean_object* v___x_973_; lean_object* v_toEnvExtension_974_; lean_object* v_env_975_; lean_object* v_nextMacroScope_976_; lean_object* v_ngen_977_; lean_object* v_auxDeclNGen_978_; lean_object* v_traceState_979_; lean_object* v_messages_980_; lean_object* v_infoState_981_; lean_object* v_snapshotTasks_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_1010_; 
v___x_973_ = lean_st_ref_take(v___y_972_);
v_toEnvExtension_974_ = lean_ctor_get(v___x_967_, 0);
v_env_975_ = lean_ctor_get(v___x_973_, 0);
v_nextMacroScope_976_ = lean_ctor_get(v___x_973_, 1);
v_ngen_977_ = lean_ctor_get(v___x_973_, 2);
v_auxDeclNGen_978_ = lean_ctor_get(v___x_973_, 3);
v_traceState_979_ = lean_ctor_get(v___x_973_, 4);
v_messages_980_ = lean_ctor_get(v___x_973_, 6);
v_infoState_981_ = lean_ctor_get(v___x_973_, 7);
v_snapshotTasks_982_ = lean_ctor_get(v___x_973_, 8);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_1010_ == 0)
{
lean_object* v_unused_1011_; 
v_unused_1011_ = lean_ctor_get(v___x_973_, 5);
lean_dec(v_unused_1011_);
v___x_984_ = v___x_973_;
v_isShared_985_ = v_isSharedCheck_1010_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_snapshotTasks_982_);
lean_inc(v_infoState_981_);
lean_inc(v_messages_980_);
lean_inc(v_traceState_979_);
lean_inc(v_auxDeclNGen_978_);
lean_inc(v_ngen_977_);
lean_inc(v_nextMacroScope_976_);
lean_inc(v_env_975_);
lean_dec(v___x_973_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_1010_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v_asyncMode_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_990_; 
v_asyncMode_986_ = lean_ctor_get(v_toEnvExtension_974_, 2);
v___x_987_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_967_, v_env_975_, v_entry_966_, v_asyncMode_986_, v___x_969_);
v___x_988_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__5);
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 5, v___x_988_);
lean_ctor_set(v___x_984_, 0, v___x_987_);
v___x_990_ = v___x_984_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v___x_987_);
lean_ctor_set(v_reuseFailAlloc_1009_, 1, v_nextMacroScope_976_);
lean_ctor_set(v_reuseFailAlloc_1009_, 2, v_ngen_977_);
lean_ctor_set(v_reuseFailAlloc_1009_, 3, v_auxDeclNGen_978_);
lean_ctor_set(v_reuseFailAlloc_1009_, 4, v_traceState_979_);
lean_ctor_set(v_reuseFailAlloc_1009_, 5, v___x_988_);
lean_ctor_set(v_reuseFailAlloc_1009_, 6, v_messages_980_);
lean_ctor_set(v_reuseFailAlloc_1009_, 7, v_infoState_981_);
lean_ctor_set(v_reuseFailAlloc_1009_, 8, v_snapshotTasks_982_);
v___x_990_ = v_reuseFailAlloc_1009_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v_mctx_993_; lean_object* v_zetaDeltaFVarIds_994_; lean_object* v_postponed_995_; lean_object* v_diag_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1007_; 
v___x_991_ = lean_st_ref_put(v___y_972_, v___x_990_);
v___x_992_ = lean_st_ref_take(v___y_971_);
v_mctx_993_ = lean_ctor_get(v___x_992_, 0);
v_zetaDeltaFVarIds_994_ = lean_ctor_get(v___x_992_, 2);
v_postponed_995_ = lean_ctor_get(v___x_992_, 3);
v_diag_996_ = lean_ctor_get(v___x_992_, 4);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1007_ == 0)
{
lean_object* v_unused_1008_; 
v_unused_1008_ = lean_ctor_get(v___x_992_, 1);
lean_dec(v_unused_1008_);
v___x_998_ = v___x_992_;
v_isShared_999_ = v_isSharedCheck_1007_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_diag_996_);
lean_inc(v_postponed_995_);
lean_inc(v_zetaDeltaFVarIds_994_);
lean_inc(v_mctx_993_);
lean_dec(v___x_992_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1007_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1000_; lean_object* v___x_1002_; 
v___x_1000_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__6);
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 1, v___x_1000_);
v___x_1002_ = v___x_998_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_mctx_993_);
lean_ctor_set(v_reuseFailAlloc_1006_, 1, v___x_1000_);
lean_ctor_set(v_reuseFailAlloc_1006_, 2, v_zetaDeltaFVarIds_994_);
lean_ctor_set(v_reuseFailAlloc_1006_, 3, v_postponed_995_);
lean_ctor_set(v_reuseFailAlloc_1006_, 4, v_diag_996_);
v___x_1002_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1003_ = lean_st_ref_put(v___y_971_, v___x_1002_);
v___x_1004_ = lean_box(0);
v___x_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
return v___x_1005_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___boxed(lean_object* v_mod_1053_, lean_object* v_isMeta_1054_, lean_object* v_hint_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
uint8_t v_isMeta_boxed_1064_; lean_object* v_res_1065_; 
v_isMeta_boxed_1064_ = lean_unbox(v_isMeta_1054_);
v_res_1065_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4(v_mod_1053_, v_isMeta_boxed_1064_, v_hint_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec(v___y_1056_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6_spec__12___redArg(lean_object* v_a_1066_, lean_object* v_x_1067_){
_start:
{
if (lean_obj_tag(v_x_1067_) == 0)
{
lean_object* v___x_1068_; 
v___x_1068_ = lean_box(0);
return v___x_1068_;
}
else
{
lean_object* v_key_1069_; lean_object* v_value_1070_; lean_object* v_tail_1071_; uint8_t v___x_1072_; 
v_key_1069_ = lean_ctor_get(v_x_1067_, 0);
v_value_1070_ = lean_ctor_get(v_x_1067_, 1);
v_tail_1071_ = lean_ctor_get(v_x_1067_, 2);
v___x_1072_ = lean_name_eq(v_key_1069_, v_a_1066_);
if (v___x_1072_ == 0)
{
v_x_1067_ = v_tail_1071_;
goto _start;
}
else
{
lean_object* v___x_1074_; 
lean_inc(v_value_1070_);
v___x_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1074_, 0, v_value_1070_);
return v___x_1074_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6_spec__12___redArg___boxed(lean_object* v_a_1075_, lean_object* v_x_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6_spec__12___redArg(v_a_1075_, v_x_1076_);
lean_dec(v_x_1076_);
lean_dec(v_a_1075_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6___redArg(lean_object* v_m_1078_, lean_object* v_a_1079_){
_start:
{
lean_object* v_buckets_1080_; lean_object* v___x_1081_; uint64_t v___y_1083_; 
v_buckets_1080_ = lean_ctor_get(v_m_1078_, 1);
v___x_1081_ = lean_array_get_size(v_buckets_1080_);
if (lean_obj_tag(v_a_1079_) == 0)
{
uint64_t v___x_1097_; 
v___x_1097_ = 1723ULL;
v___y_1083_ = v___x_1097_;
goto v___jp_1082_;
}
else
{
uint64_t v_hash_1098_; 
v_hash_1098_ = lean_ctor_get_uint64(v_a_1079_, sizeof(void*)*2);
v___y_1083_ = v_hash_1098_;
goto v___jp_1082_;
}
v___jp_1082_:
{
uint64_t v___x_1084_; uint64_t v___x_1085_; uint64_t v_fold_1086_; uint64_t v___x_1087_; uint64_t v___x_1088_; uint64_t v___x_1089_; size_t v___x_1090_; size_t v___x_1091_; size_t v___x_1092_; size_t v___x_1093_; size_t v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1084_ = 32ULL;
v___x_1085_ = lean_uint64_shift_right(v___y_1083_, v___x_1084_);
v_fold_1086_ = lean_uint64_xor(v___y_1083_, v___x_1085_);
v___x_1087_ = 16ULL;
v___x_1088_ = lean_uint64_shift_right(v_fold_1086_, v___x_1087_);
v___x_1089_ = lean_uint64_xor(v_fold_1086_, v___x_1088_);
v___x_1090_ = lean_uint64_to_usize(v___x_1089_);
v___x_1091_ = lean_usize_of_nat(v___x_1081_);
v___x_1092_ = ((size_t)1ULL);
v___x_1093_ = lean_usize_sub(v___x_1091_, v___x_1092_);
v___x_1094_ = lean_usize_land(v___x_1090_, v___x_1093_);
v___x_1095_ = lean_array_uget_borrowed(v_buckets_1080_, v___x_1094_);
v___x_1096_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6_spec__12___redArg(v_a_1079_, v___x_1095_);
return v___x_1096_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6___redArg___boxed(lean_object* v_m_1099_, lean_object* v_a_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6___redArg(v_m_1099_, v_a_1100_);
lean_dec(v_a_1100_);
lean_dec_ref(v_m_1099_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__5(lean_object* v___x_1102_, lean_object* v_declName_1103_, lean_object* v_as_1104_, size_t v_sz_1105_, size_t v_i_1106_, lean_object* v_b_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
uint8_t v___x_1116_; 
v___x_1116_ = lean_usize_dec_lt(v_i_1106_, v_sz_1105_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1117_; 
lean_dec(v_declName_1103_);
v___x_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1117_, 0, v_b_1107_);
return v___x_1117_;
}
else
{
lean_object* v___x_1118_; lean_object* v_modules_1119_; lean_object* v___x_1120_; lean_object* v_a_1121_; lean_object* v___x_1122_; lean_object* v_toImport_1123_; lean_object* v_module_1124_; uint8_t v___x_1125_; lean_object* v___x_1126_; 
v___x_1118_ = l_Lean_Environment_header(v___x_1102_);
v_modules_1119_ = lean_ctor_get(v___x_1118_, 3);
lean_inc_ref(v_modules_1119_);
lean_dec_ref(v___x_1118_);
v___x_1120_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1121_ = lean_array_uget_borrowed(v_as_1104_, v_i_1106_);
v___x_1122_ = lean_array_get(v___x_1120_, v_modules_1119_, v_a_1121_);
lean_dec_ref(v_modules_1119_);
v_toImport_1123_ = lean_ctor_get(v___x_1122_, 0);
lean_inc_ref(v_toImport_1123_);
lean_dec(v___x_1122_);
v_module_1124_ = lean_ctor_get(v_toImport_1123_, 0);
lean_inc(v_module_1124_);
lean_dec_ref(v_toImport_1123_);
v___x_1125_ = 0;
lean_inc(v_declName_1103_);
v___x_1126_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4(v_module_1124_, v___x_1125_, v_declName_1103_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v___x_1127_; size_t v___x_1128_; size_t v___x_1129_; 
lean_dec_ref_known(v___x_1126_, 1);
v___x_1127_ = lean_box(0);
v___x_1128_ = ((size_t)1ULL);
v___x_1129_ = lean_usize_add(v_i_1106_, v___x_1128_);
v_i_1106_ = v___x_1129_;
v_b_1107_ = v___x_1127_;
goto _start;
}
else
{
lean_dec(v_declName_1103_);
return v___x_1126_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__5___boxed(lean_object* v___x_1131_, lean_object* v_declName_1132_, lean_object* v_as_1133_, lean_object* v_sz_1134_, lean_object* v_i_1135_, lean_object* v_b_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
size_t v_sz_boxed_1145_; size_t v_i_boxed_1146_; lean_object* v_res_1147_; 
v_sz_boxed_1145_ = lean_unbox_usize(v_sz_1134_);
lean_dec(v_sz_1134_);
v_i_boxed_1146_ = lean_unbox_usize(v_i_1135_);
lean_dec(v_i_1135_);
v_res_1147_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__5(v___x_1131_, v_declName_1132_, v_as_1133_, v_sz_boxed_1145_, v_i_boxed_1146_, v_b_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
lean_dec(v___y_1137_);
lean_dec_ref(v_as_1133_);
lean_dec_ref(v___x_1131_);
return v_res_1147_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1150_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___closed__1));
v___x_1151_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___closed__0));
v___x_1152_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1151_, v___x_1150_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2(lean_object* v_declName_1155_, uint8_t v_isMeta_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v___x_1165_; lean_object* v_env_1169_; lean_object* v___y_1171_; lean_object* v___x_1184_; 
v___x_1165_ = lean_st_ref_get(v___y_1163_);
v_env_1169_ = lean_ctor_get(v___x_1165_, 0);
lean_inc_ref(v_env_1169_);
lean_dec(v___x_1165_);
v___x_1184_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1169_, v_declName_1155_);
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_dec_ref(v_env_1169_);
lean_dec(v_declName_1155_);
goto v___jp_1166_;
}
else
{
lean_object* v_val_1185_; lean_object* v___x_1186_; lean_object* v_modules_1187_; lean_object* v___x_1188_; uint8_t v___x_1189_; 
v_val_1185_ = lean_ctor_get(v___x_1184_, 0);
lean_inc(v_val_1185_);
lean_dec_ref_known(v___x_1184_, 1);
v___x_1186_ = l_Lean_Environment_header(v_env_1169_);
v_modules_1187_ = lean_ctor_get(v___x_1186_, 3);
lean_inc_ref(v_modules_1187_);
lean_dec_ref(v___x_1186_);
v___x_1188_ = lean_array_get_size(v_modules_1187_);
v___x_1189_ = lean_nat_dec_lt(v_val_1185_, v___x_1188_);
if (v___x_1189_ == 0)
{
lean_dec_ref(v_modules_1187_);
lean_dec(v_val_1185_);
lean_dec_ref(v_env_1169_);
lean_dec(v_declName_1155_);
goto v___jp_1166_;
}
else
{
lean_object* v___x_1190_; lean_object* v_env_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; uint8_t v___y_1195_; 
v___x_1190_ = lean_st_ref_get(v___y_1163_);
v_env_1191_ = lean_ctor_get(v___x_1190_, 0);
lean_inc_ref(v_env_1191_);
lean_dec(v___x_1190_);
v___x_1192_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___closed__2);
v___x_1193_ = lean_array_fget(v_modules_1187_, v_val_1185_);
lean_dec(v_val_1185_);
lean_dec_ref(v_modules_1187_);
if (v_isMeta_1156_ == 0)
{
lean_dec_ref(v_env_1191_);
v___y_1195_ = v_isMeta_1156_;
goto v___jp_1194_;
}
else
{
uint8_t v___x_1206_; 
lean_inc(v_declName_1155_);
v___x_1206_ = l_Lean_isMarkedMeta(v_env_1191_, v_declName_1155_);
if (v___x_1206_ == 0)
{
v___y_1195_ = v_isMeta_1156_;
goto v___jp_1194_;
}
else
{
uint8_t v___x_1207_; 
v___x_1207_ = 0;
v___y_1195_ = v___x_1207_;
goto v___jp_1194_;
}
}
v___jp_1194_:
{
lean_object* v_toImport_1196_; lean_object* v_module_1197_; lean_object* v___x_1198_; 
v_toImport_1196_ = lean_ctor_get(v___x_1193_, 0);
lean_inc_ref(v_toImport_1196_);
lean_dec(v___x_1193_);
v_module_1197_ = lean_ctor_get(v_toImport_1196_, 0);
lean_inc(v_module_1197_);
lean_dec_ref(v_toImport_1196_);
lean_inc(v_declName_1155_);
v___x_1198_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4(v_module_1197_, v___y_1195_, v_declName_1155_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
lean_dec_ref_known(v___x_1198_, 1);
v___x_1199_ = l_Lean_indirectModUseExt;
v___x_1200_ = lean_box(1);
v___x_1201_ = lean_box(0);
lean_inc_ref(v_env_1169_);
v___x_1202_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1192_, v___x_1199_, v_env_1169_, v___x_1200_, v___x_1201_);
v___x_1203_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6___redArg(v___x_1202_, v_declName_1155_);
lean_dec(v___x_1202_);
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_object* v___x_1204_; 
v___x_1204_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___closed__3));
v___y_1171_ = v___x_1204_;
goto v___jp_1170_;
}
else
{
lean_object* v_val_1205_; 
v_val_1205_ = lean_ctor_get(v___x_1203_, 0);
lean_inc(v_val_1205_);
lean_dec_ref_known(v___x_1203_, 1);
v___y_1171_ = v_val_1205_;
goto v___jp_1170_;
}
}
else
{
lean_dec_ref(v_env_1169_);
lean_dec(v_declName_1155_);
return v___x_1198_;
}
}
}
}
v___jp_1166_:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1167_ = lean_box(0);
v___x_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1167_);
return v___x_1168_;
}
v___jp_1170_:
{
lean_object* v___x_1172_; size_t v_sz_1173_; size_t v___x_1174_; lean_object* v___x_1175_; 
v___x_1172_ = lean_box(0);
v_sz_1173_ = lean_array_size(v___y_1171_);
v___x_1174_ = ((size_t)0ULL);
v___x_1175_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__5(v_env_1169_, v_declName_1155_, v___y_1171_, v_sz_1173_, v___x_1174_, v___x_1172_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
lean_dec_ref(v___y_1171_);
lean_dec_ref(v_env_1169_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1182_; 
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1182_ == 0)
{
lean_object* v_unused_1183_; 
v_unused_1183_ = lean_ctor_get(v___x_1175_, 0);
lean_dec(v_unused_1183_);
v___x_1177_ = v___x_1175_;
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
else
{
lean_dec(v___x_1175_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1180_; 
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 0, v___x_1172_);
v___x_1180_ = v___x_1177_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1172_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
else
{
return v___x_1175_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___boxed(lean_object* v_declName_1208_, lean_object* v_isMeta_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
uint8_t v_isMeta_boxed_1218_; lean_object* v_res_1219_; 
v_isMeta_boxed_1218_ = lean_unbox(v_isMeta_1209_);
v_res_1219_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2(v_declName_1208_, v_isMeta_boxed_1218_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec(v___y_1210_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3___redArg(lean_object* v_as_x27_1220_, lean_object* v_b_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
if (lean_obj_tag(v_as_x27_1220_) == 0)
{
lean_object* v___x_1230_; 
v___x_1230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1230_, 0, v_b_1221_);
return v___x_1230_;
}
else
{
lean_object* v_head_1231_; lean_object* v_tail_1232_; uint8_t v___x_1233_; lean_object* v___x_1234_; 
v_head_1231_ = lean_ctor_get(v_as_x27_1220_, 0);
v_tail_1232_ = lean_ctor_get(v_as_x27_1220_, 1);
v___x_1233_ = 1;
lean_inc(v_head_1231_);
v___x_1234_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2(v_head_1231_, v___x_1233_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v___x_1235_; 
lean_dec_ref_known(v___x_1234_, 1);
v___x_1235_ = lean_box(0);
v_as_x27_1220_ = v_tail_1232_;
v_b_1221_ = v___x_1235_;
goto _start;
}
else
{
return v___x_1234_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3___redArg___boxed(lean_object* v_as_x27_1237_, lean_object* v_b_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3___redArg(v_as_x27_1237_, v_b_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec(v___y_1239_);
lean_dec(v_as_x27_1237_);
return v_res_1247_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1253_ = l_Lean_maxRecDepthErrorMessage;
v___x_1254_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1253_);
return v___x_1254_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__4(void){
_start:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__3);
v___x_1256_ = l_Lean_MessageData_ofFormat(v___x_1255_);
return v___x_1256_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1257_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__4);
v___x_1258_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__2));
v___x_1259_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1258_);
lean_ctor_set(v___x_1259_, 1, v___x_1257_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg(lean_object* v_ref_1260_){
_start:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1262_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__5);
v___x_1263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1263_, 0, v_ref_1260_);
lean_ctor_set(v___x_1263_, 1, v___x_1262_);
v___x_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1263_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___boxed(lean_object* v_ref_1265_, lean_object* v___y_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg(v_ref_1265_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___redArg(lean_object* v_x_1268_, lean_object* v___y_1269_){
_start:
{
if (lean_obj_tag(v_x_1268_) == 0)
{
lean_object* v_a_1270_; lean_object* v___x_1271_; 
v_a_1270_ = lean_ctor_get(v_x_1268_, 0);
lean_inc(v_a_1270_);
v___x_1271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1271_, 0, v_a_1270_);
lean_ctor_set(v___x_1271_, 1, v___y_1269_);
return v___x_1271_;
}
else
{
lean_object* v_a_1272_; lean_object* v___x_1273_; 
v_a_1272_ = lean_ctor_get(v_x_1268_, 0);
lean_inc(v_a_1272_);
v___x_1273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1273_, 0, v_a_1272_);
lean_ctor_set(v___x_1273_, 1, v___y_1269_);
return v___x_1273_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___redArg___boxed(lean_object* v_x_1274_, lean_object* v___y_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___redArg(v_x_1274_, v___y_1275_);
lean_dec_ref(v_x_1274_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__0(lean_object* v_env_1277_, lean_object* v_stx_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1277_, v_stx_1278_, v___y_1279_, v___y_1280_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v_a_1282_; 
v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_a_1282_);
if (lean_obj_tag(v_a_1282_) == 0)
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1291_; 
v_a_1283_ = lean_ctor_get(v___x_1281_, 1);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1291_ == 0)
{
lean_object* v_unused_1292_; 
v_unused_1292_ = lean_ctor_get(v___x_1281_, 0);
lean_dec(v_unused_1292_);
v___x_1285_ = v___x_1281_;
v_isShared_1286_ = v_isSharedCheck_1291_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1281_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1291_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1287_; lean_object* v___x_1289_; 
v___x_1287_ = lean_box(0);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 0, v___x_1287_);
v___x_1289_ = v___x_1285_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1287_);
lean_ctor_set(v_reuseFailAlloc_1290_, 1, v_a_1283_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
else
{
lean_object* v_val_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1321_; 
v_val_1293_ = lean_ctor_get(v_a_1282_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v_a_1282_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1295_ = v_a_1282_;
v_isShared_1296_ = v_isSharedCheck_1321_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_val_1293_);
lean_dec(v_a_1282_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1321_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v_snd_1297_; 
v_snd_1297_ = lean_ctor_get(v_val_1293_, 1);
lean_inc(v_snd_1297_);
lean_dec(v_val_1293_);
if (lean_obj_tag(v_snd_1297_) == 0)
{
lean_object* v_a_1298_; lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1307_; 
lean_del_object(v___x_1295_);
v_a_1298_ = lean_ctor_get(v___x_1281_, 1);
lean_inc(v_a_1298_);
lean_dec_ref_known(v___x_1281_, 2);
v_a_1299_ = lean_ctor_get(v_snd_1297_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v_snd_1297_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1301_ = v_snd_1297_;
v_isShared_1302_ = v_isSharedCheck_1307_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_dec(v_snd_1297_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1307_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1304_; 
if (v_isShared_1302_ == 0)
{
v___x_1304_ = v___x_1301_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_a_1299_);
v___x_1304_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
lean_object* v___x_1305_; 
v___x_1305_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___redArg(v___x_1304_, v_a_1298_);
lean_dec_ref(v___x_1304_);
return v___x_1305_;
}
}
}
else
{
lean_object* v_a_1308_; lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1320_; 
v_a_1308_ = lean_ctor_get(v___x_1281_, 1);
lean_inc(v_a_1308_);
lean_dec_ref_known(v___x_1281_, 2);
v_a_1309_ = lean_ctor_get(v_snd_1297_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v_snd_1297_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1311_ = v_snd_1297_;
v_isShared_1312_ = v_isSharedCheck_1320_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v_snd_1297_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1320_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1314_; 
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 0, v_a_1309_);
v___x_1314_ = v___x_1295_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_a_1309_);
v___x_1314_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
lean_object* v___x_1316_; 
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 0, v___x_1314_);
v___x_1316_ = v___x_1311_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v___x_1314_);
v___x_1316_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
lean_object* v___x_1317_; 
v___x_1317_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___redArg(v___x_1316_, v_a_1308_);
lean_dec_ref(v___x_1316_);
return v___x_1317_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1322_; lean_object* v_a_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1330_; 
v_a_1322_ = lean_ctor_get(v___x_1281_, 0);
v_a_1323_ = lean_ctor_get(v___x_1281_, 1);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1325_ = v___x_1281_;
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_a_1323_);
lean_inc(v_a_1322_);
lean_dec(v___x_1281_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1328_; 
if (v_isShared_1326_ == 0)
{
v___x_1328_ = v___x_1325_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_a_1322_);
lean_ctor_set(v_reuseFailAlloc_1329_, 1, v_a_1323_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__0___boxed(lean_object* v_env_1331_, lean_object* v_stx_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__0(v_env_1331_, v_stx_1332_, v___y_1333_, v___y_1334_);
lean_dec_ref(v___y_1333_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__4(lean_object* v_env_1336_, lean_object* v_options_1337_, lean_object* v_currNamespace_1338_, lean_object* v_openDecls_1339_, lean_object* v_n_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1343_ = l_Lean_ResolveName_resolveGlobalName(v_env_1336_, v_options_1337_, v_currNamespace_1338_, v_openDecls_1339_, v_n_1340_);
v___x_1344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1343_);
lean_ctor_set(v___x_1344_, 1, v___y_1342_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__4___boxed(lean_object* v_env_1345_, lean_object* v_options_1346_, lean_object* v_currNamespace_1347_, lean_object* v_openDecls_1348_, lean_object* v_n_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__4(v_env_1345_, v_options_1346_, v_currNamespace_1347_, v_openDecls_1348_, v_n_1349_, v___y_1350_, v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec_ref(v_options_1346_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1_spec__8___redArg(lean_object* v_msg_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v_ref_1359_; lean_object* v___x_1360_; lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1369_; 
v_ref_1359_ = lean_ctor_get(v___y_1356_, 4);
v___x_1360_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0_spec__1(v_msg_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_);
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1363_ = v___x_1360_;
v_isShared_1364_ = v_isSharedCheck_1369_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1360_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1369_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1365_; lean_object* v___x_1367_; 
lean_inc(v_ref_1359_);
v___x_1365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1365_, 0, v_ref_1359_);
lean_ctor_set(v___x_1365_, 1, v_a_1361_);
if (v_isShared_1364_ == 0)
{
lean_ctor_set_tag(v___x_1363_, 1);
lean_ctor_set(v___x_1363_, 0, v___x_1365_);
v___x_1367_ = v___x_1363_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1365_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1_spec__8___redArg___boxed(lean_object* v_msg_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1_spec__8___redArg(v_msg_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
lean_dec(v___y_1374_);
lean_dec_ref(v___y_1373_);
lean_dec(v___y_1372_);
lean_dec_ref(v___y_1371_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1___redArg(lean_object* v_ref_1377_, lean_object* v_msg_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
lean_object* v_toCold_1387_; lean_object* v_options_1388_; lean_object* v_currRecDepth_1389_; lean_object* v_maxRecDepth_1390_; lean_object* v_ref_1391_; lean_object* v_currNamespace_1392_; lean_object* v_openDecls_1393_; lean_object* v_initHeartbeats_1394_; lean_object* v_maxHeartbeats_1395_; lean_object* v_currMacroScope_1396_; uint8_t v_diag_1397_; uint8_t v_suppressElabErrors_1398_; lean_object* v_ref_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v_toCold_1387_ = lean_ctor_get(v___y_1384_, 0);
v_options_1388_ = lean_ctor_get(v___y_1384_, 1);
v_currRecDepth_1389_ = lean_ctor_get(v___y_1384_, 2);
v_maxRecDepth_1390_ = lean_ctor_get(v___y_1384_, 3);
v_ref_1391_ = lean_ctor_get(v___y_1384_, 4);
v_currNamespace_1392_ = lean_ctor_get(v___y_1384_, 5);
v_openDecls_1393_ = lean_ctor_get(v___y_1384_, 6);
v_initHeartbeats_1394_ = lean_ctor_get(v___y_1384_, 7);
v_maxHeartbeats_1395_ = lean_ctor_get(v___y_1384_, 8);
v_currMacroScope_1396_ = lean_ctor_get(v___y_1384_, 9);
v_diag_1397_ = lean_ctor_get_uint8(v___y_1384_, sizeof(void*)*10);
v_suppressElabErrors_1398_ = lean_ctor_get_uint8(v___y_1384_, sizeof(void*)*10 + 1);
v_ref_1399_ = l_Lean_replaceRef(v_ref_1377_, v_ref_1391_);
lean_inc(v_currMacroScope_1396_);
lean_inc(v_maxHeartbeats_1395_);
lean_inc(v_initHeartbeats_1394_);
lean_inc(v_openDecls_1393_);
lean_inc(v_currNamespace_1392_);
lean_inc(v_maxRecDepth_1390_);
lean_inc(v_currRecDepth_1389_);
lean_inc_ref(v_options_1388_);
lean_inc_ref(v_toCold_1387_);
v___x_1400_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_1400_, 0, v_toCold_1387_);
lean_ctor_set(v___x_1400_, 1, v_options_1388_);
lean_ctor_set(v___x_1400_, 2, v_currRecDepth_1389_);
lean_ctor_set(v___x_1400_, 3, v_maxRecDepth_1390_);
lean_ctor_set(v___x_1400_, 4, v_ref_1399_);
lean_ctor_set(v___x_1400_, 5, v_currNamespace_1392_);
lean_ctor_set(v___x_1400_, 6, v_openDecls_1393_);
lean_ctor_set(v___x_1400_, 7, v_initHeartbeats_1394_);
lean_ctor_set(v___x_1400_, 8, v_maxHeartbeats_1395_);
lean_ctor_set(v___x_1400_, 9, v_currMacroScope_1396_);
lean_ctor_set_uint8(v___x_1400_, sizeof(void*)*10, v_diag_1397_);
lean_ctor_set_uint8(v___x_1400_, sizeof(void*)*10 + 1, v_suppressElabErrors_1398_);
v___x_1401_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1_spec__8___redArg(v_msg_1378_, v___y_1382_, v___y_1383_, v___x_1400_, v___y_1385_);
lean_dec_ref_known(v___x_1400_, 10);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1___redArg___boxed(lean_object* v_ref_1402_, lean_object* v_msg_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1___redArg(v_ref_1402_, v_msg_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
lean_dec(v___y_1404_);
lean_dec(v_ref_1402_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg(lean_object* v_x_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v___x_1423_; lean_object* v_toCold_1424_; lean_object* v_env_1425_; lean_object* v_options_1426_; lean_object* v_currRecDepth_1427_; lean_object* v_maxRecDepth_1428_; lean_object* v_ref_1429_; lean_object* v_currNamespace_1430_; lean_object* v_openDecls_1431_; lean_object* v_currMacroScope_1432_; lean_object* v_quotContext_1433_; lean_object* v___x_1434_; lean_object* v_nextMacroScope_1435_; lean_object* v___f_1436_; lean_object* v___f_1437_; lean_object* v___f_1438_; lean_object* v___f_1439_; lean_object* v___f_1440_; lean_object* v_methods_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1423_ = lean_st_ref_get(v___y_1421_);
v_toCold_1424_ = lean_ctor_get(v___y_1420_, 0);
v_env_1425_ = lean_ctor_get(v___x_1423_, 0);
lean_inc_ref_n(v_env_1425_, 4);
lean_dec(v___x_1423_);
v_options_1426_ = lean_ctor_get(v___y_1420_, 1);
v_currRecDepth_1427_ = lean_ctor_get(v___y_1420_, 2);
v_maxRecDepth_1428_ = lean_ctor_get(v___y_1420_, 3);
v_ref_1429_ = lean_ctor_get(v___y_1420_, 4);
v_currNamespace_1430_ = lean_ctor_get(v___y_1420_, 5);
v_openDecls_1431_ = lean_ctor_get(v___y_1420_, 6);
v_currMacroScope_1432_ = lean_ctor_get(v___y_1420_, 9);
v_quotContext_1433_ = lean_ctor_get(v_toCold_1424_, 2);
v___x_1434_ = lean_st_ref_get(v___y_1421_);
v_nextMacroScope_1435_ = lean_ctor_get(v___x_1434_, 1);
lean_inc(v_nextMacroScope_1435_);
lean_dec(v___x_1434_);
v___f_1436_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1436_, 0, v_env_1425_);
v___f_1437_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1437_, 0, v_env_1425_);
lean_inc_n(v_openDecls_1431_, 2);
lean_inc_n(v_currNamespace_1430_, 3);
v___f_1438_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_1438_, 0, v_env_1425_);
lean_closure_set(v___f_1438_, 1, v_currNamespace_1430_);
lean_closure_set(v___f_1438_, 2, v_openDecls_1431_);
v___f_1439_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1439_, 0, v_currNamespace_1430_);
lean_inc_ref(v_options_1426_);
v___f_1440_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_1440_, 0, v_env_1425_);
lean_closure_set(v___f_1440_, 1, v_options_1426_);
lean_closure_set(v___f_1440_, 2, v_currNamespace_1430_);
lean_closure_set(v___f_1440_, 3, v_openDecls_1431_);
v_methods_1441_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1441_, 0, v___f_1436_);
lean_ctor_set(v_methods_1441_, 1, v___f_1439_);
lean_ctor_set(v_methods_1441_, 2, v___f_1437_);
lean_ctor_set(v_methods_1441_, 3, v___f_1438_);
lean_ctor_set(v_methods_1441_, 4, v___f_1440_);
lean_inc(v_ref_1429_);
lean_inc(v_maxRecDepth_1428_);
lean_inc(v_currRecDepth_1427_);
lean_inc(v_currMacroScope_1432_);
lean_inc(v_quotContext_1433_);
v___x_1442_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1442_, 0, v_methods_1441_);
lean_ctor_set(v___x_1442_, 1, v_quotContext_1433_);
lean_ctor_set(v___x_1442_, 2, v_currMacroScope_1432_);
lean_ctor_set(v___x_1442_, 3, v_currRecDepth_1427_);
lean_ctor_set(v___x_1442_, 4, v_maxRecDepth_1428_);
lean_ctor_set(v___x_1442_, 5, v_ref_1429_);
v___x_1443_ = lean_box(0);
v___x_1444_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1444_, 0, v_nextMacroScope_1435_);
lean_ctor_set(v___x_1444_, 1, v___x_1443_);
lean_ctor_set(v___x_1444_, 2, v___x_1443_);
v___x_1445_ = lean_apply_2(v_x_1414_, v___x_1442_, v___x_1444_);
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_object* v_a_1446_; lean_object* v_a_1447_; lean_object* v_macroScope_1448_; lean_object* v_traceMsgs_1449_; lean_object* v_expandedMacroDecls_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
v_a_1446_ = lean_ctor_get(v___x_1445_, 1);
lean_inc(v_a_1446_);
v_a_1447_ = lean_ctor_get(v___x_1445_, 0);
lean_inc(v_a_1447_);
lean_dec_ref_known(v___x_1445_, 2);
v_macroScope_1448_ = lean_ctor_get(v_a_1446_, 0);
lean_inc(v_macroScope_1448_);
v_traceMsgs_1449_ = lean_ctor_get(v_a_1446_, 1);
lean_inc(v_traceMsgs_1449_);
v_expandedMacroDecls_1450_ = lean_ctor_get(v_a_1446_, 2);
lean_inc(v_expandedMacroDecls_1450_);
lean_dec(v_a_1446_);
v___x_1451_ = lean_box(0);
v___x_1452_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3___redArg(v_expandedMacroDecls_1450_, v___x_1451_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
lean_dec(v_expandedMacroDecls_1450_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_object* v___x_1453_; lean_object* v_env_1454_; lean_object* v_ngen_1455_; lean_object* v_auxDeclNGen_1456_; lean_object* v_traceState_1457_; lean_object* v_cache_1458_; lean_object* v_messages_1459_; lean_object* v_infoState_1460_; lean_object* v_snapshotTasks_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1487_; 
lean_dec_ref_known(v___x_1452_, 1);
v___x_1453_ = lean_st_ref_take(v___y_1421_);
v_env_1454_ = lean_ctor_get(v___x_1453_, 0);
v_ngen_1455_ = lean_ctor_get(v___x_1453_, 2);
v_auxDeclNGen_1456_ = lean_ctor_get(v___x_1453_, 3);
v_traceState_1457_ = lean_ctor_get(v___x_1453_, 4);
v_cache_1458_ = lean_ctor_get(v___x_1453_, 5);
v_messages_1459_ = lean_ctor_get(v___x_1453_, 6);
v_infoState_1460_ = lean_ctor_get(v___x_1453_, 7);
v_snapshotTasks_1461_ = lean_ctor_get(v___x_1453_, 8);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1487_ == 0)
{
lean_object* v_unused_1488_; 
v_unused_1488_ = lean_ctor_get(v___x_1453_, 1);
lean_dec(v_unused_1488_);
v___x_1463_ = v___x_1453_;
v_isShared_1464_ = v_isSharedCheck_1487_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_snapshotTasks_1461_);
lean_inc(v_infoState_1460_);
lean_inc(v_messages_1459_);
lean_inc(v_cache_1458_);
lean_inc(v_traceState_1457_);
lean_inc(v_auxDeclNGen_1456_);
lean_inc(v_ngen_1455_);
lean_inc(v_env_1454_);
lean_dec(v___x_1453_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1487_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1466_; 
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 1, v_macroScope_1448_);
v___x_1466_ = v___x_1463_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_env_1454_);
lean_ctor_set(v_reuseFailAlloc_1486_, 1, v_macroScope_1448_);
lean_ctor_set(v_reuseFailAlloc_1486_, 2, v_ngen_1455_);
lean_ctor_set(v_reuseFailAlloc_1486_, 3, v_auxDeclNGen_1456_);
lean_ctor_set(v_reuseFailAlloc_1486_, 4, v_traceState_1457_);
lean_ctor_set(v_reuseFailAlloc_1486_, 5, v_cache_1458_);
lean_ctor_set(v_reuseFailAlloc_1486_, 6, v_messages_1459_);
lean_ctor_set(v_reuseFailAlloc_1486_, 7, v_infoState_1460_);
lean_ctor_set(v_reuseFailAlloc_1486_, 8, v_snapshotTasks_1461_);
v___x_1466_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1467_ = lean_st_ref_put(v___y_1421_, v___x_1466_);
v___x_1468_ = l_List_reverse___redArg(v_traceMsgs_1449_);
v___x_1469_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4(v___x_1468_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1476_; 
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1476_ == 0)
{
lean_object* v_unused_1477_; 
v_unused_1477_ = lean_ctor_get(v___x_1469_, 0);
lean_dec(v_unused_1477_);
v___x_1471_ = v___x_1469_;
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
else
{
lean_dec(v___x_1469_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1474_; 
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 0, v_a_1447_);
v___x_1474_ = v___x_1471_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_a_1447_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
else
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1485_; 
lean_dec(v_a_1447_);
v_a_1478_ = lean_ctor_get(v___x_1469_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1480_ = v___x_1469_;
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1469_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1483_; 
if (v_isShared_1481_ == 0)
{
v___x_1483_ = v___x_1480_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_a_1478_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
}
}
}
else
{
lean_object* v_a_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1496_; 
lean_dec(v_traceMsgs_1449_);
lean_dec(v_macroScope_1448_);
lean_dec(v_a_1447_);
v_a_1489_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1491_ = v___x_1452_;
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_a_1489_);
lean_dec(v___x_1452_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1494_; 
if (v_isShared_1492_ == 0)
{
v___x_1494_ = v___x_1491_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_a_1489_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
}
else
{
lean_object* v_a_1497_; 
v_a_1497_ = lean_ctor_get(v___x_1445_, 0);
lean_inc(v_a_1497_);
lean_dec_ref_known(v___x_1445_, 2);
if (lean_obj_tag(v_a_1497_) == 0)
{
lean_object* v_a_1498_; lean_object* v_a_1499_; lean_object* v___x_1500_; uint8_t v___x_1501_; 
v_a_1498_ = lean_ctor_get(v_a_1497_, 0);
lean_inc(v_a_1498_);
v_a_1499_ = lean_ctor_get(v_a_1497_, 1);
lean_inc_ref(v_a_1499_);
lean_dec_ref_known(v_a_1497_, 2);
v___x_1500_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___closed__0));
v___x_1501_ = lean_string_dec_eq(v_a_1499_, v___x_1500_);
if (v___x_1501_ == 0)
{
lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1502_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1502_, 0, v_a_1499_);
v___x_1503_ = l_Lean_MessageData_ofFormat(v___x_1502_);
v___x_1504_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1___redArg(v_a_1498_, v___x_1503_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
lean_dec(v_a_1498_);
return v___x_1504_;
}
else
{
lean_object* v___x_1505_; 
lean_dec_ref(v_a_1499_);
v___x_1505_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg(v_a_1498_);
return v___x_1505_;
}
}
else
{
lean_object* v___x_1506_; 
v___x_1506_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
return v___x_1506_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___boxed(lean_object* v_x_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_){
_start:
{
lean_object* v_res_1516_; 
v_res_1516_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg(v_x_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
lean_dec(v___y_1508_);
return v_res_1516_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheck___closed__1(void){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1518_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheck___closed__0));
v___x_1519_ = l_Lean_stringToMessageData(v___x_1518_);
return v___x_1519_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheck___closed__3(void){
_start:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1521_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheck___closed__2));
v___x_1522_ = l_Lean_stringToMessageData(v___x_1521_);
return v___x_1522_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheck___closed__5(void){
_start:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; 
v___x_1524_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheck___closed__4));
v___x_1525_ = l_Lean_stringToMessageData(v___x_1524_);
return v___x_1525_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheck___closed__7(void){
_start:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1527_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheck___closed__6));
v___x_1528_ = l_Lean_stringToMessageData(v___x_1527_);
return v___x_1528_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheck___closed__9(void){
_start:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1530_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheck___closed__8));
v___x_1531_ = l_Lean_stringToMessageData(v___x_1530_);
return v___x_1531_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheck___closed__11(void){
_start:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1533_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheck___closed__10));
v___x_1534_ = l_Lean_stringToMessageData(v___x_1533_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheck(lean_object* v_stx_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_){
_start:
{
lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v___y_1552_; lean_object* v___y_1553_; lean_object* v___y_1554_; lean_object* v___y_1594_; lean_object* v___y_1595_; lean_object* v___y_1596_; lean_object* v___y_1597_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; uint8_t v___y_1604_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___x_1649_; lean_object* v___y_1651_; lean_object* v_env_1675_; lean_object* v___x_1676_; lean_object* v_toEnvExtension_1677_; lean_object* v_asyncMode_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1649_ = lean_st_ref_get(v_a_1542_);
v_env_1675_ = lean_ctor_get(v___x_1649_, 0);
lean_inc_ref(v_env_1675_);
lean_dec(v___x_1649_);
v___x_1676_ = l_Lean_Elab_deprecatedSyntaxExt;
v_toEnvExtension_1677_ = lean_ctor_get(v___x_1676_, 0);
v_asyncMode_1678_ = lean_ctor_get(v_toEnvExtension_1677_, 2);
v___x_1679_ = lean_box(1);
v___x_1680_ = lean_box(0);
v___x_1681_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1679_, v___x_1676_, v_env_1675_, v_asyncMode_1678_, v___x_1680_);
lean_inc(v_stx_1535_);
v___x_1682_ = l_Lean_Syntax_getKind(v_stx_1535_);
v___x_1683_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1681_, v___x_1682_);
lean_dec(v___x_1682_);
lean_dec(v___x_1681_);
if (lean_obj_tag(v___x_1683_) == 1)
{
lean_object* v_val_1684_; lean_object* v_text_x3f_1685_; 
v_val_1684_ = lean_ctor_get(v___x_1683_, 0);
lean_inc(v_val_1684_);
lean_dec_ref_known(v___x_1683_, 1);
v_text_x3f_1685_ = lean_ctor_get(v_val_1684_, 1);
lean_inc(v_text_x3f_1685_);
lean_dec(v_val_1684_);
if (lean_obj_tag(v_text_x3f_1685_) == 0)
{
lean_object* v___x_1686_; 
v___x_1686_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__13);
v___y_1651_ = v___x_1686_;
goto v___jp_1650_;
}
else
{
lean_object* v_val_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
v_val_1687_ = lean_ctor_get(v_text_x3f_1685_, 0);
lean_inc(v_val_1687_);
lean_dec_ref_known(v_text_x3f_1685_, 1);
v___x_1688_ = lean_obj_once(&l_Lean_Elab_Term_Quotation_precheck___closed__11, &l_Lean_Elab_Term_Quotation_precheck___closed__11_once, _init_l_Lean_Elab_Term_Quotation_precheck___closed__11);
v___x_1689_ = l_Lean_stringToMessageData(v_val_1687_);
v___x_1690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1688_);
lean_ctor_set(v___x_1690_, 1, v___x_1689_);
v___y_1651_ = v___x_1690_;
goto v___jp_1650_;
}
}
else
{
lean_dec(v___x_1683_);
v___y_1608_ = v_a_1536_;
v___y_1609_ = v_a_1537_;
v___y_1610_ = v_a_1538_;
v___y_1611_ = v_a_1539_;
v___y_1612_ = v_a_1540_;
v___y_1613_ = v_a_1541_;
v___y_1614_ = v_a_1542_;
goto v___jp_1607_;
}
v___jp_1544_:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1545_ = lean_box(0);
v___x_1546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1545_);
return v___x_1546_;
}
v___jp_1547_:
{
uint8_t v___x_1555_; 
lean_inc(v_stx_1535_);
v___x_1555_ = l_Lean_Syntax_isAnyAntiquot(v_stx_1535_);
if (v___x_1555_ == 0)
{
uint8_t v___x_1556_; 
lean_inc(v_stx_1535_);
v___x_1556_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent(v_stx_1535_);
if (v___x_1556_ == 0)
{
lean_dec(v_stx_1535_);
goto v___jp_1544_;
}
else
{
if (v___x_1555_ == 0)
{
lean_object* v___x_1557_; lean_object* v___x_1558_; 
lean_inc(v_stx_1535_);
v___x_1557_ = lean_alloc_closure((void*)(l_Lean_Macro_expandMacro_x3f___boxed), 3, 1);
lean_closure_set(v___x_1557_, 0, v_stx_1535_);
v___x_1558_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg(v___x_1557_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; 
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
lean_inc(v_a_1559_);
lean_dec_ref_known(v___x_1558_, 1);
if (lean_obj_tag(v_a_1559_) == 1)
{
lean_object* v_val_1560_; lean_object* v___x_1561_; 
lean_dec(v_stx_1535_);
v_val_1560_ = lean_ctor_get(v_a_1559_, 0);
lean_inc(v_val_1560_);
lean_dec_ref_known(v_a_1559_, 1);
v___x_1561_ = l_Lean_Elab_Term_Quotation_precheck(v_val_1560_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1569_; 
v_isSharedCheck_1569_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1569_ == 0)
{
lean_object* v_unused_1570_; 
v_unused_1570_ = lean_ctor_get(v___x_1561_, 0);
lean_dec(v_unused_1570_);
v___x_1563_ = v___x_1561_;
v_isShared_1564_ = v_isSharedCheck_1569_;
goto v_resetjp_1562_;
}
else
{
lean_dec(v___x_1561_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1569_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1565_; lean_object* v___x_1567_; 
v___x_1565_ = lean_box(0);
if (v_isShared_1564_ == 0)
{
lean_ctor_set(v___x_1563_, 0, v___x_1565_);
v___x_1567_ = v___x_1563_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v___x_1565_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
}
else
{
return v___x_1561_;
}
}
else
{
lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
lean_dec(v_a_1559_);
v___x_1571_ = lean_obj_once(&l_Lean_Elab_Term_Quotation_precheck___closed__1, &l_Lean_Elab_Term_Quotation_precheck___closed__1_once, _init_l_Lean_Elab_Term_Quotation_precheck___closed__1);
lean_inc_n(v_stx_1535_, 2);
v___x_1572_ = l_Lean_Syntax_getKind(v_stx_1535_);
v___x_1573_ = l_Lean_MessageData_ofName(v___x_1572_);
v___x_1574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1571_);
lean_ctor_set(v___x_1574_, 1, v___x_1573_);
v___x_1575_ = lean_obj_once(&l_Lean_Elab_Term_Quotation_precheck___closed__3, &l_Lean_Elab_Term_Quotation_precheck___closed__3_once, _init_l_Lean_Elab_Term_Quotation_precheck___closed__3);
v___x_1576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1574_);
lean_ctor_set(v___x_1576_, 1, v___x_1575_);
v___x_1577_ = l_Lean_MessageData_ofSyntax(v_stx_1535_);
v___x_1578_ = l_Lean_indentD(v___x_1577_);
v___x_1579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1576_);
lean_ctor_set(v___x_1579_, 1, v___x_1578_);
v___x_1580_ = lean_obj_once(&l_Lean_Elab_Term_Quotation_precheck___closed__5, &l_Lean_Elab_Term_Quotation_precheck___closed__5_once, _init_l_Lean_Elab_Term_Quotation_precheck___closed__5);
v___x_1581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1579_);
lean_ctor_set(v___x_1581_, 1, v___x_1580_);
v___x_1582_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1___redArg(v_stx_1535_, v___x_1581_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
lean_dec(v_stx_1535_);
return v___x_1582_;
}
}
else
{
lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1590_; 
lean_dec(v_stx_1535_);
v_a_1583_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1585_ = v___x_1558_;
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_dec(v___x_1558_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1588_; 
if (v_isShared_1586_ == 0)
{
v___x_1588_ = v___x_1585_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_a_1583_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
}
else
{
lean_dec(v_stx_1535_);
goto v___jp_1544_;
}
}
}
else
{
lean_object* v___x_1591_; lean_object* v___x_1592_; 
lean_dec(v_stx_1535_);
v___x_1591_ = lean_box(0);
v___x_1592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1591_);
return v___x_1592_;
}
}
v___jp_1593_:
{
if (v___y_1604_ == 0)
{
if (lean_obj_tag(v___y_1598_) == 0)
{
lean_dec_ref_known(v___y_1598_, 2);
lean_dec(v_stx_1535_);
return v___y_1596_;
}
else
{
lean_object* v_id_1605_; uint8_t v___x_1606_; 
v_id_1605_ = lean_ctor_get(v___y_1598_, 0);
lean_inc(v_id_1605_);
lean_dec_ref_known(v___y_1598_, 2);
v___x_1606_ = l_Lean_instBEqInternalExceptionId_beq(v___y_1603_, v_id_1605_);
lean_dec(v_id_1605_);
if (v___x_1606_ == 0)
{
lean_dec(v_stx_1535_);
return v___y_1596_;
}
else
{
lean_dec_ref(v___y_1596_);
v___y_1548_ = v___y_1602_;
v___y_1549_ = v___y_1597_;
v___y_1550_ = v___y_1599_;
v___y_1551_ = v___y_1595_;
v___y_1552_ = v___y_1600_;
v___y_1553_ = v___y_1601_;
v___y_1554_ = v___y_1594_;
goto v___jp_1547_;
}
}
}
else
{
lean_dec_ref(v___y_1598_);
lean_dec(v_stx_1535_);
return v___y_1596_;
}
}
v___jp_1607_:
{
lean_object* v___x_1615_; lean_object* v_env_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1615_ = lean_st_ref_get(v___y_1614_);
v_env_1616_ = lean_ctor_get(v___x_1615_, 0);
lean_inc_ref(v_env_1616_);
lean_dec(v___x_1615_);
v___x_1617_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
lean_inc(v_stx_1535_);
v___x_1618_ = l_Lean_Syntax_getKind(v_stx_1535_);
v___x_1619_ = l_Lean_KeyedDeclsAttribute_getValues___redArg(v___x_1617_, v_env_1616_, v___x_1618_);
lean_dec(v___x_1618_);
if (lean_obj_tag(v___x_1619_) == 1)
{
lean_object* v_head_1620_; lean_object* v_toCold_1621_; lean_object* v_options_1622_; lean_object* v_currRecDepth_1623_; lean_object* v_maxRecDepth_1624_; lean_object* v_ref_1625_; lean_object* v_currNamespace_1626_; lean_object* v_openDecls_1627_; lean_object* v_initHeartbeats_1628_; lean_object* v_maxHeartbeats_1629_; lean_object* v_currMacroScope_1630_; uint8_t v_diag_1631_; uint8_t v_suppressElabErrors_1632_; lean_object* v_ref_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
v_head_1620_ = lean_ctor_get(v___x_1619_, 0);
lean_inc(v_head_1620_);
lean_dec_ref_known(v___x_1619_, 2);
v_toCold_1621_ = lean_ctor_get(v___y_1613_, 0);
v_options_1622_ = lean_ctor_get(v___y_1613_, 1);
v_currRecDepth_1623_ = lean_ctor_get(v___y_1613_, 2);
v_maxRecDepth_1624_ = lean_ctor_get(v___y_1613_, 3);
v_ref_1625_ = lean_ctor_get(v___y_1613_, 4);
v_currNamespace_1626_ = lean_ctor_get(v___y_1613_, 5);
v_openDecls_1627_ = lean_ctor_get(v___y_1613_, 6);
v_initHeartbeats_1628_ = lean_ctor_get(v___y_1613_, 7);
v_maxHeartbeats_1629_ = lean_ctor_get(v___y_1613_, 8);
v_currMacroScope_1630_ = lean_ctor_get(v___y_1613_, 9);
v_diag_1631_ = lean_ctor_get_uint8(v___y_1613_, sizeof(void*)*10);
v_suppressElabErrors_1632_ = lean_ctor_get_uint8(v___y_1613_, sizeof(void*)*10 + 1);
v_ref_1633_ = l_Lean_replaceRef(v_stx_1535_, v_ref_1625_);
lean_inc(v_currMacroScope_1630_);
lean_inc(v_maxHeartbeats_1629_);
lean_inc(v_initHeartbeats_1628_);
lean_inc(v_openDecls_1627_);
lean_inc(v_currNamespace_1626_);
lean_inc(v_maxRecDepth_1624_);
lean_inc(v_currRecDepth_1623_);
lean_inc_ref(v_options_1622_);
lean_inc_ref(v_toCold_1621_);
v___x_1634_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_1634_, 0, v_toCold_1621_);
lean_ctor_set(v___x_1634_, 1, v_options_1622_);
lean_ctor_set(v___x_1634_, 2, v_currRecDepth_1623_);
lean_ctor_set(v___x_1634_, 3, v_maxRecDepth_1624_);
lean_ctor_set(v___x_1634_, 4, v_ref_1633_);
lean_ctor_set(v___x_1634_, 5, v_currNamespace_1626_);
lean_ctor_set(v___x_1634_, 6, v_openDecls_1627_);
lean_ctor_set(v___x_1634_, 7, v_initHeartbeats_1628_);
lean_ctor_set(v___x_1634_, 8, v_maxHeartbeats_1629_);
lean_ctor_set(v___x_1634_, 9, v_currMacroScope_1630_);
lean_ctor_set_uint8(v___x_1634_, sizeof(void*)*10, v_diag_1631_);
lean_ctor_set_uint8(v___x_1634_, sizeof(void*)*10 + 1, v_suppressElabErrors_1632_);
lean_inc(v___y_1614_);
lean_inc(v___y_1612_);
lean_inc_ref(v___y_1611_);
lean_inc(v___y_1610_);
lean_inc_ref(v___y_1609_);
lean_inc(v___y_1608_);
lean_inc(v_stx_1535_);
v___x_1635_ = lean_apply_9(v_head_1620_, v_stx_1535_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___x_1634_, v___y_1614_, lean_box(0));
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1643_; 
lean_dec(v_stx_1535_);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1643_ == 0)
{
lean_object* v_unused_1644_; 
v_unused_1644_ = lean_ctor_get(v___x_1635_, 0);
lean_dec(v_unused_1644_);
v___x_1637_ = v___x_1635_;
v_isShared_1638_ = v_isSharedCheck_1643_;
goto v_resetjp_1636_;
}
else
{
lean_dec(v___x_1635_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1643_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1639_; lean_object* v___x_1641_; 
v___x_1639_ = lean_box(0);
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 0, v___x_1639_);
v___x_1641_ = v___x_1637_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1639_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
else
{
lean_object* v_a_1645_; lean_object* v___x_1646_; uint8_t v___x_1647_; 
v_a_1645_ = lean_ctor_get(v___x_1635_, 0);
lean_inc(v_a_1645_);
v___x_1646_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1647_ = l_Lean_Exception_isInterrupt(v_a_1645_);
if (v___x_1647_ == 0)
{
uint8_t v___x_1648_; 
lean_inc(v_a_1645_);
v___x_1648_ = l_Lean_Exception_isRuntime(v_a_1645_);
v___y_1594_ = v___y_1614_;
v___y_1595_ = v___y_1611_;
v___y_1596_ = v___x_1635_;
v___y_1597_ = v___y_1609_;
v___y_1598_ = v_a_1645_;
v___y_1599_ = v___y_1610_;
v___y_1600_ = v___y_1612_;
v___y_1601_ = v___y_1613_;
v___y_1602_ = v___y_1608_;
v___y_1603_ = v___x_1646_;
v___y_1604_ = v___x_1648_;
goto v___jp_1593_;
}
else
{
v___y_1594_ = v___y_1614_;
v___y_1595_ = v___y_1611_;
v___y_1596_ = v___x_1635_;
v___y_1597_ = v___y_1609_;
v___y_1598_ = v_a_1645_;
v___y_1599_ = v___y_1610_;
v___y_1600_ = v___y_1612_;
v___y_1601_ = v___y_1613_;
v___y_1602_ = v___y_1608_;
v___y_1603_ = v___x_1646_;
v___y_1604_ = v___x_1647_;
goto v___jp_1593_;
}
}
}
else
{
lean_dec(v___x_1619_);
v___y_1548_ = v___y_1608_;
v___y_1549_ = v___y_1609_;
v___y_1550_ = v___y_1610_;
v___y_1551_ = v___y_1611_;
v___y_1552_ = v___y_1612_;
v___y_1553_ = v___y_1613_;
v___y_1554_ = v___y_1614_;
goto v___jp_1547_;
}
}
v___jp_1650_:
{
lean_object* v_toCold_1652_; lean_object* v_options_1653_; lean_object* v_currRecDepth_1654_; lean_object* v_maxRecDepth_1655_; lean_object* v_ref_1656_; lean_object* v_currNamespace_1657_; lean_object* v_openDecls_1658_; lean_object* v_initHeartbeats_1659_; lean_object* v_maxHeartbeats_1660_; lean_object* v_currMacroScope_1661_; uint8_t v_diag_1662_; uint8_t v_suppressElabErrors_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v_ref_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
v_toCold_1652_ = lean_ctor_get(v_a_1541_, 0);
v_options_1653_ = lean_ctor_get(v_a_1541_, 1);
v_currRecDepth_1654_ = lean_ctor_get(v_a_1541_, 2);
v_maxRecDepth_1655_ = lean_ctor_get(v_a_1541_, 3);
v_ref_1656_ = lean_ctor_get(v_a_1541_, 4);
v_currNamespace_1657_ = lean_ctor_get(v_a_1541_, 5);
v_openDecls_1658_ = lean_ctor_get(v_a_1541_, 6);
v_initHeartbeats_1659_ = lean_ctor_get(v_a_1541_, 7);
v_maxHeartbeats_1660_ = lean_ctor_get(v_a_1541_, 8);
v_currMacroScope_1661_ = lean_ctor_get(v_a_1541_, 9);
v_diag_1662_ = lean_ctor_get_uint8(v_a_1541_, sizeof(void*)*10);
v_suppressElabErrors_1663_ = lean_ctor_get_uint8(v_a_1541_, sizeof(void*)*10 + 1);
v___x_1664_ = l_Lean_Linter_linter_deprecated_syntax;
v___x_1665_ = lean_obj_once(&l_Lean_Elab_Term_Quotation_precheck___closed__7, &l_Lean_Elab_Term_Quotation_precheck___closed__7_once, _init_l_Lean_Elab_Term_Quotation_precheck___closed__7);
lean_inc_n(v_stx_1535_, 2);
v___x_1666_ = l_Lean_Syntax_getKind(v_stx_1535_);
v___x_1667_ = l_Lean_MessageData_ofName(v___x_1666_);
v___x_1668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1665_);
lean_ctor_set(v___x_1668_, 1, v___x_1667_);
v___x_1669_ = lean_obj_once(&l_Lean_Elab_Term_Quotation_precheck___closed__9, &l_Lean_Elab_Term_Quotation_precheck___closed__9_once, _init_l_Lean_Elab_Term_Quotation_precheck___closed__9);
v___x_1670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1668_);
lean_ctor_set(v___x_1670_, 1, v___x_1669_);
v___x_1671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1670_);
lean_ctor_set(v___x_1671_, 1, v___y_1651_);
v_ref_1672_ = l_Lean_replaceRef(v_stx_1535_, v_ref_1656_);
lean_inc(v_currMacroScope_1661_);
lean_inc(v_maxHeartbeats_1660_);
lean_inc(v_initHeartbeats_1659_);
lean_inc(v_openDecls_1658_);
lean_inc(v_currNamespace_1657_);
lean_inc(v_maxRecDepth_1655_);
lean_inc(v_currRecDepth_1654_);
lean_inc_ref(v_options_1653_);
lean_inc_ref(v_toCold_1652_);
v___x_1673_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_1673_, 0, v_toCold_1652_);
lean_ctor_set(v___x_1673_, 1, v_options_1653_);
lean_ctor_set(v___x_1673_, 2, v_currRecDepth_1654_);
lean_ctor_set(v___x_1673_, 3, v_maxRecDepth_1655_);
lean_ctor_set(v___x_1673_, 4, v_ref_1672_);
lean_ctor_set(v___x_1673_, 5, v_currNamespace_1657_);
lean_ctor_set(v___x_1673_, 6, v_openDecls_1658_);
lean_ctor_set(v___x_1673_, 7, v_initHeartbeats_1659_);
lean_ctor_set(v___x_1673_, 8, v_maxHeartbeats_1660_);
lean_ctor_set(v___x_1673_, 9, v_currMacroScope_1661_);
lean_ctor_set_uint8(v___x_1673_, sizeof(void*)*10, v_diag_1662_);
lean_ctor_set_uint8(v___x_1673_, sizeof(void*)*10 + 1, v_suppressElabErrors_1663_);
v___x_1674_ = l_Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2(v___x_1664_, v_stx_1535_, v___x_1671_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v___x_1673_, v_a_1542_);
lean_dec_ref_known(v___x_1673_, 10);
if (lean_obj_tag(v___x_1674_) == 0)
{
lean_dec_ref_known(v___x_1674_, 1);
v___y_1608_ = v_a_1536_;
v___y_1609_ = v_a_1537_;
v___y_1610_ = v_a_1538_;
v___y_1611_ = v_a_1539_;
v___y_1612_ = v_a_1540_;
v___y_1613_ = v_a_1541_;
v___y_1614_ = v_a_1542_;
goto v___jp_1607_;
}
else
{
lean_dec(v_stx_1535_);
return v___x_1674_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheck___boxed(lean_object* v_stx_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_Lean_Elab_Term_Quotation_precheck(v_stx_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
lean_dec(v_a_1698_);
lean_dec_ref(v_a_1697_);
lean_dec(v_a_1696_);
lean_dec_ref(v_a_1695_);
lean_dec(v_a_1694_);
lean_dec_ref(v_a_1693_);
lean_dec(v_a_1692_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1(lean_object* v_00_u03b1_1701_, lean_object* v_x_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
lean_object* v___x_1705_; 
v___x_1705_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___redArg(v_x_1702_, v___y_1704_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1706_, lean_object* v_x_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1(v_00_u03b1_1706_, v_x_1707_, v___y_1708_, v___y_1709_);
lean_dec_ref(v___y_1708_);
lean_dec_ref(v_x_1707_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5(lean_object* v_00_u03b1_1711_, lean_object* v_ref_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v___x_1721_; 
v___x_1721_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg(v_ref_1712_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1722_, lean_object* v_ref_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5(v_00_u03b1_1722_, v_ref_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
lean_dec(v___y_1724_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6(lean_object* v_00_u03b1_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_){
_start:
{
lean_object* v___x_1742_; 
v___x_1742_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___boxed(lean_object* v_00_u03b1_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6(v_00_u03b1_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
lean_dec(v___y_1746_);
lean_dec_ref(v___y_1745_);
lean_dec(v___y_1744_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0(lean_object* v_00_u03b1_1753_, lean_object* v_x_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_){
_start:
{
lean_object* v___x_1763_; 
v___x_1763_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg(v_x_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___boxed(lean_object* v_00_u03b1_1764_, lean_object* v_x_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0(v_00_u03b1_1764_, v_x_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec(v___y_1770_);
lean_dec_ref(v___y_1769_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1(lean_object* v_00_u03b1_1775_, lean_object* v_ref_1776_, lean_object* v_msg_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_){
_start:
{
lean_object* v___x_1786_; 
v___x_1786_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1___redArg(v_ref_1776_, v_msg_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1___boxed(lean_object* v_00_u03b1_1787_, lean_object* v_ref_1788_, lean_object* v_msg_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1(v_00_u03b1_1787_, v_ref_1788_, v_msg_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1793_);
lean_dec(v___y_1792_);
lean_dec_ref(v___y_1791_);
lean_dec(v___y_1790_);
lean_dec(v_ref_1788_);
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0(lean_object* v_cls_1799_, lean_object* v_msg_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
lean_object* v___x_1809_; 
v___x_1809_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg(v_cls_1799_, v_msg_1800_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___boxed(lean_object* v_cls_1810_, lean_object* v_msg_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v_res_1820_; 
v_res_1820_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0(v_cls_1810_, v_msg_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec(v___y_1812_);
return v_res_1820_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3(lean_object* v_as_1821_, lean_object* v_as_x27_1822_, lean_object* v_b_1823_, lean_object* v_a_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
lean_object* v___x_1833_; 
v___x_1833_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3___redArg(v_as_x27_1822_, v_b_1823_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3___boxed(lean_object* v_as_1834_, lean_object* v_as_x27_1835_, lean_object* v_b_1836_, lean_object* v_a_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_){
_start:
{
lean_object* v_res_1846_; 
v_res_1846_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3(v_as_1834_, v_as_x27_1835_, v_b_1836_, v_a_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_);
lean_dec(v___y_1844_);
lean_dec_ref(v___y_1843_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1841_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
lean_dec(v___y_1838_);
lean_dec(v_as_x27_1835_);
lean_dec(v_as_1834_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1_spec__8(lean_object* v_00_u03b1_1847_, lean_object* v_msg_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_){
_start:
{
lean_object* v___x_1857_; 
v___x_1857_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1_spec__8___redArg(v_msg_1848_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1_spec__8___boxed(lean_object* v_00_u03b1_1858_, lean_object* v_msg_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1_spec__8(v_00_u03b1_1858_, v_msg_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec(v___y_1860_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__10_spec__15(lean_object* v_o_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
lean_object* v___x_1878_; 
v___x_1878_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__10_spec__15___redArg(v_o_1869_, v___y_1876_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__10_spec__15___boxed(lean_object* v_o_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__10_spec__15(v_o_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_1889_, lean_object* v_m_1890_, lean_object* v_a_1891_){
_start:
{
lean_object* v___x_1892_; 
v___x_1892_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6___redArg(v_m_1890_, v_a_1891_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6___boxed(lean_object* v_00_u03b2_1893_, lean_object* v_m_1894_, lean_object* v_a_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6(v_00_u03b2_1893_, v_m_1894_, v_a_1895_);
lean_dec(v_a_1895_);
lean_dec_ref(v_m_1894_);
return v_res_1896_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9(lean_object* v_00_u03b2_1897_, lean_object* v_x_1898_, lean_object* v_x_1899_){
_start:
{
uint8_t v___x_1900_; 
v___x_1900_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9___redArg(v_x_1898_, v_x_1899_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9___boxed(lean_object* v_00_u03b2_1901_, lean_object* v_x_1902_, lean_object* v_x_1903_){
_start:
{
uint8_t v_res_1904_; lean_object* v_r_1905_; 
v_res_1904_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9(v_00_u03b2_1901_, v_x_1902_, v_x_1903_);
lean_dec_ref(v_x_1903_);
lean_dec_ref(v_x_1902_);
v_r_1905_ = lean_box(v_res_1904_);
return v_r_1905_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6_spec__12(lean_object* v_00_u03b2_1906_, lean_object* v_a_1907_, lean_object* v_x_1908_){
_start:
{
lean_object* v___x_1909_; 
v___x_1909_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6_spec__12___redArg(v_a_1907_, v_x_1908_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6_spec__12___boxed(lean_object* v_00_u03b2_1910_, lean_object* v_a_1911_, lean_object* v_x_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6_spec__12(v_00_u03b2_1910_, v_a_1911_, v_x_1912_);
lean_dec(v_x_1912_);
lean_dec(v_a_1911_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20(lean_object* v_ref_1914_, lean_object* v_msgData_1915_, uint8_t v_severity_1916_, uint8_t v_isSilent_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
lean_object* v___x_1926_; 
v___x_1926_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg(v_ref_1914_, v_msgData_1915_, v_severity_1916_, v_isSilent_1917_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___boxed(lean_object* v_ref_1927_, lean_object* v_msgData_1928_, lean_object* v_severity_1929_, lean_object* v_isSilent_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
uint8_t v_severity_boxed_1939_; uint8_t v_isSilent_boxed_1940_; lean_object* v_res_1941_; 
v_severity_boxed_1939_ = lean_unbox(v_severity_1929_);
v_isSilent_boxed_1940_ = lean_unbox(v_isSilent_1930_);
v_res_1941_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20(v_ref_1927_, v_msgData_1928_, v_severity_boxed_1939_, v_isSilent_boxed_1940_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
lean_dec(v___y_1931_);
lean_dec(v_ref_1927_);
return v_res_1941_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16(lean_object* v_00_u03b2_1942_, lean_object* v_x_1943_, size_t v_x_1944_, lean_object* v_x_1945_){
_start:
{
uint8_t v___x_1946_; 
v___x_1946_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16___redArg(v_x_1943_, v_x_1944_, v_x_1945_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16___boxed(lean_object* v_00_u03b2_1947_, lean_object* v_x_1948_, lean_object* v_x_1949_, lean_object* v_x_1950_){
_start:
{
size_t v_x_38130__boxed_1951_; uint8_t v_res_1952_; lean_object* v_r_1953_; 
v_x_38130__boxed_1951_ = lean_unbox_usize(v_x_1949_);
lean_dec(v_x_1949_);
v_res_1952_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16(v_00_u03b2_1947_, v_x_1948_, v_x_38130__boxed_1951_, v_x_1950_);
lean_dec_ref(v_x_1950_);
lean_dec_ref(v_x_1948_);
v_r_1953_ = lean_box(v_res_1952_);
return v_r_1953_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16_spec__20(lean_object* v_00_u03b2_1954_, lean_object* v_keys_1955_, lean_object* v_vals_1956_, lean_object* v_heq_1957_, lean_object* v_i_1958_, lean_object* v_k_1959_){
_start:
{
uint8_t v___x_1960_; 
v___x_1960_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16_spec__20___redArg(v_keys_1955_, v_i_1958_, v_k_1959_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16_spec__20___boxed(lean_object* v_00_u03b2_1961_, lean_object* v_keys_1962_, lean_object* v_vals_1963_, lean_object* v_heq_1964_, lean_object* v_i_1965_, lean_object* v_k_1966_){
_start:
{
uint8_t v_res_1967_; lean_object* v_r_1968_; 
v_res_1967_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16_spec__20(v_00_u03b2_1961_, v_keys_1962_, v_vals_1963_, v_heq_1964_, v_i_1965_, v_k_1966_);
lean_dec_ref(v_k_1966_);
lean_dec_ref(v_vals_1963_);
lean_dec_ref(v_keys_1962_);
v_r_1968_ = lean_box(v_res_1967_);
return v_r_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_runPrecheck(lean_object* v_stx_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_){
_start:
{
uint8_t v___y_1978_; lean_object* v_options_1983_; lean_object* v___x_1984_; uint8_t v___x_1985_; 
v_options_1983_ = lean_ctor_get(v_a_1974_, 1);
v___x_1984_ = l_Lean_Elab_Term_Quotation_quotPrecheck;
v___x_1985_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20_spec__22(v_options_1983_, v___x_1984_);
if (v___x_1985_ == 0)
{
v___y_1978_ = v___x_1985_;
goto v___jp_1977_;
}
else
{
lean_object* v___x_1986_; uint8_t v___x_1987_; 
v___x_1986_ = l_Lean_Elab_Term_Quotation_hygiene;
v___x_1987_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20_spec__22(v_options_1983_, v___x_1986_);
v___y_1978_ = v___x_1987_;
goto v___jp_1977_;
}
v___jp_1977_:
{
if (v___y_1978_ == 0)
{
lean_object* v___x_1979_; lean_object* v___x_1980_; 
lean_dec(v_stx_1969_);
v___x_1979_ = lean_box(0);
v___x_1980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1979_);
return v___x_1980_;
}
else
{
lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___x_1981_ = l_Lean_NameSet_empty;
v___x_1982_ = l_Lean_Elab_Term_Quotation_precheck(v_stx_1969_, v___x_1981_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_);
return v___x_1982_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_runPrecheck___boxed(lean_object* v_stx_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l_Lean_Elab_Term_Quotation_runPrecheck(v_stx_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_);
lean_dec(v_a_1994_);
lean_dec_ref(v_a_1993_);
lean_dec(v_a_1992_);
lean_dec_ref(v_a_1991_);
lean_dec(v_a_1990_);
lean_dec_ref(v_a_1989_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable_spec__0(lean_object* v_e_2000_, lean_object* v_init_2001_, lean_object* v_x_2002_){
_start:
{
if (lean_obj_tag(v_x_2002_) == 0)
{
lean_object* v_v_2003_; lean_object* v_l_2004_; lean_object* v_r_2005_; lean_object* v___x_2006_; 
v_v_2003_ = lean_ctor_get(v_x_2002_, 2);
v_l_2004_ = lean_ctor_get(v_x_2002_, 3);
v_r_2005_ = lean_ctor_get(v_x_2002_, 4);
v___x_2006_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable_spec__0(v_e_2000_, v_init_2001_, v_l_2004_);
if (lean_obj_tag(v___x_2006_) == 0)
{
return v___x_2006_;
}
else
{
lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2020_; 
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2020_ == 0)
{
lean_object* v_unused_2021_; 
v_unused_2021_ = lean_ctor_get(v___x_2006_, 0);
lean_dec(v_unused_2021_);
v___x_2008_ = v___x_2006_;
v_isShared_2009_ = v_isSharedCheck_2020_;
goto v_resetjp_2007_;
}
else
{
lean_dec(v___x_2006_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2020_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2010_; uint8_t v___x_2011_; 
v___x_2010_ = lean_box(0);
v___x_2011_ = lean_expr_eqv(v_e_2000_, v_v_2003_);
if (v___x_2011_ == 0)
{
lean_object* v___x_2012_; 
lean_del_object(v___x_2008_);
v___x_2012_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable_spec__0___closed__0));
v_init_2001_ = v___x_2012_;
v_x_2002_ = v_r_2005_;
goto _start;
}
else
{
lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2018_; 
v___x_2014_ = lean_box(v___x_2011_);
v___x_2015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2015_, 0, v___x_2014_);
v___x_2016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2015_);
lean_ctor_set(v___x_2016_, 1, v___x_2010_);
if (v_isShared_2009_ == 0)
{
lean_ctor_set_tag(v___x_2008_, 0);
lean_ctor_set(v___x_2008_, 0, v___x_2016_);
v___x_2018_ = v___x_2008_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v___x_2016_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
}
else
{
lean_object* v___x_2022_; 
v___x_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2022_, 0, v_init_2001_);
return v___x_2022_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable_spec__0___boxed(lean_object* v_e_2023_, lean_object* v_init_2024_, lean_object* v_x_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable_spec__0(v_e_2023_, v_init_2024_, v_x_2025_);
lean_dec(v_x_2025_);
lean_dec_ref(v_e_2023_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable___redArg(lean_object* v_e_2027_, lean_object* v_a_2028_){
_start:
{
lean_object* v___y_2031_; lean_object* v_sectionFVars_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v_a_2047_; 
v_sectionFVars_2044_ = lean_ctor_get(v_a_2028_, 5);
v___x_2045_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable_spec__0___closed__0));
v___x_2046_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable_spec__0(v_e_2027_, v___x_2045_, v_sectionFVars_2044_);
v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
lean_inc(v_a_2047_);
lean_dec_ref(v___x_2046_);
v___y_2031_ = v_a_2047_;
goto v___jp_2030_;
v___jp_2030_:
{
lean_object* v_fst_2032_; 
v_fst_2032_ = lean_ctor_get(v___y_2031_, 0);
lean_inc(v_fst_2032_);
lean_dec_ref(v___y_2031_);
if (lean_obj_tag(v_fst_2032_) == 0)
{
uint8_t v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2033_ = 0;
v___x_2034_ = lean_box(v___x_2033_);
v___x_2035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2034_);
return v___x_2035_;
}
else
{
lean_object* v_val_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2043_; 
v_val_2036_ = lean_ctor_get(v_fst_2032_, 0);
v_isSharedCheck_2043_ = !lean_is_exclusive(v_fst_2032_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2038_ = v_fst_2032_;
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_val_2036_);
lean_dec(v_fst_2032_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2041_; 
if (v_isShared_2039_ == 0)
{
lean_ctor_set_tag(v___x_2038_, 0);
v___x_2041_ = v___x_2038_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_val_2036_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable___redArg___boxed(lean_object* v_e_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_){
_start:
{
lean_object* v_res_2051_; 
v_res_2051_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable___redArg(v_e_2048_, v_a_2049_);
lean_dec_ref(v_a_2049_);
lean_dec_ref(v_e_2048_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable(lean_object* v_e_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_){
_start:
{
lean_object* v___x_2060_; 
v___x_2060_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable___redArg(v_e_2052_, v_a_2053_);
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable___boxed(lean_object* v_e_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_){
_start:
{
lean_object* v_res_2069_; 
v_res_2069_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable(v_e_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_);
lean_dec(v_a_2067_);
lean_dec_ref(v_a_2066_);
lean_dec(v_a_2065_);
lean_dec_ref(v_a_2064_);
lean_dec(v_a_2063_);
lean_dec_ref(v_a_2062_);
lean_dec_ref(v_e_2061_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg(uint8_t v___x_2078_, lean_object* v_as_x27_2079_, lean_object* v_b_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
if (lean_obj_tag(v_as_x27_2079_) == 0)
{
lean_object* v___x_2084_; 
v___x_2084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2084_, 0, v_b_2080_);
return v___x_2084_;
}
else
{
lean_object* v_head_2085_; lean_object* v_tail_2086_; lean_object* v_fst_2087_; lean_object* v___x_2088_; 
lean_dec_ref(v_b_2080_);
v_head_2085_ = lean_ctor_get(v_as_x27_2079_, 0);
v_tail_2086_ = lean_ctor_get(v_as_x27_2079_, 1);
v_fst_2087_ = lean_ctor_get(v_head_2085_, 0);
v___x_2088_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___closed__0));
if (lean_obj_tag(v_fst_2087_) == 1)
{
lean_object* v___x_2089_; lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2105_; 
v___x_2089_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable___redArg(v_fst_2087_, v___y_2081_);
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2092_ = v___x_2089_;
v_isShared_2093_ = v_isSharedCheck_2105_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2089_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2105_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
uint8_t v___y_2095_; lean_object* v_options_2101_; lean_object* v___x_2102_; uint8_t v___x_2103_; 
v_options_2101_ = lean_ctor_get(v___y_2082_, 1);
v___x_2102_ = l_Lean_Elab_Term_Quotation_quotPrecheck_allowSectionVars;
v___x_2103_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20_spec__22(v_options_2101_, v___x_2102_);
if (v___x_2103_ == 0)
{
lean_dec(v_a_2090_);
v___y_2095_ = v___x_2078_;
goto v___jp_2094_;
}
else
{
uint8_t v___x_2104_; 
v___x_2104_ = lean_unbox(v_a_2090_);
lean_dec(v_a_2090_);
v___y_2095_ = v___x_2104_;
goto v___jp_2094_;
}
v___jp_2094_:
{
if (v___y_2095_ == 0)
{
lean_del_object(v___x_2092_);
v_as_x27_2079_ = v_tail_2086_;
v_b_2080_ = v___x_2088_;
goto _start;
}
else
{
lean_object* v___x_2097_; lean_object* v___x_2099_; 
v___x_2097_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___closed__2));
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 0, v___x_2097_);
v___x_2099_ = v___x_2092_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v___x_2097_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
return v___x_2099_;
}
}
}
}
}
else
{
v_as_x27_2079_ = v_tail_2086_;
v_b_2080_ = v___x_2088_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___boxed(lean_object* v___x_2107_, lean_object* v_as_x27_2108_, lean_object* v_b_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_){
_start:
{
uint8_t v___x_5564__boxed_2113_; lean_object* v_res_2114_; 
v___x_5564__boxed_2113_ = lean_unbox(v___x_2107_);
v_res_2114_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg(v___x_5564__boxed_2113_, v_as_x27_2108_, v_b_2109_, v___y_2110_, v___y_2111_);
lean_dec_ref(v___y_2111_);
lean_dec_ref(v___y_2110_);
lean_dec(v_as_x27_2108_);
return v_res_2114_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckIdent___closed__1(void){
_start:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2116_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckIdent___closed__0));
v___x_2117_ = l_Lean_stringToMessageData(v___x_2116_);
return v___x_2117_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckIdent___closed__3(void){
_start:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2119_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckIdent___closed__2));
v___x_2120_ = l_Lean_stringToMessageData(v___x_2119_);
return v___x_2120_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckIdent___closed__6(void){
_start:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2124_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckIdent___closed__5));
v___x_2125_ = l_Lean_MessageData_ofFormat(v___x_2124_);
return v___x_2125_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckIdent___closed__7(void){
_start:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2126_ = lean_obj_once(&l_Lean_Elab_Term_Quotation_precheckIdent___closed__6, &l_Lean_Elab_Term_Quotation_precheckIdent___closed__6_once, _init_l_Lean_Elab_Term_Quotation_precheckIdent___closed__6);
v___x_2127_ = l_Lean_MessageData_note(v___x_2126_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckIdent(lean_object* v_stx_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_){
_start:
{
if (lean_obj_tag(v_stx_2128_) == 3)
{
lean_object* v_val_2137_; lean_object* v_preresolved_2138_; uint8_t v___x_2139_; 
v_val_2137_ = lean_ctor_get(v_stx_2128_, 2);
lean_inc(v_val_2137_);
v_preresolved_2138_ = lean_ctor_get(v_stx_2128_, 3);
v___x_2139_ = l_List_isEmpty___redArg(v_preresolved_2138_);
if (v___x_2139_ == 0)
{
lean_object* v___x_2140_; lean_object* v___x_2141_; 
lean_dec_ref_known(v_stx_2128_, 4);
lean_dec(v_val_2137_);
v___x_2140_ = lean_box(0);
v___x_2141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2141_, 0, v___x_2140_);
return v___x_2141_;
}
else
{
lean_object* v___x_2142_; 
lean_inc(v_val_2137_);
lean_inc_ref(v_stx_2128_);
v___x_2142_ = l_Lean_Elab_realizeGlobalNameWithInfos(v_stx_2128_, v_val_2137_, v_a_2134_, v_a_2135_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_object* v_a_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2212_; 
v_a_2143_ = lean_ctor_get(v___x_2142_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2145_ = v___x_2142_;
v_isShared_2146_ = v_isSharedCheck_2212_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_a_2143_);
lean_dec(v___x_2142_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2212_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
if (lean_obj_tag(v_a_2143_) == 1)
{
lean_object* v___x_2147_; lean_object* v___x_2149_; 
lean_dec_ref_known(v_a_2143_, 2);
lean_dec_ref_known(v_stx_2128_, 4);
lean_dec(v_val_2137_);
v___x_2147_ = lean_box(0);
if (v_isShared_2146_ == 0)
{
lean_ctor_set(v___x_2145_, 0, v___x_2147_);
v___x_2149_ = v___x_2145_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v___x_2147_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
else
{
uint8_t v___x_2151_; lean_object* v_a_2153_; lean_object* v___y_2190_; 
lean_dec(v_a_2143_);
v___x_2151_ = l_Lean_NameSet_contains(v_a_2129_, v_val_2137_);
if (v___x_2151_ == 0)
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
lean_del_object(v___x_2145_);
v___x_2200_ = lean_box(0);
v___x_2201_ = lean_box(0);
lean_inc(v_val_2137_);
v___x_2202_ = l_Lean_Elab_Term_resolveName(v_stx_2128_, v_val_2137_, v___x_2200_, v___x_2200_, v___x_2201_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_);
if (lean_obj_tag(v___x_2202_) == 0)
{
v___y_2190_ = v___x_2202_;
goto v___jp_2189_;
}
else
{
lean_object* v_a_2203_; uint8_t v___y_2205_; uint8_t v___x_2206_; 
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_a_2203_);
v___x_2206_ = l_Lean_Exception_isInterrupt(v_a_2203_);
if (v___x_2206_ == 0)
{
uint8_t v___x_2207_; 
v___x_2207_ = l_Lean_Exception_isRuntime(v_a_2203_);
v___y_2205_ = v___x_2207_;
goto v___jp_2204_;
}
else
{
lean_dec(v_a_2203_);
v___y_2205_ = v___x_2206_;
goto v___jp_2204_;
}
v___jp_2204_:
{
if (v___y_2205_ == 0)
{
lean_dec_ref_known(v___x_2202_, 1);
v_a_2153_ = v___x_2200_;
goto v___jp_2152_;
}
else
{
v___y_2190_ = v___x_2202_;
goto v___jp_2189_;
}
}
}
}
else
{
lean_object* v___x_2208_; lean_object* v___x_2210_; 
lean_dec_ref_known(v_stx_2128_, 4);
lean_dec(v_val_2137_);
v___x_2208_ = lean_box(0);
if (v_isShared_2146_ == 0)
{
lean_ctor_set(v___x_2145_, 0, v___x_2208_);
v___x_2210_ = v___x_2145_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v___x_2208_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
v___jp_2152_:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2154_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___closed__0));
v___x_2155_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg(v___x_2151_, v_a_2153_, v___x_2154_, v_a_2130_, v_a_2134_);
lean_dec(v_a_2153_);
if (lean_obj_tag(v___x_2155_) == 0)
{
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2180_; 
v_a_2156_ = lean_ctor_get(v___x_2155_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2158_ = v___x_2155_;
v_isShared_2159_ = v_isSharedCheck_2180_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2155_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2180_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v_fst_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2178_; 
v_fst_2160_ = lean_ctor_get(v_a_2156_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v_a_2156_);
if (v_isSharedCheck_2178_ == 0)
{
lean_object* v_unused_2179_; 
v_unused_2179_ = lean_ctor_get(v_a_2156_, 1);
lean_dec(v_unused_2179_);
v___x_2162_ = v_a_2156_;
v_isShared_2163_ = v_isSharedCheck_2178_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_fst_2160_);
lean_dec(v_a_2156_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2178_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
if (lean_obj_tag(v_fst_2160_) == 0)
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2167_; 
lean_del_object(v___x_2158_);
v___x_2164_ = lean_obj_once(&l_Lean_Elab_Term_Quotation_precheckIdent___closed__1, &l_Lean_Elab_Term_Quotation_precheckIdent___closed__1_once, _init_l_Lean_Elab_Term_Quotation_precheckIdent___closed__1);
v___x_2165_ = l_Lean_MessageData_ofName(v_val_2137_);
if (v_isShared_2163_ == 0)
{
lean_ctor_set_tag(v___x_2162_, 7);
lean_ctor_set(v___x_2162_, 1, v___x_2165_);
lean_ctor_set(v___x_2162_, 0, v___x_2164_);
v___x_2167_ = v___x_2162_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v___x_2164_);
lean_ctor_set(v_reuseFailAlloc_2173_, 1, v___x_2165_);
v___x_2167_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2168_ = lean_obj_once(&l_Lean_Elab_Term_Quotation_precheckIdent___closed__3, &l_Lean_Elab_Term_Quotation_precheckIdent___closed__3_once, _init_l_Lean_Elab_Term_Quotation_precheckIdent___closed__3);
v___x_2169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2167_);
lean_ctor_set(v___x_2169_, 1, v___x_2168_);
v___x_2170_ = lean_obj_once(&l_Lean_Elab_Term_Quotation_precheckIdent___closed__7, &l_Lean_Elab_Term_Quotation_precheckIdent___closed__7_once, _init_l_Lean_Elab_Term_Quotation_precheckIdent___closed__7);
v___x_2171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2169_);
lean_ctor_set(v___x_2171_, 1, v___x_2170_);
v___x_2172_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1_spec__8___redArg(v___x_2171_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_);
return v___x_2172_;
}
}
else
{
lean_object* v_val_2174_; lean_object* v___x_2176_; 
lean_del_object(v___x_2162_);
lean_dec(v_val_2137_);
v_val_2174_ = lean_ctor_get(v_fst_2160_, 0);
lean_inc(v_val_2174_);
lean_dec_ref_known(v_fst_2160_, 1);
if (v_isShared_2159_ == 0)
{
lean_ctor_set(v___x_2158_, 0, v_val_2174_);
v___x_2176_ = v___x_2158_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_val_2174_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
}
else
{
lean_object* v_a_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2188_; 
lean_dec(v_val_2137_);
v_a_2181_ = lean_ctor_get(v___x_2155_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2183_ = v___x_2155_;
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_a_2181_);
lean_dec(v___x_2155_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2186_; 
if (v_isShared_2184_ == 0)
{
v___x_2186_ = v___x_2183_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_a_2181_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
}
v___jp_2189_:
{
if (lean_obj_tag(v___y_2190_) == 0)
{
lean_object* v_a_2191_; 
v_a_2191_ = lean_ctor_get(v___y_2190_, 0);
lean_inc(v_a_2191_);
lean_dec_ref_known(v___y_2190_, 1);
v_a_2153_ = v_a_2191_;
goto v___jp_2152_;
}
else
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2199_; 
lean_dec(v_val_2137_);
v_a_2192_ = lean_ctor_get(v___y_2190_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___y_2190_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2194_ = v___y_2190_;
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___y_2190_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2197_; 
if (v_isShared_2195_ == 0)
{
v___x_2197_ = v___x_2194_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_a_2192_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
lean_dec_ref_known(v_stx_2128_, 4);
lean_dec(v_val_2137_);
v_a_2213_ = lean_ctor_get(v___x_2142_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2215_ = v___x_2142_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2142_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2213_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
}
}
else
{
lean_object* v___x_2221_; 
lean_dec(v_stx_2128_);
v___x_2221_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
return v___x_2221_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___boxed(lean_object* v_stx_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l_Lean_Elab_Term_Quotation_precheckIdent(v_stx_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_);
lean_dec(v_a_2229_);
lean_dec_ref(v_a_2228_);
lean_dec(v_a_2227_);
lean_dec_ref(v_a_2226_);
lean_dec(v_a_2225_);
lean_dec_ref(v_a_2224_);
lean_dec(v_a_2223_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0(uint8_t v___x_2232_, lean_object* v_as_2233_, lean_object* v_as_x27_2234_, lean_object* v_b_2235_, lean_object* v_a_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_){
_start:
{
lean_object* v___x_2245_; 
v___x_2245_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg(v___x_2232_, v_as_x27_2234_, v_b_2235_, v___y_2238_, v___y_2242_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___boxed(lean_object* v___x_2246_, lean_object* v_as_2247_, lean_object* v_as_x27_2248_, lean_object* v_b_2249_, lean_object* v_a_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_){
_start:
{
uint8_t v___x_5849__boxed_2259_; lean_object* v_res_2260_; 
v___x_5849__boxed_2259_ = lean_unbox(v___x_2246_);
v_res_2260_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0(v___x_5849__boxed_2259_, v_as_2247_, v_as_x27_2248_, v_b_2249_, v_a_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
lean_dec(v___y_2251_);
lean_dec(v_as_x27_2248_);
lean_dec(v_as_2247_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1(){
_start:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2272_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
v___x_2273_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__1));
v___x_2274_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__3));
v___x_2275_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckIdent___boxed), 9, 0);
v___x_2276_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2272_, v___x_2273_, v___x_2274_, v___x_2275_);
return v___x_2276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___boxed(lean_object* v_a_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1();
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0(lean_object* v_as_2292_, size_t v_sz_2293_, size_t v_i_2294_, lean_object* v_b_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_){
_start:
{
lean_object* v_a_2305_; uint8_t v___x_2309_; 
v___x_2309_ = lean_usize_dec_lt(v_i_2294_, v_sz_2293_);
if (v___x_2309_ == 0)
{
lean_object* v___x_2310_; 
v___x_2310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2310_, 0, v_b_2295_);
return v___x_2310_;
}
else
{
lean_object* v___x_2311_; lean_object* v_a_2312_; lean_object* v___x_2313_; uint8_t v___x_2314_; 
v___x_2311_ = lean_box(0);
v_a_2312_ = lean_array_uget_borrowed(v_as_2292_, v_i_2294_);
v___x_2313_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__2));
lean_inc(v_a_2312_);
v___x_2314_ = l_Lean_Syntax_isOfKind(v_a_2312_, v___x_2313_);
if (v___x_2314_ == 0)
{
lean_object* v___x_2315_; uint8_t v___x_2316_; 
v___x_2315_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__4));
lean_inc(v_a_2312_);
v___x_2316_ = l_Lean_Syntax_isOfKind(v_a_2312_, v___x_2315_);
if (v___x_2316_ == 0)
{
lean_object* v___x_2317_; 
lean_inc(v_a_2312_);
v___x_2317_ = l_Lean_Elab_Term_Quotation_precheck(v_a_2312_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_);
if (lean_obj_tag(v___x_2317_) == 0)
{
lean_dec_ref_known(v___x_2317_, 1);
v_a_2305_ = v___x_2311_;
goto v___jp_2304_;
}
else
{
return v___x_2317_;
}
}
else
{
v_a_2305_ = v___x_2311_;
goto v___jp_2304_;
}
}
else
{
lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2318_ = lean_unsigned_to_nat(3u);
v___x_2319_ = l_Lean_Syntax_getArg(v_a_2312_, v___x_2318_);
v___x_2320_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2319_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_dec_ref_known(v___x_2320_, 1);
v_a_2305_ = v___x_2311_;
goto v___jp_2304_;
}
else
{
return v___x_2320_;
}
}
}
v___jp_2304_:
{
size_t v___x_2306_; size_t v___x_2307_; 
v___x_2306_ = ((size_t)1ULL);
v___x_2307_ = lean_usize_add(v_i_2294_, v___x_2306_);
v_i_2294_ = v___x_2307_;
v_b_2295_ = v_a_2305_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___boxed(lean_object* v_as_2321_, lean_object* v_sz_2322_, lean_object* v_i_2323_, lean_object* v_b_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
size_t v_sz_boxed_2333_; size_t v_i_boxed_2334_; lean_object* v_res_2335_; 
v_sz_boxed_2333_ = lean_unbox_usize(v_sz_2322_);
lean_dec(v_sz_2322_);
v_i_boxed_2334_ = lean_unbox_usize(v_i_2323_);
lean_dec(v_i_2323_);
v_res_2335_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0(v_as_2321_, v_sz_boxed_2333_, v_i_boxed_2334_, v_b_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
lean_dec(v___y_2327_);
lean_dec_ref(v___y_2326_);
lean_dec(v___y_2325_);
lean_dec_ref(v_as_2321_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckApp(lean_object* v_x_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_){
_start:
{
lean_object* v___x_2351_; uint8_t v___x_2352_; 
v___x_2351_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckApp___closed__1));
lean_inc(v_x_2342_);
v___x_2352_ = l_Lean_Syntax_isOfKind(v_x_2342_, v___x_2351_);
if (v___x_2352_ == 0)
{
lean_object* v___x_2353_; 
lean_dec(v_x_2342_);
v___x_2353_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
return v___x_2353_;
}
else
{
lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2354_ = lean_unsigned_to_nat(0u);
v___x_2355_ = l_Lean_Syntax_getArg(v_x_2342_, v___x_2354_);
v___x_2356_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2355_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_);
if (lean_obj_tag(v___x_2356_) == 0)
{
lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v_args_2359_; lean_object* v___x_2360_; size_t v_sz_2361_; size_t v___x_2362_; lean_object* v___x_2363_; 
lean_dec_ref_known(v___x_2356_, 1);
v___x_2357_ = lean_unsigned_to_nat(1u);
v___x_2358_ = l_Lean_Syntax_getArg(v_x_2342_, v___x_2357_);
lean_dec(v_x_2342_);
v_args_2359_ = l_Lean_Syntax_getArgs(v___x_2358_);
lean_dec(v___x_2358_);
v___x_2360_ = lean_box(0);
v_sz_2361_ = lean_array_size(v_args_2359_);
v___x_2362_ = ((size_t)0ULL);
v___x_2363_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0(v_args_2359_, v_sz_2361_, v___x_2362_, v___x_2360_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_);
lean_dec_ref(v_args_2359_);
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2370_; 
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2370_ == 0)
{
lean_object* v_unused_2371_; 
v_unused_2371_ = lean_ctor_get(v___x_2363_, 0);
lean_dec(v_unused_2371_);
v___x_2365_ = v___x_2363_;
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
else
{
lean_dec(v___x_2363_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2368_; 
if (v_isShared_2366_ == 0)
{
lean_ctor_set(v___x_2365_, 0, v___x_2360_);
v___x_2368_ = v___x_2365_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v___x_2360_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
else
{
return v___x_2363_;
}
}
else
{
lean_dec(v_x_2342_);
return v___x_2356_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckApp___boxed(lean_object* v_x_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_){
_start:
{
lean_object* v_res_2381_; 
v_res_2381_ = l_Lean_Elab_Term_Quotation_precheckApp(v_x_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_);
lean_dec(v_a_2379_);
lean_dec_ref(v_a_2378_);
lean_dec(v_a_2377_);
lean_dec_ref(v_a_2376_);
lean_dec(v_a_2375_);
lean_dec_ref(v_a_2374_);
lean_dec(v_a_2373_);
return v_res_2381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1(){
_start:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2390_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
v___x_2391_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckApp___closed__1));
v___x_2392_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__1));
v___x_2393_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckApp___boxed), 9, 0);
v___x_2394_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2390_, v___x_2391_, v___x_2392_, v___x_2393_);
return v___x_2394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___boxed(lean_object* v_a_2395_){
_start:
{
lean_object* v_res_2396_; 
v_res_2396_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1();
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckTypeAscription(lean_object* v_x_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_){
_start:
{
lean_object* v___x_2418_; uint8_t v___x_2419_; 
v___x_2418_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__1));
lean_inc(v_x_2409_);
v___x_2419_ = l_Lean_Syntax_isOfKind(v_x_2409_, v___x_2418_);
if (v___x_2419_ == 0)
{
lean_object* v___x_2420_; 
lean_dec(v_x_2409_);
v___x_2420_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
return v___x_2420_;
}
else
{
lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; uint8_t v___x_2424_; 
v___x_2421_ = lean_unsigned_to_nat(0u);
v___x_2422_ = l_Lean_Syntax_getArg(v_x_2409_, v___x_2421_);
v___x_2423_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__3));
lean_inc(v___x_2422_);
v___x_2424_ = l_Lean_Syntax_isOfKind(v___x_2422_, v___x_2423_);
if (v___x_2424_ == 0)
{
lean_object* v___x_2425_; 
lean_dec(v___x_2422_);
lean_dec(v_x_2409_);
v___x_2425_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
return v___x_2425_;
}
else
{
lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; uint8_t v___x_2429_; 
v___x_2426_ = lean_unsigned_to_nat(1u);
v___x_2427_ = l_Lean_Syntax_getArg(v___x_2422_, v___x_2426_);
lean_dec(v___x_2422_);
v___x_2428_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___closed__1));
lean_inc(v___x_2427_);
v___x_2429_ = l_Lean_Syntax_isOfKind(v___x_2427_, v___x_2428_);
if (v___x_2429_ == 0)
{
lean_object* v___x_2430_; 
lean_dec(v___x_2427_);
lean_dec(v_x_2409_);
v___x_2430_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
return v___x_2430_;
}
else
{
lean_object* v___x_2431_; lean_object* v___x_2432_; uint8_t v___x_2433_; 
v___x_2431_ = l_Lean_Syntax_getArg(v___x_2427_, v___x_2421_);
lean_dec(v___x_2427_);
v___x_2432_ = lean_box(0);
v___x_2433_ = l_Lean_Syntax_matchesIdent(v___x_2431_, v___x_2432_);
lean_dec(v___x_2431_);
if (v___x_2433_ == 0)
{
lean_object* v___x_2434_; 
lean_dec(v_x_2409_);
v___x_2434_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
return v___x_2434_;
}
else
{
lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; uint8_t v___x_2438_; 
v___x_2435_ = l_Lean_Syntax_getArg(v_x_2409_, v___x_2426_);
v___x_2436_ = lean_unsigned_to_nat(3u);
v___x_2437_ = l_Lean_Syntax_getArg(v_x_2409_, v___x_2436_);
lean_dec(v_x_2409_);
lean_inc(v___x_2437_);
v___x_2438_ = l_Lean_Syntax_matchesNull(v___x_2437_, v___x_2426_);
if (v___x_2438_ == 0)
{
uint8_t v___x_2439_; 
v___x_2439_ = l_Lean_Syntax_matchesNull(v___x_2437_, v___x_2421_);
if (v___x_2439_ == 0)
{
lean_object* v___x_2440_; 
lean_dec(v___x_2435_);
v___x_2440_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
return v___x_2440_;
}
else
{
lean_object* v___x_2441_; 
v___x_2441_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2435_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_);
return v___x_2441_;
}
}
else
{
lean_object* v___x_2442_; 
v___x_2442_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2435_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_object* v___x_2443_; lean_object* v___x_2444_; 
lean_dec_ref_known(v___x_2442_, 1);
v___x_2443_ = l_Lean_Syntax_getArg(v___x_2437_, v___x_2421_);
lean_dec(v___x_2437_);
v___x_2444_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2443_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_);
return v___x_2444_;
}
else
{
lean_dec(v___x_2437_);
return v___x_2442_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckTypeAscription___boxed(lean_object* v_x_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_){
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l_Lean_Elab_Term_Quotation_precheckTypeAscription(v_x_2445_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_);
lean_dec(v_a_2452_);
lean_dec_ref(v_a_2451_);
lean_dec(v_a_2450_);
lean_dec_ref(v_a_2449_);
lean_dec(v_a_2448_);
lean_dec_ref(v_a_2447_);
lean_dec(v_a_2446_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1(){
_start:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2463_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
v___x_2464_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__1));
v___x_2465_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__1));
v___x_2466_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckTypeAscription___boxed), 9, 0);
v___x_2467_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2463_, v___x_2464_, v___x_2465_, v___x_2466_);
return v___x_2467_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___boxed(lean_object* v_a_2468_){
_start:
{
lean_object* v_res_2469_; 
v_res_2469_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1();
return v_res_2469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckExplicit(lean_object* v_x_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_){
_start:
{
lean_object* v___x_2485_; uint8_t v___x_2486_; 
v___x_2485_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckExplicit___closed__1));
lean_inc(v_x_2476_);
v___x_2486_ = l_Lean_Syntax_isOfKind(v_x_2476_, v___x_2485_);
if (v___x_2486_ == 0)
{
lean_object* v___x_2487_; 
lean_dec(v_x_2476_);
v___x_2487_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
return v___x_2487_;
}
else
{
lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2488_ = lean_unsigned_to_nat(1u);
v___x_2489_ = l_Lean_Syntax_getArg(v_x_2476_, v___x_2488_);
lean_dec(v_x_2476_);
v___x_2490_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2489_, v_a_2477_, v_a_2478_, v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_, v_a_2483_);
return v___x_2490_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckExplicit___boxed(lean_object* v_x_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l_Lean_Elab_Term_Quotation_precheckExplicit(v_x_2491_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_);
lean_dec(v_a_2498_);
lean_dec_ref(v_a_2497_);
lean_dec(v_a_2496_);
lean_dec_ref(v_a_2495_);
lean_dec(v_a_2494_);
lean_dec_ref(v_a_2493_);
lean_dec(v_a_2492_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1(){
_start:
{
lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2509_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
v___x_2510_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckExplicit___closed__1));
v___x_2511_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__1));
v___x_2512_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckExplicit___boxed), 9, 0);
v___x_2513_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2509_, v___x_2510_, v___x_2511_, v___x_2512_);
return v___x_2513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___boxed(lean_object* v_a_2514_){
_start:
{
lean_object* v_res_2515_; 
v_res_2515_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1();
return v_res_2515_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2517_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1___closed__0));
v___x_2518_ = l_Lean_stringToMessageData(v___x_2517_);
return v___x_2518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1(lean_object* v_as_2519_, size_t v_i_2520_, size_t v_stop_2521_, lean_object* v_b_2522_){
_start:
{
lean_object* v___y_2524_; uint8_t v___x_2528_; 
v___x_2528_ = lean_usize_dec_eq(v_i_2520_, v_stop_2521_);
if (v___x_2528_ == 0)
{
lean_object* v___x_2529_; lean_object* v_fst_2530_; 
v___x_2529_ = lean_array_uget(v_as_2519_, v_i_2520_);
v_fst_2530_ = lean_ctor_get(v___x_2529_, 0);
lean_inc(v_fst_2530_);
if (lean_obj_tag(v_fst_2530_) == 0)
{
lean_object* v_snd_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2544_; 
v_snd_2531_ = lean_ctor_get(v___x_2529_, 1);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2544_ == 0)
{
lean_object* v_unused_2545_; 
v_unused_2545_ = lean_ctor_get(v___x_2529_, 0);
lean_dec(v_unused_2545_);
v___x_2533_ = v___x_2529_;
v_isShared_2534_ = v_isSharedCheck_2544_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_snd_2531_);
lean_dec(v___x_2529_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2544_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v_a_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2539_; 
v_a_2535_ = lean_ctor_get(v_fst_2530_, 0);
lean_inc(v_a_2535_);
lean_dec_ref_known(v_fst_2530_, 1);
v___x_2536_ = l_Lean_MessageData_ofSyntax(v_snd_2531_);
v___x_2537_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1___closed__1);
if (v_isShared_2534_ == 0)
{
lean_ctor_set_tag(v___x_2533_, 7);
lean_ctor_set(v___x_2533_, 1, v___x_2537_);
lean_ctor_set(v___x_2533_, 0, v___x_2536_);
v___x_2539_ = v___x_2533_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v___x_2536_);
lean_ctor_set(v_reuseFailAlloc_2543_, 1, v___x_2537_);
v___x_2539_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; 
v___x_2540_ = l_Lean_Exception_toMessageData(v_a_2535_);
v___x_2541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2539_);
lean_ctor_set(v___x_2541_, 1, v___x_2540_);
v___x_2542_ = lean_array_push(v_b_2522_, v___x_2541_);
v___y_2524_ = v___x_2542_;
goto v___jp_2523_;
}
}
}
else
{
lean_dec(v_fst_2530_);
lean_dec(v___x_2529_);
v___y_2524_ = v_b_2522_;
goto v___jp_2523_;
}
}
else
{
return v_b_2522_;
}
v___jp_2523_:
{
size_t v___x_2525_; size_t v___x_2526_; 
v___x_2525_ = ((size_t)1ULL);
v___x_2526_ = lean_usize_add(v_i_2520_, v___x_2525_);
v_i_2520_ = v___x_2526_;
v_b_2522_ = v___y_2524_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1___boxed(lean_object* v_as_2546_, lean_object* v_i_2547_, lean_object* v_stop_2548_, lean_object* v_b_2549_){
_start:
{
size_t v_i_boxed_2550_; size_t v_stop_boxed_2551_; lean_object* v_res_2552_; 
v_i_boxed_2550_ = lean_unbox_usize(v_i_2547_);
lean_dec(v_i_2547_);
v_stop_boxed_2551_ = lean_unbox_usize(v_stop_2548_);
lean_dec(v_stop_2548_);
v_res_2552_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1(v_as_2546_, v_i_boxed_2550_, v_stop_boxed_2551_, v_b_2549_);
lean_dec_ref(v_as_2546_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1(lean_object* v_as_2553_, lean_object* v_start_2554_, lean_object* v_stop_2555_){
_start:
{
lean_object* v___x_2556_; uint8_t v___x_2557_; 
v___x_2556_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___closed__1));
v___x_2557_ = lean_nat_dec_lt(v_start_2554_, v_stop_2555_);
if (v___x_2557_ == 0)
{
return v___x_2556_;
}
else
{
lean_object* v___x_2558_; uint8_t v___x_2559_; 
v___x_2558_ = lean_array_get_size(v_as_2553_);
v___x_2559_ = lean_nat_dec_le(v_stop_2555_, v___x_2558_);
if (v___x_2559_ == 0)
{
uint8_t v___x_2560_; 
v___x_2560_ = lean_nat_dec_lt(v_start_2554_, v___x_2558_);
if (v___x_2560_ == 0)
{
return v___x_2556_;
}
else
{
size_t v___x_2561_; size_t v___x_2562_; lean_object* v___x_2563_; 
v___x_2561_ = lean_usize_of_nat(v_start_2554_);
v___x_2562_ = lean_usize_of_nat(v___x_2558_);
v___x_2563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1(v_as_2553_, v___x_2561_, v___x_2562_, v___x_2556_);
return v___x_2563_;
}
}
else
{
size_t v___x_2564_; size_t v___x_2565_; lean_object* v___x_2566_; 
v___x_2564_ = lean_usize_of_nat(v_start_2554_);
v___x_2565_ = lean_usize_of_nat(v_stop_2555_);
v___x_2566_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1(v_as_2553_, v___x_2564_, v___x_2565_, v___x_2556_);
return v___x_2566_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1___boxed(lean_object* v_as_2567_, lean_object* v_start_2568_, lean_object* v_stop_2569_){
_start:
{
lean_object* v_res_2570_; 
v_res_2570_ = l_Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1(v_as_2567_, v_start_2568_, v_stop_2569_);
lean_dec(v_stop_2569_);
lean_dec(v_start_2568_);
lean_dec_ref(v_as_2567_);
return v_res_2570_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__0(size_t v_sz_2571_, size_t v_i_2572_, lean_object* v_bs_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_){
_start:
{
uint8_t v___x_2582_; 
v___x_2582_ = lean_usize_dec_lt(v_i_2572_, v_sz_2571_);
if (v___x_2582_ == 0)
{
lean_object* v___x_2583_; 
v___x_2583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2583_, 0, v_bs_2573_);
return v___x_2583_;
}
else
{
lean_object* v_v_2584_; lean_object* v___x_2585_; lean_object* v_bs_x27_2586_; lean_object* v_a_2588_; lean_object* v___x_2593_; 
v_v_2584_ = lean_array_uget(v_bs_2573_, v_i_2572_);
v___x_2585_ = lean_unsigned_to_nat(0u);
v_bs_x27_2586_ = lean_array_uset(v_bs_2573_, v_i_2572_, v___x_2585_);
v___x_2593_ = l_Lean_Elab_Term_Quotation_precheck(v_v_2584_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v_a_2594_; lean_object* v___x_2595_; 
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
lean_inc(v_a_2594_);
lean_dec_ref_known(v___x_2593_, 1);
v___x_2595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2595_, 0, v_a_2594_);
v_a_2588_ = v___x_2595_;
goto v___jp_2587_;
}
else
{
lean_object* v_a_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2608_; 
v_a_2596_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2598_ = v___x_2593_;
v_isShared_2599_ = v_isSharedCheck_2608_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_a_2596_);
lean_dec(v___x_2593_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2608_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
uint8_t v___y_2601_; uint8_t v___x_2606_; 
v___x_2606_ = l_Lean_Exception_isInterrupt(v_a_2596_);
if (v___x_2606_ == 0)
{
uint8_t v___x_2607_; 
lean_inc(v_a_2596_);
v___x_2607_ = l_Lean_Exception_isRuntime(v_a_2596_);
v___y_2601_ = v___x_2607_;
goto v___jp_2600_;
}
else
{
v___y_2601_ = v___x_2606_;
goto v___jp_2600_;
}
v___jp_2600_:
{
if (v___y_2601_ == 0)
{
lean_object* v___x_2602_; 
lean_del_object(v___x_2598_);
v___x_2602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2602_, 0, v_a_2596_);
v_a_2588_ = v___x_2602_;
goto v___jp_2587_;
}
else
{
lean_object* v___x_2604_; 
lean_dec_ref(v_bs_x27_2586_);
if (v_isShared_2599_ == 0)
{
v___x_2604_ = v___x_2598_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v_a_2596_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
return v___x_2604_;
}
}
}
}
}
v___jp_2587_:
{
size_t v___x_2589_; size_t v___x_2590_; lean_object* v___x_2591_; 
v___x_2589_ = ((size_t)1ULL);
v___x_2590_ = lean_usize_add(v_i_2572_, v___x_2589_);
v___x_2591_ = lean_array_uset(v_bs_x27_2586_, v_i_2572_, v_a_2588_);
v_i_2572_ = v___x_2590_;
v_bs_2573_ = v___x_2591_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__0___boxed(lean_object* v_sz_2609_, lean_object* v_i_2610_, lean_object* v_bs_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_){
_start:
{
size_t v_sz_boxed_2620_; size_t v_i_boxed_2621_; lean_object* v_res_2622_; 
v_sz_boxed_2620_ = lean_unbox_usize(v_sz_2609_);
lean_dec(v_sz_2609_);
v_i_boxed_2621_ = lean_unbox_usize(v_i_2610_);
lean_dec(v_i_2610_);
v_res_2622_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__0(v_sz_boxed_2620_, v_i_boxed_2621_, v_bs_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2615_);
lean_dec(v___y_2614_);
lean_dec_ref(v___y_2613_);
lean_dec(v___y_2612_);
return v_res_2622_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckChoice___closed__1(void){
_start:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2624_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckChoice___closed__0));
v___x_2625_ = l_Lean_stringToMessageData(v___x_2624_);
return v___x_2625_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckChoice___closed__3(void){
_start:
{
lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___x_2627_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckChoice___closed__2));
v___x_2628_ = l_Lean_stringToMessageData(v___x_2627_);
return v___x_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckChoice(lean_object* v_stx_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_){
_start:
{
lean_object* v___x_2638_; size_t v_sz_2639_; size_t v___x_2640_; lean_object* v___x_2641_; 
v___x_2638_ = l_Lean_Syntax_getArgs(v_stx_2629_);
v_sz_2639_ = lean_array_size(v___x_2638_);
v___x_2640_ = ((size_t)0ULL);
lean_inc_ref(v___x_2638_);
v___x_2641_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__0(v_sz_2639_, v___x_2640_, v___x_2638_, v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_, v_a_2634_, v_a_2635_, v_a_2636_);
if (lean_obj_tag(v___x_2641_) == 0)
{
lean_object* v_a_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2663_; 
v_a_2642_ = lean_ctor_get(v___x_2641_, 0);
v_isSharedCheck_2663_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2644_ = v___x_2641_;
v_isShared_2645_ = v_isSharedCheck_2663_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_a_2642_);
lean_dec(v___x_2641_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2663_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; uint8_t v___x_2651_; 
v___x_2646_ = l_Array_zip___redArg(v_a_2642_, v___x_2638_);
lean_dec_ref(v___x_2638_);
lean_dec(v_a_2642_);
v___x_2647_ = lean_unsigned_to_nat(0u);
v___x_2648_ = lean_array_get_size(v___x_2646_);
v___x_2649_ = l_Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1(v___x_2646_, v___x_2647_, v___x_2648_);
lean_dec_ref(v___x_2646_);
v___x_2650_ = lean_array_get_size(v___x_2649_);
v___x_2651_ = lean_nat_dec_eq(v___x_2650_, v___x_2647_);
if (v___x_2651_ == 0)
{
lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; 
lean_del_object(v___x_2644_);
v___x_2652_ = lean_obj_once(&l_Lean_Elab_Term_Quotation_precheckChoice___closed__1, &l_Lean_Elab_Term_Quotation_precheckChoice___closed__1_once, _init_l_Lean_Elab_Term_Quotation_precheckChoice___closed__1);
v___x_2653_ = lean_array_to_list(v___x_2649_);
v___x_2654_ = lean_obj_once(&l_Lean_Elab_Term_Quotation_precheckChoice___closed__3, &l_Lean_Elab_Term_Quotation_precheckChoice___closed__3_once, _init_l_Lean_Elab_Term_Quotation_precheckChoice___closed__3);
v___x_2655_ = l_Lean_MessageData_joinSep(v___x_2653_, v___x_2654_);
v___x_2656_ = l_Lean_indentD(v___x_2655_);
v___x_2657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2657_, 0, v___x_2652_);
lean_ctor_set(v___x_2657_, 1, v___x_2656_);
v___x_2658_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1___redArg(v_stx_2629_, v___x_2657_, v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_, v_a_2634_, v_a_2635_, v_a_2636_);
return v___x_2658_;
}
else
{
lean_object* v___x_2659_; lean_object* v___x_2661_; 
lean_dec_ref(v___x_2649_);
v___x_2659_ = lean_box(0);
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 0, v___x_2659_);
v___x_2661_ = v___x_2644_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v___x_2659_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
}
}
else
{
lean_object* v_a_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2671_; 
lean_dec_ref(v___x_2638_);
v_a_2664_ = lean_ctor_get(v___x_2641_, 0);
v_isSharedCheck_2671_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2666_ = v___x_2641_;
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_a_2664_);
lean_dec(v___x_2641_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___x_2669_; 
if (v_isShared_2667_ == 0)
{
v___x_2669_ = v___x_2666_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v_a_2664_);
v___x_2669_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
return v___x_2669_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckChoice___boxed(lean_object* v_stx_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_){
_start:
{
lean_object* v_res_2681_; 
v_res_2681_ = l_Lean_Elab_Term_Quotation_precheckChoice(v_stx_2672_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_);
lean_dec(v_a_2679_);
lean_dec_ref(v_a_2678_);
lean_dec(v_a_2677_);
lean_dec_ref(v_a_2676_);
lean_dec(v_a_2675_);
lean_dec_ref(v_a_2674_);
lean_dec(v_a_2673_);
lean_dec(v_stx_2672_);
return v_res_2681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1(){
_start:
{
lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; 
v___x_2693_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
v___x_2694_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__1));
v___x_2695_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__3));
v___x_2696_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckChoice___boxed), 9, 0);
v___x_2697_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2693_, v___x_2694_, v___x_2695_, v___x_2696_);
return v___x_2697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___boxed(lean_object* v_a_2698_){
_start:
{
lean_object* v_res_2699_; 
v_res_2699_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1();
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___lam__0(lean_object* v_singleQuot_2700_, lean_object* v_x_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_){
_start:
{
lean_object* v___x_2709_; 
v___x_2709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2709_, 0, v_singleQuot_2700_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___lam__0___boxed(lean_object* v_singleQuot_2710_, lean_object* v_x_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
lean_object* v_res_2719_; 
v_res_2719_ = l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___lam__0(v_singleQuot_2710_, v_x_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_);
lean_dec(v___y_2717_);
lean_dec_ref(v___y_2716_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
lean_dec(v___y_2713_);
lean_dec_ref(v___y_2712_);
lean_dec(v_x_2711_);
return v_res_2719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot(lean_object* v_stx_2720_, lean_object* v_expectedType_x3f_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_){
_start:
{
lean_object* v___x_2729_; lean_object* v_singleQuot_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; 
v___x_2729_ = lean_unsigned_to_nat(1u);
v_singleQuot_2730_ = l_Lean_Syntax_getArg(v_stx_2720_, v___x_2729_);
lean_inc(v_singleQuot_2730_);
v___x_2731_ = l_Lean_Syntax_getQuotContent(v_singleQuot_2730_);
v___x_2732_ = l_Lean_Elab_Term_Quotation_runPrecheck(v___x_2731_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_);
if (lean_obj_tag(v___x_2732_) == 0)
{
lean_object* v___f_2733_; lean_object* v___x_2734_; 
lean_dec_ref_known(v___x_2732_, 1);
v___f_2733_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___lam__0___boxed), 9, 1);
lean_closure_set(v___f_2733_, 0, v_singleQuot_2730_);
v___x_2734_ = l_Lean_Elab_Term_adaptExpander(v___f_2733_, v_stx_2720_, v_expectedType_x3f_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_);
return v___x_2734_;
}
else
{
lean_object* v_a_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2742_; 
lean_dec(v_singleQuot_2730_);
lean_dec(v_expectedType_x3f_2721_);
lean_dec(v_stx_2720_);
v_a_2735_ = lean_ctor_get(v___x_2732_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v___x_2732_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2737_ = v___x_2732_;
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_a_2735_);
lean_dec(v___x_2732_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2740_; 
if (v_isShared_2738_ == 0)
{
v___x_2740_ = v___x_2737_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_a_2735_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___boxed(lean_object* v_stx_2743_, lean_object* v_expectedType_x3f_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l_Lean_Elab_Term_Quotation_elabPrecheckedQuot(v_stx_2743_, v_expectedType_x3f_2744_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_);
lean_dec(v_a_2750_);
lean_dec_ref(v_a_2749_);
lean_dec(v_a_2748_);
lean_dec_ref(v_a_2747_);
lean_dec(v_a_2746_);
lean_dec_ref(v_a_2745_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1(){
_start:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; 
v___x_2767_ = l_Lean_Elab_Term_termElabAttribute;
v___x_2768_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__1));
v___x_2769_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3));
v___x_2770_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___boxed), 9, 0);
v___x_2771_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2767_, v___x_2768_, v___x_2769_, v___x_2770_);
return v___x_2771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___boxed(lean_object* v_a_2772_){
_start:
{
lean_object* v_res_2773_; 
v_res_2773_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1();
return v_res_2773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3(){
_start:
{
lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2800_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3));
v___x_2801_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__6));
v___x_2802_ = l_Lean_addBuiltinDeclarationRanges(v___x_2800_, v___x_2801_);
return v___x_2802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___boxed(lean_object* v_a_2803_){
_start:
{
lean_object* v_res_2804_; 
v_res_2804_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3();
return v_res_2804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinrel(lean_object* v_x_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_){
_start:
{
lean_object* v___x_2820_; uint8_t v___x_2821_; 
v___x_2820_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckBinrel___closed__1));
lean_inc(v_x_2811_);
v___x_2821_ = l_Lean_Syntax_isOfKind(v_x_2811_, v___x_2820_);
if (v___x_2821_ == 0)
{
lean_object* v___x_2822_; 
lean_dec(v_x_2811_);
v___x_2822_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
return v___x_2822_;
}
else
{
lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; 
v___x_2823_ = lean_unsigned_to_nat(1u);
v___x_2824_ = l_Lean_Syntax_getArg(v_x_2811_, v___x_2823_);
v___x_2825_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2824_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; 
lean_dec_ref_known(v___x_2825_, 1);
v___x_2826_ = lean_unsigned_to_nat(2u);
v___x_2827_ = l_Lean_Syntax_getArg(v_x_2811_, v___x_2826_);
v___x_2828_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2827_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_);
if (lean_obj_tag(v___x_2828_) == 0)
{
lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; 
lean_dec_ref_known(v___x_2828_, 1);
v___x_2829_ = lean_unsigned_to_nat(3u);
v___x_2830_ = l_Lean_Syntax_getArg(v_x_2811_, v___x_2829_);
lean_dec(v_x_2811_);
v___x_2831_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2830_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_);
return v___x_2831_;
}
else
{
lean_dec(v_x_2811_);
return v___x_2828_;
}
}
else
{
lean_dec(v_x_2811_);
return v___x_2825_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinrel___boxed(lean_object* v_x_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_){
_start:
{
lean_object* v_res_2841_; 
v_res_2841_ = l_Lean_Elab_Term_Quotation_precheckBinrel(v_x_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_);
lean_dec(v_a_2839_);
lean_dec_ref(v_a_2838_);
lean_dec(v_a_2837_);
lean_dec_ref(v_a_2836_);
lean_dec(v_a_2835_);
lean_dec_ref(v_a_2834_);
lean_dec(v_a_2833_);
return v_res_2841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1(){
_start:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; 
v___x_2850_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
v___x_2851_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckBinrel___closed__1));
v___x_2852_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__1));
v___x_2853_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckBinrel___boxed), 9, 0);
v___x_2854_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2850_, v___x_2851_, v___x_2852_, v___x_2853_);
return v___x_2854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___boxed(lean_object* v_a_2855_){
_start:
{
lean_object* v_res_2856_; 
v_res_2856_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1();
return v_res_2856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinrelNoProp(lean_object* v_x_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_){
_start:
{
lean_object* v___x_2872_; uint8_t v___x_2873_; 
v___x_2872_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__1));
lean_inc(v_x_2863_);
v___x_2873_ = l_Lean_Syntax_isOfKind(v_x_2863_, v___x_2872_);
if (v___x_2873_ == 0)
{
lean_object* v___x_2874_; 
lean_dec(v_x_2863_);
v___x_2874_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
return v___x_2874_;
}
else
{
lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; 
v___x_2875_ = lean_unsigned_to_nat(1u);
v___x_2876_ = l_Lean_Syntax_getArg(v_x_2863_, v___x_2875_);
v___x_2877_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2876_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_);
if (lean_obj_tag(v___x_2877_) == 0)
{
lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; 
lean_dec_ref_known(v___x_2877_, 1);
v___x_2878_ = lean_unsigned_to_nat(2u);
v___x_2879_ = l_Lean_Syntax_getArg(v_x_2863_, v___x_2878_);
v___x_2880_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2879_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_);
if (lean_obj_tag(v___x_2880_) == 0)
{
lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; 
lean_dec_ref_known(v___x_2880_, 1);
v___x_2881_ = lean_unsigned_to_nat(3u);
v___x_2882_ = l_Lean_Syntax_getArg(v_x_2863_, v___x_2881_);
lean_dec(v_x_2863_);
v___x_2883_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2882_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_);
return v___x_2883_;
}
else
{
lean_dec(v_x_2863_);
return v___x_2880_;
}
}
else
{
lean_dec(v_x_2863_);
return v___x_2877_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___boxed(lean_object* v_x_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_){
_start:
{
lean_object* v_res_2893_; 
v_res_2893_ = l_Lean_Elab_Term_Quotation_precheckBinrelNoProp(v_x_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_);
lean_dec(v_a_2891_);
lean_dec_ref(v_a_2890_);
lean_dec(v_a_2889_);
lean_dec_ref(v_a_2888_);
lean_dec(v_a_2887_);
lean_dec_ref(v_a_2886_);
lean_dec(v_a_2885_);
return v_res_2893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1(){
_start:
{
lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; 
v___x_2902_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
v___x_2903_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__1));
v___x_2904_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__1));
v___x_2905_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___boxed), 9, 0);
v___x_2906_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2902_, v___x_2903_, v___x_2904_, v___x_2905_);
return v___x_2906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___boxed(lean_object* v_a_2907_){
_start:
{
lean_object* v_res_2908_; 
v_res_2908_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1();
return v_res_2908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinop(lean_object* v_x_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_){
_start:
{
lean_object* v___x_2924_; uint8_t v___x_2925_; 
v___x_2924_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckBinop___closed__1));
lean_inc(v_x_2915_);
v___x_2925_ = l_Lean_Syntax_isOfKind(v_x_2915_, v___x_2924_);
if (v___x_2925_ == 0)
{
lean_object* v___x_2926_; 
lean_dec(v_x_2915_);
v___x_2926_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
return v___x_2926_;
}
else
{
lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; 
v___x_2927_ = lean_unsigned_to_nat(1u);
v___x_2928_ = l_Lean_Syntax_getArg(v_x_2915_, v___x_2927_);
v___x_2929_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2928_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_, v_a_2922_);
if (lean_obj_tag(v___x_2929_) == 0)
{
lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; 
lean_dec_ref_known(v___x_2929_, 1);
v___x_2930_ = lean_unsigned_to_nat(2u);
v___x_2931_ = l_Lean_Syntax_getArg(v_x_2915_, v___x_2930_);
v___x_2932_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2931_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_, v_a_2922_);
if (lean_obj_tag(v___x_2932_) == 0)
{
lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; 
lean_dec_ref_known(v___x_2932_, 1);
v___x_2933_ = lean_unsigned_to_nat(3u);
v___x_2934_ = l_Lean_Syntax_getArg(v_x_2915_, v___x_2933_);
lean_dec(v_x_2915_);
v___x_2935_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2934_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_, v_a_2922_);
return v___x_2935_;
}
else
{
lean_dec(v_x_2915_);
return v___x_2932_;
}
}
else
{
lean_dec(v_x_2915_);
return v___x_2929_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinop___boxed(lean_object* v_x_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_){
_start:
{
lean_object* v_res_2945_; 
v_res_2945_ = l_Lean_Elab_Term_Quotation_precheckBinop(v_x_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_, v_a_2943_);
lean_dec(v_a_2943_);
lean_dec_ref(v_a_2942_);
lean_dec(v_a_2941_);
lean_dec_ref(v_a_2940_);
lean_dec(v_a_2939_);
lean_dec_ref(v_a_2938_);
lean_dec(v_a_2937_);
return v_res_2945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1(){
_start:
{
lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; 
v___x_2954_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
v___x_2955_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckBinop___closed__1));
v___x_2956_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__1));
v___x_2957_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckBinop___boxed), 9, 0);
v___x_2958_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2954_, v___x_2955_, v___x_2956_, v___x_2957_);
return v___x_2958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___boxed(lean_object* v_a_2959_){
_start:
{
lean_object* v_res_2960_; 
v_res_2960_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1();
return v_res_2960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinopLazy(lean_object* v_x_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_){
_start:
{
lean_object* v___x_2976_; uint8_t v___x_2977_; 
v___x_2976_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__1));
lean_inc(v_x_2967_);
v___x_2977_ = l_Lean_Syntax_isOfKind(v_x_2967_, v___x_2976_);
if (v___x_2977_ == 0)
{
lean_object* v___x_2978_; 
lean_dec(v_x_2967_);
v___x_2978_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
return v___x_2978_;
}
else
{
lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
v___x_2979_ = lean_unsigned_to_nat(1u);
v___x_2980_ = l_Lean_Syntax_getArg(v_x_2967_, v___x_2979_);
v___x_2981_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2980_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_2981_) == 0)
{
lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; 
lean_dec_ref_known(v___x_2981_, 1);
v___x_2982_ = lean_unsigned_to_nat(2u);
v___x_2983_ = l_Lean_Syntax_getArg(v_x_2967_, v___x_2982_);
v___x_2984_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2983_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_2984_) == 0)
{
lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; 
lean_dec_ref_known(v___x_2984_, 1);
v___x_2985_ = lean_unsigned_to_nat(3u);
v___x_2986_ = l_Lean_Syntax_getArg(v_x_2967_, v___x_2985_);
lean_dec(v_x_2967_);
v___x_2987_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2986_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
return v___x_2987_;
}
else
{
lean_dec(v_x_2967_);
return v___x_2984_;
}
}
else
{
lean_dec(v_x_2967_);
return v___x_2981_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinopLazy___boxed(lean_object* v_x_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_){
_start:
{
lean_object* v_res_2997_; 
v_res_2997_ = l_Lean_Elab_Term_Quotation_precheckBinopLazy(v_x_2988_, v_a_2989_, v_a_2990_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_, v_a_2995_);
lean_dec(v_a_2995_);
lean_dec_ref(v_a_2994_);
lean_dec(v_a_2993_);
lean_dec_ref(v_a_2992_);
lean_dec(v_a_2991_);
lean_dec_ref(v_a_2990_);
lean_dec(v_a_2989_);
return v_res_2997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1(){
_start:
{
lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___x_3006_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
v___x_3007_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__1));
v___x_3008_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__1));
v___x_3009_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckBinopLazy___boxed), 9, 0);
v___x_3010_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3006_, v___x_3007_, v___x_3008_, v___x_3009_);
return v___x_3010_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___boxed(lean_object* v_a_3011_){
_start:
{
lean_object* v_res_3012_; 
v_res_3012_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1();
return v_res_3012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckLeftact(lean_object* v_x_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_){
_start:
{
lean_object* v___x_3028_; uint8_t v___x_3029_; 
v___x_3028_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckLeftact___closed__1));
lean_inc(v_x_3019_);
v___x_3029_ = l_Lean_Syntax_isOfKind(v_x_3019_, v___x_3028_);
if (v___x_3029_ == 0)
{
lean_object* v___x_3030_; 
lean_dec(v_x_3019_);
v___x_3030_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
return v___x_3030_;
}
else
{
lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___x_3031_ = lean_unsigned_to_nat(1u);
v___x_3032_ = l_Lean_Syntax_getArg(v_x_3019_, v___x_3031_);
v___x_3033_ = l_Lean_Elab_Term_Quotation_precheck(v___x_3032_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_);
if (lean_obj_tag(v___x_3033_) == 0)
{
lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; 
lean_dec_ref_known(v___x_3033_, 1);
v___x_3034_ = lean_unsigned_to_nat(2u);
v___x_3035_ = l_Lean_Syntax_getArg(v_x_3019_, v___x_3034_);
v___x_3036_ = l_Lean_Elab_Term_Quotation_precheck(v___x_3035_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_);
if (lean_obj_tag(v___x_3036_) == 0)
{
lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; 
lean_dec_ref_known(v___x_3036_, 1);
v___x_3037_ = lean_unsigned_to_nat(3u);
v___x_3038_ = l_Lean_Syntax_getArg(v_x_3019_, v___x_3037_);
lean_dec(v_x_3019_);
v___x_3039_ = l_Lean_Elab_Term_Quotation_precheck(v___x_3038_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_);
return v___x_3039_;
}
else
{
lean_dec(v_x_3019_);
return v___x_3036_;
}
}
else
{
lean_dec(v_x_3019_);
return v___x_3033_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckLeftact___boxed(lean_object* v_x_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_){
_start:
{
lean_object* v_res_3049_; 
v_res_3049_ = l_Lean_Elab_Term_Quotation_precheckLeftact(v_x_3040_, v_a_3041_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_);
lean_dec(v_a_3047_);
lean_dec_ref(v_a_3046_);
lean_dec(v_a_3045_);
lean_dec_ref(v_a_3044_);
lean_dec(v_a_3043_);
lean_dec_ref(v_a_3042_);
lean_dec(v_a_3041_);
return v_res_3049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1(){
_start:
{
lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; 
v___x_3058_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
v___x_3059_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckLeftact___closed__1));
v___x_3060_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__1));
v___x_3061_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckLeftact___boxed), 9, 0);
v___x_3062_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3058_, v___x_3059_, v___x_3060_, v___x_3061_);
return v___x_3062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___boxed(lean_object* v_a_3063_){
_start:
{
lean_object* v_res_3064_; 
v_res_3064_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1();
return v_res_3064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckRightact(lean_object* v_x_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_){
_start:
{
lean_object* v___x_3080_; uint8_t v___x_3081_; 
v___x_3080_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckRightact___closed__1));
lean_inc(v_x_3071_);
v___x_3081_ = l_Lean_Syntax_isOfKind(v_x_3071_, v___x_3080_);
if (v___x_3081_ == 0)
{
lean_object* v___x_3082_; 
lean_dec(v_x_3071_);
v___x_3082_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
return v___x_3082_;
}
else
{
lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3083_ = lean_unsigned_to_nat(1u);
v___x_3084_ = l_Lean_Syntax_getArg(v_x_3071_, v___x_3083_);
v___x_3085_ = l_Lean_Elab_Term_Quotation_precheck(v___x_3084_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_);
if (lean_obj_tag(v___x_3085_) == 0)
{
lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; 
lean_dec_ref_known(v___x_3085_, 1);
v___x_3086_ = lean_unsigned_to_nat(2u);
v___x_3087_ = l_Lean_Syntax_getArg(v_x_3071_, v___x_3086_);
v___x_3088_ = l_Lean_Elab_Term_Quotation_precheck(v___x_3087_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_);
if (lean_obj_tag(v___x_3088_) == 0)
{
lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
lean_dec_ref_known(v___x_3088_, 1);
v___x_3089_ = lean_unsigned_to_nat(3u);
v___x_3090_ = l_Lean_Syntax_getArg(v_x_3071_, v___x_3089_);
lean_dec(v_x_3071_);
v___x_3091_ = l_Lean_Elab_Term_Quotation_precheck(v___x_3090_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_);
return v___x_3091_;
}
else
{
lean_dec(v_x_3071_);
return v___x_3088_;
}
}
else
{
lean_dec(v_x_3071_);
return v___x_3085_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckRightact___boxed(lean_object* v_x_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_){
_start:
{
lean_object* v_res_3101_; 
v_res_3101_ = l_Lean_Elab_Term_Quotation_precheckRightact(v_x_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_);
lean_dec(v_a_3099_);
lean_dec_ref(v_a_3098_);
lean_dec(v_a_3097_);
lean_dec_ref(v_a_3096_);
lean_dec(v_a_3095_);
lean_dec_ref(v_a_3094_);
lean_dec(v_a_3093_);
return v_res_3101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1(){
_start:
{
lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3110_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
v___x_3111_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckRightact___closed__1));
v___x_3112_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__1));
v___x_3113_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckRightact___boxed), 9, 0);
v___x_3114_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3110_, v___x_3111_, v___x_3112_, v___x_3113_);
return v___x_3114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___boxed(lean_object* v_a_3115_){
_start:
{
lean_object* v_res_3116_; 
v_res_3116_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1();
return v_res_3116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckUnop(lean_object* v_x_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_){
_start:
{
lean_object* v___x_3132_; uint8_t v___x_3133_; 
v___x_3132_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckUnop___closed__1));
lean_inc(v_x_3123_);
v___x_3133_ = l_Lean_Syntax_isOfKind(v_x_3123_, v___x_3132_);
if (v___x_3133_ == 0)
{
lean_object* v___x_3134_; 
lean_dec(v_x_3123_);
v___x_3134_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
return v___x_3134_;
}
else
{
lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; 
v___x_3135_ = lean_unsigned_to_nat(1u);
v___x_3136_ = l_Lean_Syntax_getArg(v_x_3123_, v___x_3135_);
v___x_3137_ = l_Lean_Elab_Term_Quotation_precheck(v___x_3136_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_, v_a_3128_, v_a_3129_, v_a_3130_);
if (lean_obj_tag(v___x_3137_) == 0)
{
lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; 
lean_dec_ref_known(v___x_3137_, 1);
v___x_3138_ = lean_unsigned_to_nat(2u);
v___x_3139_ = l_Lean_Syntax_getArg(v_x_3123_, v___x_3138_);
lean_dec(v_x_3123_);
v___x_3140_ = l_Lean_Elab_Term_Quotation_precheck(v___x_3139_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_, v_a_3128_, v_a_3129_, v_a_3130_);
return v___x_3140_;
}
else
{
lean_dec(v_x_3123_);
return v___x_3137_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckUnop___boxed(lean_object* v_x_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_){
_start:
{
lean_object* v_res_3150_; 
v_res_3150_ = l_Lean_Elab_Term_Quotation_precheckUnop(v_x_3141_, v_a_3142_, v_a_3143_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_);
lean_dec(v_a_3148_);
lean_dec_ref(v_a_3147_);
lean_dec(v_a_3146_);
lean_dec_ref(v_a_3145_);
lean_dec(v_a_3144_);
lean_dec_ref(v_a_3143_);
lean_dec(v_a_3142_);
return v_res_3150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1(){
_start:
{
lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3159_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
v___x_3160_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckUnop___closed__1));
v___x_3161_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__1));
v___x_3162_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckUnop___boxed), 9, 0);
v___x_3163_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3159_, v___x_3160_, v___x_3161_, v___x_3162_);
return v___x_3163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___boxed(lean_object* v_a_3164_){
_start:
{
lean_object* v_res_3165_; 
v_res_3165_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1();
return v_res_3165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckHygieneInfo___redArg(){
_start:
{
lean_object* v___x_3167_; lean_object* v___x_3168_; 
v___x_3167_ = lean_box(0);
v___x_3168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3168_, 0, v___x_3167_);
return v___x_3168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckHygieneInfo___redArg___boxed(lean_object* v_a_3169_){
_start:
{
lean_object* v_res_3170_; 
v_res_3170_ = l_Lean_Elab_Term_Quotation_precheckHygieneInfo___redArg();
return v_res_3170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckHygieneInfo(lean_object* v_x_3171_, lean_object* v_a_3172_, lean_object* v_a_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_){
_start:
{
lean_object* v___x_3180_; 
v___x_3180_ = l_Lean_Elab_Term_Quotation_precheckHygieneInfo___redArg();
return v___x_3180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckHygieneInfo___boxed(lean_object* v_x_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_){
_start:
{
lean_object* v_res_3190_; 
v_res_3190_ = l_Lean_Elab_Term_Quotation_precheckHygieneInfo(v_x_3181_, v_a_3182_, v_a_3183_, v_a_3184_, v_a_3185_, v_a_3186_, v_a_3187_, v_a_3188_);
lean_dec(v_a_3188_);
lean_dec_ref(v_a_3187_);
lean_dec(v_a_3186_);
lean_dec_ref(v_a_3185_);
lean_dec(v_a_3184_);
lean_dec_ref(v_a_3183_);
lean_dec(v_a_3182_);
lean_dec(v_x_3181_);
return v_res_3190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1(){
_start:
{
lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; 
v___x_3204_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
v___x_3205_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__0));
v___x_3206_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__2));
v___x_3207_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckHygieneInfo___boxed), 9, 0);
v___x_3208_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3204_, v___x_3205_, v___x_3206_, v___x_3207_);
return v___x_3208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___boxed(lean_object* v_a_3209_){
_start:
{
lean_object* v_res_3210_; 
v_res_3210_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1();
return v_res_3210_;
}
}
lean_object* runtime_initialize_Lean_Elab_Quotation_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_DeprecatedSyntax(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Quotation_Precheck(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Quotation_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_DeprecatedSyntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Term_Quotation_quotPrecheck = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Term_Quotation_quotPrecheck);
lean_dec_ref(res);
res = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Term_Quotation_quotPrecheck_allowSectionVars = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Term_Quotation_quotPrecheck_allowSectionVars);
lean_dec_ref(res);
res = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Term_Quotation_precheckAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckAttribute);
lean_dec_ref(res);
res = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Quotation_Precheck(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Quotation_Util(uint8_t builtin);
lean_object* initialize_Lean_Elab_DeprecatedSyntax(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Quotation_Precheck(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Quotation_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DeprecatedSyntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Quotation_Precheck(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Quotation_Precheck(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Quotation_Precheck(builtin);
}
#ifdef __cplusplus
}
#endif
