// Lean compiler output
// Module: Lean.Elab.Quotation.Precheck
// Imports: public import Lean.Elab.Quotation.Util import Lean.Elab.DeprecatedSyntax.Basic
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
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited___redArg();
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___redArg();
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
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
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_checkDeprecatedQuotedSyntax(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_evalIdentKey(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_init___redArg(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_getValues___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
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
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Elab_realizeGlobalNameWithInfos(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
lean_object* l_Lean_extractMacroScopes(lean_object*);
lean_object* l_Lean_MacroScopesView_review(lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Quotation_resolveSectionVariable(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_checkDeprecatedCore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resolveName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getQuotContent(lean_object*);
extern lean_object* l_Lean_Elab_Term_Quotation_hygiene;
extern lean_object* l_Lean_NameSet_empty;
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
static const lean_string_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 521, .m_capacity = 521, .m_length = 520, .m_data = "Registers a double backtick syntax quotation pre-check.\n\n`@[quot_precheck k]` registers a declaration of type `Lean.Elab.Term.Quotation.Precheck` for the\nsyntax node kind `k`. It should implement eager name analysis on the passed syntax by throwing an\nexception on unbound identifiers, and calling `precheck` recursively on nested terms, potentially\nwith an extended local context (`withNewLocal`). Macros without registered precheck hook are\nunfolded, and identifier-less syntax is ultimately assumed to be well-formed."};
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
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4___closed__0 = (const lean_object*)&l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4___closed__0_value;
static const lean_ctor_object l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4___closed__1 = (const lean_object*)&l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4___closed__1_value;
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___lam__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__14___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__14___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__14___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__14___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__14___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__14___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__8_spec__12_spec__15___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__8_spec__12_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__8_spec__12___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__8_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__0;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__1;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__4;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__5_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__5_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__6 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__6_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__7_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__8;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__10;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__11;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__13_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__18_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__20_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6_spec__12___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___closed__0;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___closed__1_value;
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__14(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__8_spec__12(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__8_spec__12_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__8_spec__12_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Term_Quotation_runPrecheck_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Term_Quotation_runPrecheck_spec__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isQuotLocal_loop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isQuotLocal_loop___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isQuotLocal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isQuotLocal___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___closed__1_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
size_t v___x_79_; size_t v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_79_ = ((size_t)0ULL);
v___x_80_ = lean_usize_of_nat(v___x_76_);
lean_inc(v_a_67_);
v___x_81_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Quotation_withNewLocals_spec__0(v_ls_65_, v___x_79_, v___x_80_, v_a_67_);
lean_inc(v_a_73_);
lean_inc_ref(v_a_72_);
lean_inc(v_a_71_);
lean_inc_ref(v_a_70_);
lean_inc(v_a_69_);
lean_inc_ref(v_a_68_);
v___x_82_ = lean_apply_8(v_x_66_, v___x_81_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_, lean_box(0));
return v___x_82_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_withNewLocals___redArg___boxed(lean_object* v_ls_83_, lean_object* v_x_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_Elab_Term_Quotation_withNewLocals___redArg(v_ls_83_, v_x_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_);
lean_dec(v_a_91_);
lean_dec_ref(v_a_90_);
lean_dec(v_a_89_);
lean_dec_ref(v_a_88_);
lean_dec(v_a_87_);
lean_dec_ref(v_a_86_);
lean_dec(v_a_85_);
lean_dec_ref(v_ls_83_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_withNewLocals(lean_object* v_00_u03b1_94_, lean_object* v_ls_95_, lean_object* v_x_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = l_Lean_Elab_Term_Quotation_withNewLocals___redArg(v_ls_95_, v_x_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_withNewLocals___boxed(lean_object* v_00_u03b1_106_, lean_object* v_ls_107_, lean_object* v_x_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Lean_Elab_Term_Quotation_withNewLocals(v_00_u03b1_106_, v_ls_107_, v_x_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_);
lean_dec(v_a_115_);
lean_dec_ref(v_a_114_);
lean_dec(v_a_113_);
lean_dec_ref(v_a_112_);
lean_dec(v_a_111_);
lean_dec_ref(v_a_110_);
lean_dec(v_a_109_);
lean_dec_ref(v_ls_107_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__spec__0(lean_object* v_name_118_, lean_object* v_decl_119_, lean_object* v_ref_120_){
_start:
{
lean_object* v_defValue_122_; lean_object* v_descr_123_; lean_object* v_deprecation_x3f_124_; lean_object* v___x_125_; uint8_t v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v_defValue_122_ = lean_ctor_get(v_decl_119_, 0);
v_descr_123_ = lean_ctor_get(v_decl_119_, 1);
v_deprecation_x3f_124_ = lean_ctor_get(v_decl_119_, 2);
v___x_125_ = lean_alloc_ctor(1, 0, 1);
v___x_126_ = lean_unbox(v_defValue_122_);
lean_ctor_set_uint8(v___x_125_, 0, v___x_126_);
lean_inc(v_deprecation_x3f_124_);
lean_inc_ref(v_descr_123_);
lean_inc_n(v_name_118_, 2);
v___x_127_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_127_, 0, v_name_118_);
lean_ctor_set(v___x_127_, 1, v_ref_120_);
lean_ctor_set(v___x_127_, 2, v___x_125_);
lean_ctor_set(v___x_127_, 3, v_descr_123_);
lean_ctor_set(v___x_127_, 4, v_deprecation_x3f_124_);
v___x_128_ = lean_register_option(v_name_118_, v___x_127_);
if (lean_obj_tag(v___x_128_) == 0)
{
lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_136_; 
v_isSharedCheck_136_ = !lean_is_exclusive(v___x_128_);
if (v_isSharedCheck_136_ == 0)
{
lean_object* v_unused_137_; 
v_unused_137_ = lean_ctor_get(v___x_128_, 0);
lean_dec(v_unused_137_);
v___x_130_ = v___x_128_;
v_isShared_131_ = v_isSharedCheck_136_;
goto v_resetjp_129_;
}
else
{
lean_dec(v___x_128_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_136_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_132_; lean_object* v___x_134_; 
lean_inc(v_defValue_122_);
v___x_132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_132_, 0, v_name_118_);
lean_ctor_set(v___x_132_, 1, v_defValue_122_);
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 0, v___x_132_);
v___x_134_ = v___x_130_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v___x_132_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
else
{
lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_145_; 
lean_dec(v_name_118_);
v_a_138_ = lean_ctor_get(v___x_128_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_128_);
if (v_isSharedCheck_145_ == 0)
{
v___x_140_ = v___x_128_;
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v___x_128_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_143_; 
if (v_isShared_141_ == 0)
{
v___x_143_ = v___x_140_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_a_138_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_146_, lean_object* v_decl_147_, lean_object* v_ref_148_, lean_object* v_a_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Lean_Option_register___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__spec__0(v_name_146_, v_decl_147_, v_ref_148_);
lean_dec_ref(v_decl_147_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_171_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_));
v___x_172_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_));
v___x_173_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_));
v___x_174_ = l_Lean_Option_register___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__spec__0(v___x_171_, v___x_172_, v___x_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4____boxed(lean_object* v_a_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_();
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_195_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4_));
v___x_196_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4_));
v___x_197_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4_));
v___x_198_ = l_Lean_Option_register___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__spec__0(v___x_195_, v___x_196_, v___x_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4____boxed(lean_object* v_a_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4_();
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___lam__0_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_(uint8_t v_builtin_201_, lean_object* v_stx_202_, lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Lean_KeyedDeclsAttribute_evalIdentKey(v_stx_202_, v___y_203_, v___y_204_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___lam__0_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2____boxed(lean_object* v_builtin_207_, lean_object* v_stx_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
uint8_t v_builtin_boxed_212_; lean_object* v_res_213_; 
v_builtin_boxed_212_ = lean_unbox(v_builtin_207_);
v_res_213_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___lam__0_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_(v_builtin_boxed_212_, v_stx_208_, v___y_209_, v___y_210_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___lam__1_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_(uint8_t v_builtin_214_, lean_object* v_declName_215_, lean_object* v_key_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_220_ = lean_box(0);
v___x_221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___lam__1_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2____boxed(lean_object* v_builtin_222_, lean_object* v_declName_223_, lean_object* v_key_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
uint8_t v_builtin_boxed_228_; lean_object* v_res_229_; 
v_builtin_boxed_228_ = lean_unbox(v_builtin_222_);
v_res_229_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___lam__1_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_(v_builtin_boxed_228_, v_declName_223_, v_key_224_, v___y_225_, v___y_226_);
lean_dec(v___y_226_);
lean_dec_ref(v___y_225_);
lean_dec(v_key_224_);
lean_dec(v_declName_223_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_261_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__9_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_));
v___x_262_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__11_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_));
v___x_263_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_261_, v___x_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2____boxed(lean_object* v_a_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_();
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_docString__1(){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_268_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__11_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_));
v___x_269_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_docString__1___closed__0));
v___x_270_ = l_Lean_addBuiltinDocString(v___x_268_, v___x_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_docString__1___boxed(lean_object* v_a_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_docString__1();
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3(){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_299_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__11_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_));
v___x_300_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__6));
v___x_301_ = l_Lean_addBuiltinDeclarationRanges(v___x_299_, v___x_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___boxed(lean_object* v_a_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3();
return v_res_303_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent(lean_object* v_x_307_){
_start:
{
if (lean_obj_tag(v_x_307_) == 3)
{
uint8_t v___x_308_; 
lean_dec_ref_known(v_x_307_, 4);
v___x_308_ = 1;
return v___x_308_;
}
else
{
uint8_t v___x_309_; 
lean_inc(v_x_307_);
v___x_309_ = l_Lean_Syntax_isAnyAntiquot(v_x_307_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; uint8_t v___x_311_; 
v___x_310_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___closed__1));
lean_inc(v_x_307_);
v___x_311_ = l_Lean_Syntax_isOfKind(v_x_307_, v___x_310_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; 
v___x_312_ = l_Lean_Syntax_getArgs(v_x_307_);
lean_dec(v_x_307_);
v___x_313_ = lean_unsigned_to_nat(0u);
v___x_314_ = lean_array_get_size(v___x_312_);
v___x_315_ = lean_nat_dec_lt(v___x_313_, v___x_314_);
if (v___x_315_ == 0)
{
lean_dec_ref(v___x_312_);
return v___x_315_;
}
else
{
if (v___x_315_ == 0)
{
lean_dec_ref(v___x_312_);
return v___x_315_;
}
else
{
size_t v___x_316_; size_t v___x_317_; uint8_t v___x_318_; 
v___x_316_ = ((size_t)0ULL);
v___x_317_ = lean_usize_of_nat(v___x_314_);
v___x_318_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent_spec__0(v___x_312_, v___x_316_, v___x_317_);
lean_dec_ref(v___x_312_);
return v___x_318_;
}
}
}
else
{
lean_dec(v_x_307_);
return v___x_309_;
}
}
else
{
uint8_t v___x_319_; 
lean_dec(v_x_307_);
v___x_319_ = 0;
return v___x_319_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent_spec__0(lean_object* v_as_320_, size_t v_i_321_, size_t v_stop_322_){
_start:
{
uint8_t v___x_323_; 
v___x_323_ = lean_usize_dec_eq(v_i_321_, v_stop_322_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; uint8_t v___x_325_; 
v___x_324_ = lean_array_uget_borrowed(v_as_320_, v_i_321_);
lean_inc(v___x_324_);
v___x_325_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent(v___x_324_);
if (v___x_325_ == 0)
{
size_t v___x_326_; size_t v___x_327_; 
v___x_326_ = ((size_t)1ULL);
v___x_327_ = lean_usize_add(v_i_321_, v___x_326_);
v_i_321_ = v___x_327_;
goto _start;
}
else
{
return v___x_325_;
}
}
else
{
uint8_t v___x_329_; 
v___x_329_ = 0;
return v___x_329_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent_spec__0___boxed(lean_object* v_as_330_, lean_object* v_i_331_, lean_object* v_stop_332_){
_start:
{
size_t v_i_boxed_333_; size_t v_stop_boxed_334_; uint8_t v_res_335_; lean_object* v_r_336_; 
v_i_boxed_333_ = lean_unbox_usize(v_i_331_);
lean_dec(v_i_331_);
v_stop_boxed_334_ = lean_unbox_usize(v_stop_332_);
lean_dec(v_stop_332_);
v_res_335_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent_spec__0(v_as_330_, v_i_boxed_333_, v_stop_boxed_334_);
lean_dec_ref(v_as_330_);
v_r_336_ = lean_box(v_res_335_);
return v_r_336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___boxed(lean_object* v_x_337_){
_start:
{
uint8_t v_res_338_; lean_object* v_r_339_; 
v_res_338_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent(v_x_337_);
v_r_339_ = lean_box(v_res_338_);
return v_r_339_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_340_ = lean_box(0);
v___x_341_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_342_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
lean_ctor_set(v___x_342_, 1, v___x_340_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg(){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__0);
v___x_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___boxed(lean_object* v___y_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__3(lean_object* v_env_348_, lean_object* v___x_349_, lean_object* v_currNamespace_350_, lean_object* v_openDecls_351_, lean_object* v_n_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = l_Lean_ResolveName_resolveGlobalName(v_env_348_, v___x_349_, v_currNamespace_350_, v_openDecls_351_, v_n_352_);
v___x_356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
lean_ctor_set(v___x_356_, 1, v___y_354_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__3___boxed(lean_object* v_env_357_, lean_object* v___x_358_, lean_object* v_currNamespace_359_, lean_object* v_openDecls_360_, lean_object* v_n_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__3(v_env_357_, v___x_358_, v_currNamespace_359_, v_openDecls_360_, v_n_361_, v___y_362_, v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec_ref(v___x_358_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0_spec__1(lean_object* v_msgData_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v___x_371_; lean_object* v_env_372_; uint8_t v___x_373_; lean_object* v_env_374_; lean_object* v___x_375_; lean_object* v_toCold_376_; lean_object* v_mctx_377_; lean_object* v_lctx_378_; lean_object* v_options_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_371_ = lean_st_ref_get(v___y_369_);
v_env_372_ = lean_ctor_get(v___x_371_, 0);
lean_inc_ref(v_env_372_);
lean_dec(v___x_371_);
v___x_373_ = 0;
v_env_374_ = l_Lean_Environment_setRecordingDeps(v_env_372_, v___x_373_);
v___x_375_ = lean_st_ref_get(v___y_367_);
v_toCold_376_ = lean_ctor_get(v___y_368_, 0);
v_mctx_377_ = lean_ctor_get(v___x_375_, 0);
lean_inc_ref(v_mctx_377_);
lean_dec(v___x_375_);
v_lctx_378_ = lean_ctor_get(v___y_366_, 2);
v_options_379_ = lean_ctor_get(v_toCold_376_, 2);
lean_inc_ref(v_options_379_);
lean_inc_ref(v_lctx_378_);
v___x_380_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_380_, 0, v_env_374_);
lean_ctor_set(v___x_380_, 1, v_mctx_377_);
lean_ctor_set(v___x_380_, 2, v_lctx_378_);
lean_ctor_set(v___x_380_, 3, v_options_379_);
v___x_381_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
lean_ctor_set(v___x_381_, 1, v_msgData_365_);
v___x_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0_spec__1(v_msgData_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
return v_res_389_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_390_; double v___x_391_; 
v___x_390_ = lean_unsigned_to_nat(0u);
v___x_391_ = lean_float_of_nat(v___x_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg(lean_object* v_cls_395_, lean_object* v_msg_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v_ref_402_; lean_object* v___x_403_; lean_object* v_a_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_449_; 
v_ref_402_ = lean_ctor_get(v___y_399_, 2);
v___x_403_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0_spec__1(v_msg_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_);
v_a_404_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_449_ == 0)
{
v___x_406_ = v___x_403_;
v_isShared_407_ = v_isSharedCheck_449_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_a_404_);
lean_dec(v___x_403_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_449_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_408_; lean_object* v_traceState_409_; lean_object* v_env_410_; lean_object* v_nextMacroScope_411_; lean_object* v_ngen_412_; lean_object* v_auxDeclNGen_413_; lean_object* v_cache_414_; lean_object* v_recordedDeps_415_; lean_object* v_messages_416_; lean_object* v_infoState_417_; lean_object* v_snapshotTasks_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_448_; 
v___x_408_ = lean_st_ref_take(v___y_400_);
v_traceState_409_ = lean_ctor_get(v___x_408_, 4);
v_env_410_ = lean_ctor_get(v___x_408_, 0);
v_nextMacroScope_411_ = lean_ctor_get(v___x_408_, 1);
v_ngen_412_ = lean_ctor_get(v___x_408_, 2);
v_auxDeclNGen_413_ = lean_ctor_get(v___x_408_, 3);
v_cache_414_ = lean_ctor_get(v___x_408_, 5);
v_recordedDeps_415_ = lean_ctor_get(v___x_408_, 6);
v_messages_416_ = lean_ctor_get(v___x_408_, 7);
v_infoState_417_ = lean_ctor_get(v___x_408_, 8);
v_snapshotTasks_418_ = lean_ctor_get(v___x_408_, 9);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_448_ == 0)
{
v___x_420_ = v___x_408_;
v_isShared_421_ = v_isSharedCheck_448_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_snapshotTasks_418_);
lean_inc(v_infoState_417_);
lean_inc(v_messages_416_);
lean_inc(v_recordedDeps_415_);
lean_inc(v_cache_414_);
lean_inc(v_traceState_409_);
lean_inc(v_auxDeclNGen_413_);
lean_inc(v_ngen_412_);
lean_inc(v_nextMacroScope_411_);
lean_inc(v_env_410_);
lean_dec(v___x_408_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_448_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
uint64_t v_tid_422_; lean_object* v_traces_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_447_; 
v_tid_422_ = lean_ctor_get_uint64(v_traceState_409_, sizeof(void*)*1);
v_traces_423_ = lean_ctor_get(v_traceState_409_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v_traceState_409_);
if (v_isSharedCheck_447_ == 0)
{
v___x_425_ = v_traceState_409_;
v_isShared_426_ = v_isSharedCheck_447_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_traces_423_);
lean_dec(v_traceState_409_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_447_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_427_; lean_object* v___x_428_; double v___x_429_; uint8_t v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_438_; 
v___x_427_ = lean_box(0);
v___x_428_ = lean_box(0);
v___x_429_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___closed__0);
v___x_430_ = 0;
v___x_431_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___closed__1));
v___x_432_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_432_, 0, v_cls_395_);
lean_ctor_set(v___x_432_, 1, v___x_428_);
lean_ctor_set(v___x_432_, 2, v___x_431_);
lean_ctor_set_float(v___x_432_, sizeof(void*)*3, v___x_429_);
lean_ctor_set_float(v___x_432_, sizeof(void*)*3 + 8, v___x_429_);
lean_ctor_set_uint8(v___x_432_, sizeof(void*)*3 + 16, v___x_430_);
v___x_433_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___closed__2));
v___x_434_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_434_, 0, v___x_432_);
lean_ctor_set(v___x_434_, 1, v_a_404_);
lean_ctor_set(v___x_434_, 2, v___x_433_);
lean_inc(v_ref_402_);
v___x_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_435_, 0, v_ref_402_);
lean_ctor_set(v___x_435_, 1, v___x_434_);
v___x_436_ = l_Lean_PersistentArray_push___redArg(v_traces_423_, v___x_435_);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 0, v___x_436_);
v___x_438_ = v___x_425_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v___x_436_);
lean_ctor_set_uint64(v_reuseFailAlloc_446_, sizeof(void*)*1, v_tid_422_);
v___x_438_ = v_reuseFailAlloc_446_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
lean_object* v___x_440_; 
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 4, v___x_438_);
v___x_440_ = v___x_420_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_env_410_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v_nextMacroScope_411_);
lean_ctor_set(v_reuseFailAlloc_445_, 2, v_ngen_412_);
lean_ctor_set(v_reuseFailAlloc_445_, 3, v_auxDeclNGen_413_);
lean_ctor_set(v_reuseFailAlloc_445_, 4, v___x_438_);
lean_ctor_set(v_reuseFailAlloc_445_, 5, v_cache_414_);
lean_ctor_set(v_reuseFailAlloc_445_, 6, v_recordedDeps_415_);
lean_ctor_set(v_reuseFailAlloc_445_, 7, v_messages_416_);
lean_ctor_set(v_reuseFailAlloc_445_, 8, v_infoState_417_);
lean_ctor_set(v_reuseFailAlloc_445_, 9, v_snapshotTasks_418_);
v___x_440_ = v_reuseFailAlloc_445_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
lean_object* v___x_441_; lean_object* v___x_443_; 
v___x_441_ = lean_st_ref_put(v___y_400_, v___x_440_);
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 0, v___x_427_);
v___x_443_ = v___x_406_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_427_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___boxed(lean_object* v_cls_450_, lean_object* v_msg_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg(v_cls_450_, v_msg_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4(lean_object* v_as_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
if (lean_obj_tag(v_as_461_) == 0)
{
lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_470_ = lean_box(0);
v___x_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
return v___x_471_;
}
else
{
lean_object* v_toCold_472_; lean_object* v_options_473_; uint8_t v_hasTrace_474_; 
v_toCold_472_ = lean_ctor_get(v___y_467_, 0);
v_options_473_ = lean_ctor_get(v_toCold_472_, 2);
v_hasTrace_474_ = lean_ctor_get_uint8(v_options_473_, sizeof(void*)*1);
if (v_hasTrace_474_ == 0)
{
lean_object* v_tail_475_; 
v_tail_475_ = lean_ctor_get(v_as_461_, 1);
lean_inc(v_tail_475_);
lean_dec_ref_known(v_as_461_, 2);
v_as_461_ = v_tail_475_;
goto _start;
}
else
{
lean_object* v_head_477_; lean_object* v_tail_478_; lean_object* v_fst_479_; lean_object* v_snd_480_; lean_object* v_inheritedTraceOptions_481_; lean_object* v___x_482_; lean_object* v___x_483_; uint8_t v___x_484_; 
v_head_477_ = lean_ctor_get(v_as_461_, 0);
lean_inc(v_head_477_);
v_tail_478_ = lean_ctor_get(v_as_461_, 1);
lean_inc(v_tail_478_);
lean_dec_ref_known(v_as_461_, 2);
v_fst_479_ = lean_ctor_get(v_head_477_, 0);
lean_inc_n(v_fst_479_, 2);
v_snd_480_ = lean_ctor_get(v_head_477_, 1);
lean_inc(v_snd_480_);
lean_dec(v_head_477_);
v_inheritedTraceOptions_481_ = lean_ctor_get(v_toCold_472_, 11);
v___x_482_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4___closed__1));
v___x_483_ = l_Lean_Name_append(v___x_482_, v_fst_479_);
v___x_484_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_481_, v_options_473_, v___x_483_);
lean_dec(v___x_483_);
if (v___x_484_ == 0)
{
lean_dec(v_snd_480_);
lean_dec(v_fst_479_);
v_as_461_ = v_tail_478_;
goto _start;
}
else
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_486_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_486_, 0, v_snd_480_);
v___x_487_ = l_Lean_MessageData_ofFormat(v___x_486_);
v___x_488_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg(v_fst_479_, v___x_487_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_dec_ref_known(v___x_488_, 1);
v_as_461_ = v_tail_478_;
goto _start;
}
else
{
lean_dec(v_tail_478_);
return v___x_488_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4___boxed(lean_object* v_as_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4(v_as_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
lean_dec(v___y_495_);
lean_dec_ref(v___y_494_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
lean_dec(v___y_491_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__2(lean_object* v_currNamespace_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_503_, 0, v_currNamespace_500_);
lean_ctor_set(v___x_503_, 1, v___y_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__2___boxed(lean_object* v_currNamespace_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__2(v_currNamespace_504_, v___y_505_, v___y_506_);
lean_dec_ref(v___y_505_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___redArg(lean_object* v_x_508_, lean_object* v___y_509_){
_start:
{
if (lean_obj_tag(v_x_508_) == 0)
{
lean_object* v_a_510_; lean_object* v___x_511_; 
v_a_510_ = lean_ctor_get(v_x_508_, 0);
lean_inc(v_a_510_);
v___x_511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_511_, 0, v_a_510_);
lean_ctor_set(v___x_511_, 1, v___y_509_);
return v___x_511_;
}
else
{
lean_object* v_a_512_; lean_object* v___x_513_; 
v_a_512_ = lean_ctor_get(v_x_508_, 0);
lean_inc(v_a_512_);
v___x_513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_513_, 0, v_a_512_);
lean_ctor_set(v___x_513_, 1, v___y_509_);
return v___x_513_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___redArg___boxed(lean_object* v_x_514_, lean_object* v___y_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___redArg(v_x_514_, v___y_515_);
lean_dec_ref(v_x_514_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__1(lean_object* v_env_517_, lean_object* v_stx_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_517_, v_stx_518_, v___y_519_, v___y_520_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_522_; 
v_a_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc(v_a_522_);
if (lean_obj_tag(v_a_522_) == 0)
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_531_; 
v_a_523_ = lean_ctor_get(v___x_521_, 1);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_531_ == 0)
{
lean_object* v_unused_532_; 
v_unused_532_ = lean_ctor_get(v___x_521_, 0);
lean_dec(v_unused_532_);
v___x_525_ = v___x_521_;
v_isShared_526_ = v_isSharedCheck_531_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_521_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_531_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_527_; lean_object* v___x_529_; 
v___x_527_ = lean_box(0);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 0, v___x_527_);
v___x_529_ = v___x_525_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_527_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v_a_523_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
else
{
lean_object* v_val_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_561_; 
v_val_533_ = lean_ctor_get(v_a_522_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v_a_522_);
if (v_isSharedCheck_561_ == 0)
{
v___x_535_ = v_a_522_;
v_isShared_536_ = v_isSharedCheck_561_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_val_533_);
lean_dec(v_a_522_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_561_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v_snd_537_; 
v_snd_537_ = lean_ctor_get(v_val_533_, 1);
lean_inc(v_snd_537_);
lean_dec(v_val_533_);
if (lean_obj_tag(v_snd_537_) == 0)
{
lean_object* v_a_538_; lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_547_; 
lean_del_object(v___x_535_);
v_a_538_ = lean_ctor_get(v___x_521_, 1);
lean_inc(v_a_538_);
lean_dec_ref_known(v___x_521_, 2);
v_a_539_ = lean_ctor_get(v_snd_537_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v_snd_537_);
if (v_isSharedCheck_547_ == 0)
{
v___x_541_ = v_snd_537_;
v_isShared_542_ = v_isSharedCheck_547_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v_snd_537_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_547_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_a_539_);
v___x_544_ = v_reuseFailAlloc_546_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
lean_object* v___x_545_; 
v___x_545_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___redArg(v___x_544_, v_a_538_);
lean_dec_ref(v___x_544_);
return v___x_545_;
}
}
}
else
{
lean_object* v_a_548_; lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_560_; 
v_a_548_ = lean_ctor_get(v___x_521_, 1);
lean_inc(v_a_548_);
lean_dec_ref_known(v___x_521_, 2);
v_a_549_ = lean_ctor_get(v_snd_537_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v_snd_537_);
if (v_isSharedCheck_560_ == 0)
{
v___x_551_ = v_snd_537_;
v_isShared_552_ = v_isSharedCheck_560_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v_snd_537_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_560_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_554_; 
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 0, v_a_549_);
v___x_554_ = v___x_535_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_a_549_);
v___x_554_ = v_reuseFailAlloc_559_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
lean_object* v___x_556_; 
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 0, v___x_554_);
v___x_556_ = v___x_551_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_554_);
v___x_556_ = v_reuseFailAlloc_558_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
lean_object* v___x_557_; 
v___x_557_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___redArg(v___x_556_, v_a_548_);
lean_dec_ref(v___x_556_);
return v___x_557_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_562_; lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_570_; 
v_a_562_ = lean_ctor_get(v___x_521_, 0);
v_a_563_ = lean_ctor_get(v___x_521_, 1);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_570_ == 0)
{
v___x_565_ = v___x_521_;
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_inc(v_a_562_);
lean_dec(v___x_521_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_568_; 
if (v_isShared_566_ == 0)
{
v___x_568_ = v___x_565_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_a_562_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v_a_563_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__1___boxed(lean_object* v_env_571_, lean_object* v_stx_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__1(v_env_571_, v_stx_572_, v___y_573_, v___y_574_);
lean_dec_ref(v___y_573_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___lam__0(lean_object* v___x_576_, lean_object* v_entry_577_, lean_object* v_s_578_){
_start:
{
lean_object* v_addEntryFn_579_; lean_object* v_importedEntries_580_; lean_object* v_state_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_589_; 
v_addEntryFn_579_ = lean_ctor_get(v___x_576_, 3);
lean_inc(v_addEntryFn_579_);
lean_dec_ref(v___x_576_);
v_importedEntries_580_ = lean_ctor_get(v_s_578_, 0);
v_state_581_ = lean_ctor_get(v_s_578_, 1);
v_isSharedCheck_589_ = !lean_is_exclusive(v_s_578_);
if (v_isSharedCheck_589_ == 0)
{
v___x_583_ = v_s_578_;
v_isShared_584_ = v_isSharedCheck_589_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_state_581_);
lean_inc(v_importedEntries_580_);
lean_dec(v_s_578_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_589_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v_state_585_; lean_object* v___x_587_; 
v_state_585_ = lean_apply_2(v_addEntryFn_579_, v_state_581_, v_entry_577_);
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 1, v_state_585_);
v___x_587_ = v___x_583_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_importedEntries_580_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v_state_585_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__14___redArg___closed__0(void){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_590_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__14___redArg___closed__1(void){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__14___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__14___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__14___redArg___closed__0);
v___x_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_592_, 0, v___x_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__14___redArg(){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__14___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__14___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__14___redArg___closed__1);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__14___redArg___boxed(lean_object* v___dummy_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__14___redArg();
return v_res_596_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__8_spec__12_spec__15___redArg(lean_object* v_keys_597_, lean_object* v_i_598_, lean_object* v_k_599_){
_start:
{
lean_object* v___x_600_; uint8_t v___x_601_; 
v___x_600_ = lean_array_get_size(v_keys_597_);
v___x_601_ = lean_nat_dec_lt(v_i_598_, v___x_600_);
if (v___x_601_ == 0)
{
lean_dec(v_i_598_);
return v___x_601_;
}
else
{
lean_object* v_k_x27_602_; uint8_t v___x_603_; 
v_k_x27_602_ = lean_array_fget_borrowed(v_keys_597_, v_i_598_);
v___x_603_ = l_Lean_instBEqExtraModUse_beq(v_k_599_, v_k_x27_602_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = lean_unsigned_to_nat(1u);
v___x_605_ = lean_nat_add(v_i_598_, v___x_604_);
lean_dec(v_i_598_);
v_i_598_ = v___x_605_;
goto _start;
}
else
{
lean_dec(v_i_598_);
return v___x_601_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__8_spec__12_spec__15___redArg___boxed(lean_object* v_keys_607_, lean_object* v_i_608_, lean_object* v_k_609_){
_start:
{
uint8_t v_res_610_; lean_object* v_r_611_; 
v_res_610_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__8_spec__12_spec__15___redArg(v_keys_607_, v_i_608_, v_k_609_);
lean_dec_ref(v_k_609_);
lean_dec_ref(v_keys_607_);
v_r_611_ = lean_box(v_res_610_);
return v_r_611_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__8_spec__12___redArg(lean_object* v_x_612_, size_t v_x_613_, lean_object* v_x_614_){
_start:
{
if (lean_obj_tag(v_x_612_) == 0)
{
lean_object* v_es_615_; lean_object* v___x_616_; size_t v___x_617_; size_t v___x_618_; lean_object* v_j_619_; lean_object* v___x_620_; 
v_es_615_ = lean_ctor_get(v_x_612_, 0);
v___x_616_ = lean_box(2);
v___x_617_ = ((size_t)31ULL);
v___x_618_ = lean_usize_land(v_x_613_, v___x_617_);
v_j_619_ = lean_usize_to_nat(v___x_618_);
v___x_620_ = lean_array_get_borrowed(v___x_616_, v_es_615_, v_j_619_);
lean_dec(v_j_619_);
switch(lean_obj_tag(v___x_620_))
{
case 0:
{
lean_object* v_key_621_; uint8_t v___x_622_; 
v_key_621_ = lean_ctor_get(v___x_620_, 0);
v___x_622_ = l_Lean_instBEqExtraModUse_beq(v_x_614_, v_key_621_);
return v___x_622_;
}
case 1:
{
lean_object* v_node_623_; size_t v___x_624_; size_t v___x_625_; 
v_node_623_ = lean_ctor_get(v___x_620_, 0);
v___x_624_ = ((size_t)5ULL);
v___x_625_ = lean_usize_shift_right(v_x_613_, v___x_624_);
v_x_612_ = v_node_623_;
v_x_613_ = v___x_625_;
goto _start;
}
default: 
{
uint8_t v___x_627_; 
v___x_627_ = 0;
return v___x_627_;
}
}
}
else
{
lean_object* v_ks_628_; lean_object* v___x_629_; uint8_t v___x_630_; 
v_ks_628_ = lean_ctor_get(v_x_612_, 0);
v___x_629_ = lean_unsigned_to_nat(0u);
v___x_630_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__8_spec__12_spec__15___redArg(v_ks_628_, v___x_629_, v_x_614_);
return v___x_630_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__8_spec__12___redArg___boxed(lean_object* v_x_631_, lean_object* v_x_632_, lean_object* v_x_633_){
_start:
{
size_t v_x_28518__boxed_634_; uint8_t v_res_635_; lean_object* v_r_636_; 
v_x_28518__boxed_634_ = lean_unbox_usize(v_x_632_);
lean_dec(v_x_632_);
v_res_635_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__8_spec__12___redArg(v_x_631_, v_x_28518__boxed_634_, v_x_633_);
lean_dec_ref(v_x_633_);
lean_dec_ref(v_x_631_);
v_r_636_ = lean_box(v_res_635_);
return v_r_636_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__8___redArg(lean_object* v_x_637_, lean_object* v_x_638_){
_start:
{
uint64_t v___x_639_; size_t v___x_640_; uint8_t v___x_641_; 
v___x_639_ = l_Lean_instHashableExtraModUse_hash(v_x_638_);
v___x_640_ = lean_uint64_to_usize(v___x_639_);
v___x_641_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__8_spec__12___redArg(v_x_637_, v___x_640_, v_x_638_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_x_642_, lean_object* v_x_643_){
_start:
{
uint8_t v_res_644_; lean_object* v_r_645_; 
v_res_644_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__8___redArg(v_x_642_, v_x_643_);
lean_dec_ref(v_x_643_);
lean_dec_ref(v_x_642_);
v_r_645_ = lean_box(v_res_644_);
return v_r_645_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__0(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__14___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__14___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__14___redArg___closed__0);
v___x_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_647_, 0, v___x_646_);
return v___x_647_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__1(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__0);
v___x_649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
return v___x_649_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__2(void){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__14___redArg();
return v___x_650_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_651_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__0);
v___x_652_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__2);
v___x_653_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_653_, 0, v___x_652_);
lean_ctor_set(v___x_653_, 1, v___x_651_);
lean_ctor_set(v___x_653_, 2, v___x_651_);
lean_ctor_set(v___x_653_, 3, v___x_651_);
lean_ctor_set(v___x_653_, 4, v___x_651_);
lean_ctor_set(v___x_653_, 5, v___x_651_);
lean_ctor_set(v___x_653_, 6, v___x_651_);
return v___x_653_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__4(void){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_654_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__8(void){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__7));
v___x_660_ = l_Lean_stringToMessageData(v___x_659_);
return v___x_660_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__10(void){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_662_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__9));
v___x_663_ = l_Lean_stringToMessageData(v___x_662_);
return v___x_663_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__11(void){
_start:
{
lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_664_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___closed__1));
v___x_665_ = l_Lean_stringToMessageData(v___x_664_);
return v___x_665_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__12(void){
_start:
{
lean_object* v_cls_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v_cls_666_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__6));
v___x_667_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4___closed__1));
v___x_668_ = l_Lean_Name_append(v___x_667_, v_cls_666_);
return v___x_668_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__14(void){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__13));
v___x_671_ = l_Lean_stringToMessageData(v___x_670_);
return v___x_671_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__16(void){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__15));
v___x_674_ = l_Lean_stringToMessageData(v___x_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4(lean_object* v_mod_679_, uint8_t v_isMeta_680_, lean_object* v_hint_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v_env_724_; uint8_t v_isExporting_725_; lean_object* v_entry_726_; lean_object* v___x_727_; lean_object* v_env_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; uint8_t v___x_733_; 
v___x_722_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__4);
v___x_723_ = lean_st_ref_get(v___y_688_);
v_env_724_ = lean_ctor_get(v___x_723_, 0);
lean_inc_ref(v_env_724_);
lean_dec(v___x_723_);
v_isExporting_725_ = lean_ctor_get_uint8(v_env_724_, sizeof(void*)*13);
lean_dec_ref(v_env_724_);
lean_inc(v_mod_679_);
v_entry_726_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_726_, 0, v_mod_679_);
lean_ctor_set_uint8(v_entry_726_, sizeof(void*)*1, v_isExporting_725_);
lean_ctor_set_uint8(v_entry_726_, sizeof(void*)*1 + 1, v_isMeta_680_);
v___x_727_ = lean_st_ref_get(v___y_688_);
v_env_728_ = lean_ctor_get(v___x_727_, 0);
lean_inc_ref(v_env_728_);
lean_dec(v___x_727_);
v___x_729_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_730_ = lean_box(1);
v___x_731_ = lean_box(0);
v___x_732_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_722_, v___x_729_, v_env_728_, v___x_730_, v___x_731_);
v___x_733_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__8___redArg(v___x_732_, v_entry_726_);
lean_dec(v___x_732_);
if (v___x_733_ == 0)
{
lean_object* v_toCold_734_; lean_object* v_options_735_; lean_object* v_inheritedTraceOptions_736_; uint8_t v_hasTrace_737_; lean_object* v___f_738_; uint8_t v___x_739_; lean_object* v___y_741_; lean_object* v___y_742_; 
v_toCold_734_ = lean_ctor_get(v___y_687_, 0);
v_options_735_ = lean_ctor_get(v_toCold_734_, 2);
v_inheritedTraceOptions_736_ = lean_ctor_get(v_toCold_734_, 11);
v_hasTrace_737_ = lean_ctor_get_uint8(v_options_735_, sizeof(void*)*1);
v___f_738_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___lam__0), 3, 2);
lean_closure_set(v___f_738_, 0, v___x_729_);
lean_closure_set(v___f_738_, 1, v_entry_726_);
v___x_739_ = 1;
if (v_hasTrace_737_ == 0)
{
lean_dec(v_hint_681_);
lean_dec(v_mod_679_);
v___y_741_ = v___y_686_;
v___y_742_ = v___y_688_;
goto v___jp_740_;
}
else
{
lean_object* v_cls_769_; lean_object* v___y_771_; lean_object* v___y_772_; lean_object* v___y_776_; lean_object* v___y_777_; lean_object* v___x_789_; uint8_t v___x_790_; 
v_cls_769_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__6));
v___x_789_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__12);
v___x_790_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_736_, v_options_735_, v___x_789_);
if (v___x_790_ == 0)
{
lean_dec(v_hint_681_);
lean_dec(v_mod_679_);
v___y_741_ = v___y_686_;
v___y_742_ = v___y_688_;
goto v___jp_740_;
}
else
{
lean_object* v___x_791_; lean_object* v___y_793_; 
v___x_791_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__14);
if (v_isExporting_725_ == 0)
{
lean_object* v___x_800_; 
v___x_800_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__19));
v___y_793_ = v___x_800_;
goto v___jp_792_;
}
else
{
lean_object* v___x_801_; 
v___x_801_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__20));
v___y_793_ = v___x_801_;
goto v___jp_792_;
}
v___jp_792_:
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
lean_inc_ref(v___y_793_);
v___x_794_ = l_Lean_stringToMessageData(v___y_793_);
v___x_795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_795_, 0, v___x_791_);
lean_ctor_set(v___x_795_, 1, v___x_794_);
v___x_796_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__16);
v___x_797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_797_, 0, v___x_795_);
lean_ctor_set(v___x_797_, 1, v___x_796_);
if (v_isMeta_680_ == 0)
{
lean_object* v___x_798_; 
v___x_798_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__17));
v___y_776_ = v___x_797_;
v___y_777_ = v___x_798_;
goto v___jp_775_;
}
else
{
lean_object* v___x_799_; 
v___x_799_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__18));
v___y_776_ = v___x_797_;
v___y_777_ = v___x_799_;
goto v___jp_775_;
}
}
}
v___jp_770_:
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_773_, 0, v___y_771_);
lean_ctor_set(v___x_773_, 1, v___y_772_);
v___x_774_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg(v_cls_769_, v___x_773_, v___y_685_, v___y_686_, v___y_687_, v___y_688_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_dec_ref_known(v___x_774_, 1);
v___y_741_ = v___y_686_;
v___y_742_ = v___y_688_;
goto v___jp_740_;
}
else
{
lean_dec_ref(v___f_738_);
return v___x_774_;
}
}
v___jp_775_:
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; uint8_t v___x_784_; 
lean_inc_ref(v___y_777_);
v___x_778_ = l_Lean_stringToMessageData(v___y_777_);
v___x_779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_779_, 0, v___y_776_);
lean_ctor_set(v___x_779_, 1, v___x_778_);
v___x_780_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__8);
v___x_781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_781_, 0, v___x_779_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
v___x_782_ = l_Lean_MessageData_ofName(v_mod_679_);
v___x_783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_781_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
v___x_784_ = l_Lean_Name_isAnonymous(v_hint_681_);
if (v___x_784_ == 0)
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_785_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__10);
v___x_786_ = l_Lean_MessageData_ofName(v_hint_681_);
v___x_787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_785_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
v___y_771_ = v___x_783_;
v___y_772_ = v___x_787_;
goto v___jp_770_;
}
else
{
lean_object* v___x_788_; 
lean_dec(v_hint_681_);
v___x_788_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__11);
v___y_771_ = v___x_783_;
v___y_772_ = v___x_788_;
goto v___jp_770_;
}
}
}
v___jp_740_:
{
lean_object* v___x_743_; lean_object* v_toEnvExtension_744_; uint8_t v_logWrites_745_; 
v___x_743_ = lean_st_ref_take(v___y_742_);
v_toEnvExtension_744_ = lean_ctor_get(v___x_729_, 0);
v_logWrites_745_ = lean_ctor_get_uint8(v_toEnvExtension_744_, sizeof(void*)*6);
if (v_logWrites_745_ == 0)
{
lean_object* v_env_746_; lean_object* v_nextMacroScope_747_; lean_object* v_ngen_748_; lean_object* v_auxDeclNGen_749_; lean_object* v_traceState_750_; lean_object* v_recordedDeps_751_; lean_object* v_messages_752_; lean_object* v_infoState_753_; lean_object* v_snapshotTasks_754_; lean_object* v_asyncMode_755_; lean_object* v___x_756_; 
v_env_746_ = lean_ctor_get(v___x_743_, 0);
lean_inc_ref(v_env_746_);
v_nextMacroScope_747_ = lean_ctor_get(v___x_743_, 1);
lean_inc(v_nextMacroScope_747_);
v_ngen_748_ = lean_ctor_get(v___x_743_, 2);
lean_inc_ref(v_ngen_748_);
v_auxDeclNGen_749_ = lean_ctor_get(v___x_743_, 3);
lean_inc_ref(v_auxDeclNGen_749_);
v_traceState_750_ = lean_ctor_get(v___x_743_, 4);
lean_inc_ref(v_traceState_750_);
v_recordedDeps_751_ = lean_ctor_get(v___x_743_, 6);
lean_inc_ref(v_recordedDeps_751_);
v_messages_752_ = lean_ctor_get(v___x_743_, 7);
lean_inc_ref(v_messages_752_);
v_infoState_753_ = lean_ctor_get(v___x_743_, 8);
lean_inc_ref(v_infoState_753_);
v_snapshotTasks_754_ = lean_ctor_get(v___x_743_, 9);
lean_inc_ref(v_snapshotTasks_754_);
lean_dec(v___x_743_);
v_asyncMode_755_ = lean_ctor_get(v_toEnvExtension_744_, 2);
lean_inc_ref(v_toEnvExtension_744_);
v___x_756_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_744_, v_env_746_, v___f_738_, v_asyncMode_755_, v___x_731_, v___x_739_);
v___y_691_ = v_snapshotTasks_754_;
v___y_692_ = v_traceState_750_;
v___y_693_ = v_infoState_753_;
v___y_694_ = v_messages_752_;
v___y_695_ = v_recordedDeps_751_;
v___y_696_ = v_auxDeclNGen_749_;
v___y_697_ = v_nextMacroScope_747_;
v___y_698_ = v___y_742_;
v___y_699_ = v_ngen_748_;
v___y_700_ = v___y_741_;
v___y_701_ = v___x_756_;
goto v___jp_690_;
}
else
{
lean_object* v_env_757_; lean_object* v_nextMacroScope_758_; lean_object* v_ngen_759_; lean_object* v_auxDeclNGen_760_; lean_object* v_traceState_761_; lean_object* v_recordedDeps_762_; lean_object* v_messages_763_; lean_object* v_infoState_764_; lean_object* v_snapshotTasks_765_; lean_object* v_asyncMode_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v_env_757_ = lean_ctor_get(v___x_743_, 0);
lean_inc_ref(v_env_757_);
v_nextMacroScope_758_ = lean_ctor_get(v___x_743_, 1);
lean_inc(v_nextMacroScope_758_);
v_ngen_759_ = lean_ctor_get(v___x_743_, 2);
lean_inc_ref(v_ngen_759_);
v_auxDeclNGen_760_ = lean_ctor_get(v___x_743_, 3);
lean_inc_ref(v_auxDeclNGen_760_);
v_traceState_761_ = lean_ctor_get(v___x_743_, 4);
lean_inc_ref(v_traceState_761_);
v_recordedDeps_762_ = lean_ctor_get(v___x_743_, 6);
lean_inc_ref(v_recordedDeps_762_);
v_messages_763_ = lean_ctor_get(v___x_743_, 7);
lean_inc_ref(v_messages_763_);
v_infoState_764_ = lean_ctor_get(v___x_743_, 8);
lean_inc_ref(v_infoState_764_);
v_snapshotTasks_765_ = lean_ctor_get(v___x_743_, 9);
lean_inc_ref(v_snapshotTasks_765_);
lean_dec(v___x_743_);
v_asyncMode_766_ = lean_ctor_get(v_toEnvExtension_744_, 2);
lean_inc_ref_n(v_toEnvExtension_744_, 2);
v___x_767_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_744_, v_env_757_);
lean_dec_ref(v_env_757_);
v___x_768_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_744_, v___x_767_, v___f_738_, v_asyncMode_766_, v___x_731_, v___x_739_);
v___y_691_ = v_snapshotTasks_765_;
v___y_692_ = v_traceState_761_;
v___y_693_ = v_infoState_764_;
v___y_694_ = v_messages_763_;
v___y_695_ = v_recordedDeps_762_;
v___y_696_ = v_auxDeclNGen_760_;
v___y_697_ = v_nextMacroScope_758_;
v___y_698_ = v___y_742_;
v___y_699_ = v_ngen_759_;
v___y_700_ = v___y_741_;
v___y_701_ = v___x_768_;
goto v___jp_690_;
}
}
}
else
{
lean_object* v___x_802_; lean_object* v___x_803_; 
lean_dec_ref_known(v_entry_726_, 1);
lean_dec(v_hint_681_);
lean_dec(v_mod_679_);
v___x_802_ = lean_box(0);
v___x_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
return v___x_803_;
}
v___jp_690_:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v_mctx_706_; lean_object* v_zetaDeltaFVarIds_707_; lean_object* v_postponed_708_; lean_object* v_diag_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_720_; 
v___x_702_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__1);
v___x_703_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_703_, 0, v___y_701_);
lean_ctor_set(v___x_703_, 1, v___y_697_);
lean_ctor_set(v___x_703_, 2, v___y_699_);
lean_ctor_set(v___x_703_, 3, v___y_696_);
lean_ctor_set(v___x_703_, 4, v___y_692_);
lean_ctor_set(v___x_703_, 5, v___x_702_);
lean_ctor_set(v___x_703_, 6, v___y_695_);
lean_ctor_set(v___x_703_, 7, v___y_694_);
lean_ctor_set(v___x_703_, 8, v___y_693_);
lean_ctor_set(v___x_703_, 9, v___y_691_);
v___x_704_ = lean_st_ref_put(v___y_698_, v___x_703_);
v___x_705_ = lean_st_ref_take(v___y_700_);
v_mctx_706_ = lean_ctor_get(v___x_705_, 0);
v_zetaDeltaFVarIds_707_ = lean_ctor_get(v___x_705_, 2);
v_postponed_708_ = lean_ctor_get(v___x_705_, 3);
v_diag_709_ = lean_ctor_get(v___x_705_, 4);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_720_ == 0)
{
lean_object* v_unused_721_; 
v_unused_721_ = lean_ctor_get(v___x_705_, 1);
lean_dec(v_unused_721_);
v___x_711_ = v___x_705_;
v_isShared_712_ = v_isSharedCheck_720_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_diag_709_);
lean_inc(v_postponed_708_);
lean_inc(v_zetaDeltaFVarIds_707_);
lean_inc(v_mctx_706_);
lean_dec(v___x_705_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_720_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_713_ = lean_box(0);
v___x_714_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__3);
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 1, v___x_714_);
v___x_716_ = v___x_711_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_mctx_706_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v___x_714_);
lean_ctor_set(v_reuseFailAlloc_719_, 2, v_zetaDeltaFVarIds_707_);
lean_ctor_set(v_reuseFailAlloc_719_, 3, v_postponed_708_);
lean_ctor_set(v_reuseFailAlloc_719_, 4, v_diag_709_);
v___x_716_ = v_reuseFailAlloc_719_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_717_ = lean_st_ref_put(v___y_700_, v___x_716_);
v___x_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_718_, 0, v___x_713_);
return v___x_718_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___boxed(lean_object* v_mod_804_, lean_object* v_isMeta_805_, lean_object* v_hint_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
uint8_t v_isMeta_boxed_815_; lean_object* v_res_816_; 
v_isMeta_boxed_815_ = lean_unbox(v_isMeta_805_);
v_res_816_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4(v_mod_804_, v_isMeta_boxed_815_, v_hint_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
lean_dec(v___y_813_);
lean_dec_ref(v___y_812_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
lean_dec(v___y_807_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6_spec__12___redArg(lean_object* v_a_817_, lean_object* v_x_818_){
_start:
{
if (lean_obj_tag(v_x_818_) == 0)
{
lean_object* v___x_819_; 
v___x_819_ = lean_box(0);
return v___x_819_;
}
else
{
lean_object* v_key_820_; lean_object* v_value_821_; lean_object* v_tail_822_; uint8_t v___x_823_; 
v_key_820_ = lean_ctor_get(v_x_818_, 0);
v_value_821_ = lean_ctor_get(v_x_818_, 1);
v_tail_822_ = lean_ctor_get(v_x_818_, 2);
v___x_823_ = lean_name_eq(v_key_820_, v_a_817_);
if (v___x_823_ == 0)
{
v_x_818_ = v_tail_822_;
goto _start;
}
else
{
lean_object* v___x_825_; 
lean_inc(v_value_821_);
v___x_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_825_, 0, v_value_821_);
return v___x_825_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6_spec__12___redArg___boxed(lean_object* v_a_826_, lean_object* v_x_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6_spec__12___redArg(v_a_826_, v_x_827_);
lean_dec(v_x_827_);
lean_dec(v_a_826_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6___redArg(lean_object* v_m_829_, lean_object* v_a_830_){
_start:
{
lean_object* v_buckets_831_; lean_object* v___x_832_; uint64_t v___y_834_; 
v_buckets_831_ = lean_ctor_get(v_m_829_, 1);
v___x_832_ = lean_array_get_size(v_buckets_831_);
if (lean_obj_tag(v_a_830_) == 0)
{
uint64_t v___x_848_; 
v___x_848_ = 1723ULL;
v___y_834_ = v___x_848_;
goto v___jp_833_;
}
else
{
uint64_t v_hash_849_; 
v_hash_849_ = lean_ctor_get_uint64(v_a_830_, sizeof(void*)*2);
v___y_834_ = v_hash_849_;
goto v___jp_833_;
}
v___jp_833_:
{
uint64_t v___x_835_; uint64_t v___x_836_; uint64_t v_fold_837_; uint64_t v___x_838_; uint64_t v___x_839_; uint64_t v___x_840_; size_t v___x_841_; size_t v___x_842_; size_t v___x_843_; size_t v___x_844_; size_t v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_835_ = 32ULL;
v___x_836_ = lean_uint64_shift_right(v___y_834_, v___x_835_);
v_fold_837_ = lean_uint64_xor(v___y_834_, v___x_836_);
v___x_838_ = 16ULL;
v___x_839_ = lean_uint64_shift_right(v_fold_837_, v___x_838_);
v___x_840_ = lean_uint64_xor(v_fold_837_, v___x_839_);
v___x_841_ = lean_uint64_to_usize(v___x_840_);
v___x_842_ = lean_usize_of_nat(v___x_832_);
v___x_843_ = ((size_t)1ULL);
v___x_844_ = lean_usize_sub(v___x_842_, v___x_843_);
v___x_845_ = lean_usize_land(v___x_841_, v___x_844_);
v___x_846_ = lean_array_uget_borrowed(v_buckets_831_, v___x_845_);
v___x_847_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6_spec__12___redArg(v_a_830_, v___x_846_);
return v___x_847_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6___redArg___boxed(lean_object* v_m_850_, lean_object* v_a_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6___redArg(v_m_850_, v_a_851_);
lean_dec(v_a_851_);
lean_dec_ref(v_m_850_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__5(lean_object* v___x_853_, lean_object* v_declName_854_, lean_object* v_as_855_, size_t v_sz_856_, size_t v_i_857_, lean_object* v_b_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
uint8_t v___x_867_; 
v___x_867_ = lean_usize_dec_lt(v_i_857_, v_sz_856_);
if (v___x_867_ == 0)
{
lean_object* v___x_868_; 
lean_dec(v_declName_854_);
v___x_868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_868_, 0, v_b_858_);
return v___x_868_;
}
else
{
lean_object* v___x_869_; lean_object* v_modules_870_; lean_object* v___x_871_; lean_object* v_a_872_; lean_object* v___x_873_; lean_object* v_toImport_874_; lean_object* v_module_875_; lean_object* v___x_876_; uint8_t v___x_877_; lean_object* v___x_878_; 
v___x_869_ = l_Lean_Environment_header(v___x_853_);
v_modules_870_ = lean_ctor_get(v___x_869_, 3);
lean_inc_ref(v_modules_870_);
lean_dec_ref(v___x_869_);
v___x_871_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_872_ = lean_array_uget_borrowed(v_as_855_, v_i_857_);
v___x_873_ = lean_array_get(v___x_871_, v_modules_870_, v_a_872_);
lean_dec_ref(v_modules_870_);
v_toImport_874_ = lean_ctor_get(v___x_873_, 0);
lean_inc_ref(v_toImport_874_);
lean_dec(v___x_873_);
v_module_875_ = lean_ctor_get(v_toImport_874_, 0);
lean_inc(v_module_875_);
lean_dec_ref(v_toImport_874_);
v___x_876_ = lean_box(0);
v___x_877_ = 0;
lean_inc(v_declName_854_);
v___x_878_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4(v_module_875_, v___x_877_, v_declName_854_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
if (lean_obj_tag(v___x_878_) == 0)
{
size_t v___x_879_; size_t v___x_880_; 
lean_dec_ref_known(v___x_878_, 1);
v___x_879_ = ((size_t)1ULL);
v___x_880_ = lean_usize_add(v_i_857_, v___x_879_);
v_i_857_ = v___x_880_;
v_b_858_ = v___x_876_;
goto _start;
}
else
{
lean_dec(v_declName_854_);
return v___x_878_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__5___boxed(lean_object* v___x_882_, lean_object* v_declName_883_, lean_object* v_as_884_, lean_object* v_sz_885_, lean_object* v_i_886_, lean_object* v_b_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
size_t v_sz_boxed_896_; size_t v_i_boxed_897_; lean_object* v_res_898_; 
v_sz_boxed_896_ = lean_unbox_usize(v_sz_885_);
lean_dec(v_sz_885_);
v_i_boxed_897_ = lean_unbox_usize(v_i_886_);
lean_dec(v_i_886_);
v_res_898_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__5(v___x_882_, v_declName_883_, v_as_884_, v_sz_boxed_896_, v_i_boxed_897_, v_b_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
lean_dec(v___y_888_);
lean_dec_ref(v_as_884_);
lean_dec_ref(v___x_882_);
return v_res_898_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = l_Std_HashMap_instInhabited___redArg();
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2(lean_object* v_declName_902_, uint8_t v_isMeta_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v_env_917_; lean_object* v___y_919_; lean_object* v___x_932_; 
v___x_912_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___closed__0);
v___x_913_ = lean_st_ref_get(v___y_910_);
v_env_917_ = lean_ctor_get(v___x_913_, 0);
lean_inc_ref(v_env_917_);
lean_dec(v___x_913_);
v___x_932_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_917_, v_declName_902_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_dec_ref(v_env_917_);
lean_dec(v_declName_902_);
goto v___jp_914_;
}
else
{
lean_object* v_val_933_; lean_object* v___x_934_; lean_object* v_modules_935_; lean_object* v___x_936_; uint8_t v___x_937_; 
v_val_933_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_val_933_);
lean_dec_ref_known(v___x_932_, 1);
v___x_934_ = l_Lean_Environment_header(v_env_917_);
v_modules_935_ = lean_ctor_get(v___x_934_, 3);
lean_inc_ref(v_modules_935_);
lean_dec_ref(v___x_934_);
v___x_936_ = lean_array_get_size(v_modules_935_);
v___x_937_ = lean_nat_dec_lt(v_val_933_, v___x_936_);
if (v___x_937_ == 0)
{
lean_dec_ref(v_modules_935_);
lean_dec(v_val_933_);
lean_dec_ref(v_env_917_);
lean_dec(v_declName_902_);
goto v___jp_914_;
}
else
{
lean_object* v___x_938_; lean_object* v___x_939_; uint8_t v___y_941_; 
v___x_938_ = lean_array_fget(v_modules_935_, v_val_933_);
lean_dec(v_val_933_);
lean_dec_ref(v_modules_935_);
v___x_939_ = lean_st_ref_get(v___y_910_);
if (v_isMeta_903_ == 0)
{
lean_dec(v___x_939_);
v___y_941_ = v_isMeta_903_;
goto v___jp_940_;
}
else
{
lean_object* v_env_952_; uint8_t v___x_953_; 
v_env_952_ = lean_ctor_get(v___x_939_, 0);
lean_inc_ref(v_env_952_);
lean_dec(v___x_939_);
lean_inc(v_declName_902_);
v___x_953_ = l_Lean_isMarkedMeta(v_env_952_, v_declName_902_);
if (v___x_953_ == 0)
{
v___y_941_ = v_isMeta_903_;
goto v___jp_940_;
}
else
{
uint8_t v___x_954_; 
v___x_954_ = 0;
v___y_941_ = v___x_954_;
goto v___jp_940_;
}
}
v___jp_940_:
{
lean_object* v_toImport_942_; lean_object* v_module_943_; lean_object* v___x_944_; 
v_toImport_942_ = lean_ctor_get(v___x_938_, 0);
lean_inc_ref(v_toImport_942_);
lean_dec(v___x_938_);
v_module_943_ = lean_ctor_get(v_toImport_942_, 0);
lean_inc(v_module_943_);
lean_dec_ref(v_toImport_942_);
lean_inc(v_declName_902_);
v___x_944_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4(v_module_943_, v___y_941_, v_declName_902_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
lean_dec_ref_known(v___x_944_, 1);
v___x_945_ = l_Lean_indirectModUseExt;
v___x_946_ = lean_box(1);
v___x_947_ = lean_box(0);
lean_inc_ref(v_env_917_);
v___x_948_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_912_, v___x_945_, v_env_917_, v___x_946_, v___x_947_);
v___x_949_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6___redArg(v___x_948_, v_declName_902_);
lean_dec(v___x_948_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v___x_950_; 
v___x_950_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___closed__1));
v___y_919_ = v___x_950_;
goto v___jp_918_;
}
else
{
lean_object* v_val_951_; 
v_val_951_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_val_951_);
lean_dec_ref_known(v___x_949_, 1);
v___y_919_ = v_val_951_;
goto v___jp_918_;
}
}
else
{
lean_dec_ref(v_env_917_);
lean_dec(v_declName_902_);
return v___x_944_;
}
}
}
}
v___jp_914_:
{
lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_915_ = lean_box(0);
v___x_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
return v___x_916_;
}
v___jp_918_:
{
lean_object* v___x_920_; size_t v_sz_921_; size_t v___x_922_; lean_object* v___x_923_; 
v___x_920_ = lean_box(0);
v_sz_921_ = lean_array_size(v___y_919_);
v___x_922_ = ((size_t)0ULL);
v___x_923_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__5(v_env_917_, v_declName_902_, v___y_919_, v_sz_921_, v___x_922_, v___x_920_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
lean_dec_ref(v___y_919_);
lean_dec_ref(v_env_917_);
if (lean_obj_tag(v___x_923_) == 0)
{
lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_930_; 
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_930_ == 0)
{
lean_object* v_unused_931_; 
v_unused_931_ = lean_ctor_get(v___x_923_, 0);
lean_dec(v_unused_931_);
v___x_925_ = v___x_923_;
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
else
{
lean_dec(v___x_923_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 0, v___x_920_);
v___x_928_ = v___x_925_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_920_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
else
{
return v___x_923_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___boxed(lean_object* v_declName_955_, lean_object* v_isMeta_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
uint8_t v_isMeta_boxed_965_; lean_object* v_res_966_; 
v_isMeta_boxed_965_ = lean_unbox(v_isMeta_956_);
v_res_966_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2(v_declName_955_, v_isMeta_boxed_965_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3___redArg(lean_object* v_as_x27_967_, lean_object* v_b_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
if (lean_obj_tag(v_as_x27_967_) == 0)
{
lean_object* v___x_977_; 
v___x_977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_977_, 0, v_b_968_);
return v___x_977_;
}
else
{
lean_object* v_head_978_; lean_object* v_tail_979_; lean_object* v___x_980_; uint8_t v___x_981_; lean_object* v___x_982_; 
v_head_978_ = lean_ctor_get(v_as_x27_967_, 0);
v_tail_979_ = lean_ctor_get(v_as_x27_967_, 1);
v___x_980_ = lean_box(0);
v___x_981_ = 1;
lean_inc(v_head_978_);
v___x_982_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2(v_head_978_, v___x_981_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_dec_ref_known(v___x_982_, 1);
v_as_x27_967_ = v_tail_979_;
v_b_968_ = v___x_980_;
goto _start;
}
else
{
return v___x_982_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3___redArg___boxed(lean_object* v_as_x27_984_, lean_object* v_b_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3___redArg(v_as_x27_984_, v_b_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec(v___y_986_);
lean_dec(v_as_x27_984_);
return v_res_994_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = l_Lean_maxRecDepthErrorMessage;
v___x_1001_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
return v___x_1001_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__4(void){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__3);
v___x_1003_ = l_Lean_MessageData_ofFormat(v___x_1002_);
return v___x_1003_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1004_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__4);
v___x_1005_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__2));
v___x_1006_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
lean_ctor_set(v___x_1006_, 1, v___x_1004_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg(lean_object* v_ref_1007_){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1009_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__5);
v___x_1010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1010_, 0, v_ref_1007_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
v___x_1011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___boxed(lean_object* v_ref_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg(v_ref_1012_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__0(lean_object* v_env_1015_, lean_object* v_declName_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
uint8_t v___x_1019_; lean_object* v_env_1020_; lean_object* v___x_1021_; uint8_t v___x_1022_; uint8_t v___x_1023_; 
v___x_1019_ = 0;
v_env_1020_ = l_Lean_Environment_setExporting(v_env_1015_, v___x_1019_);
lean_inc(v_declName_1016_);
v___x_1021_ = l_Lean_mkPrivateName(v_env_1020_, v_declName_1016_);
v___x_1022_ = 1;
lean_inc_ref(v_env_1020_);
v___x_1023_ = l_Lean_Environment_contains(v_env_1020_, v___x_1021_, v___x_1022_);
if (v___x_1023_ == 0)
{
lean_object* v___x_1024_; uint8_t v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1024_ = l_Lean_privateToUserName(v_declName_1016_);
v___x_1025_ = l_Lean_Environment_contains(v_env_1020_, v___x_1024_, v___x_1022_);
v___x_1026_ = lean_box(v___x_1025_);
v___x_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
lean_ctor_set(v___x_1027_, 1, v___y_1018_);
return v___x_1027_;
}
else
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
lean_dec_ref(v_env_1020_);
lean_dec(v_declName_1016_);
v___x_1028_ = lean_box(v___x_1023_);
v___x_1029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
lean_ctor_set(v___x_1029_, 1, v___y_1018_);
return v___x_1029_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__0___boxed(lean_object* v_env_1030_, lean_object* v_declName_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__0(v_env_1030_, v_declName_1031_, v___y_1032_, v___y_1033_);
lean_dec_ref(v___y_1032_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__4(lean_object* v_env_1035_, lean_object* v_currNamespace_1036_, lean_object* v_openDecls_1037_, lean_object* v_n_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = l_Lean_ResolveName_resolveNamespace(v_env_1035_, v_currNamespace_1036_, v_openDecls_1037_, v_n_1038_);
v___x_1042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
lean_ctor_set(v___x_1042_, 1, v___y_1040_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__4___boxed(lean_object* v_env_1043_, lean_object* v_currNamespace_1044_, lean_object* v_openDecls_1045_, lean_object* v_n_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__4(v_env_1043_, v_currNamespace_1044_, v_openDecls_1045_, v_n_1046_, v___y_1047_, v___y_1048_);
lean_dec_ref(v___y_1047_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1_spec__8___redArg(lean_object* v_msg_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v_ref_1056_; lean_object* v___x_1057_; lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1066_; 
v_ref_1056_ = lean_ctor_get(v___y_1053_, 2);
v___x_1057_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0_spec__1(v_msg_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
v_a_1058_ = lean_ctor_get(v___x_1057_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1060_ = v___x_1057_;
v_isShared_1061_ = v_isSharedCheck_1066_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_1057_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1066_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1062_; lean_object* v___x_1064_; 
lean_inc(v_ref_1056_);
v___x_1062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1062_, 0, v_ref_1056_);
lean_ctor_set(v___x_1062_, 1, v_a_1058_);
if (v_isShared_1061_ == 0)
{
lean_ctor_set_tag(v___x_1060_, 1);
lean_ctor_set(v___x_1060_, 0, v___x_1062_);
v___x_1064_ = v___x_1060_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1062_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1_spec__8___redArg___boxed(lean_object* v_msg_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1_spec__8___redArg(v_msg_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1___redArg(lean_object* v_ref_1074_, lean_object* v_msg_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
lean_object* v_toCold_1084_; lean_object* v_currRecDepth_1085_; lean_object* v_ref_1086_; uint16_t v_optionFlags_1087_; uint8_t v_suppressElabErrors_1088_; uint8_t v_checkDeprecated_1089_; uint8_t v_isRecordingDeps_1090_; lean_object* v_ref_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v_toCold_1084_ = lean_ctor_get(v___y_1081_, 0);
v_currRecDepth_1085_ = lean_ctor_get(v___y_1081_, 1);
v_ref_1086_ = lean_ctor_get(v___y_1081_, 2);
v_optionFlags_1087_ = lean_ctor_get_uint16(v___y_1081_, sizeof(void*)*3);
v_suppressElabErrors_1088_ = lean_ctor_get_uint8(v___y_1081_, sizeof(void*)*3 + 2);
v_checkDeprecated_1089_ = lean_ctor_get_uint8(v___y_1081_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1090_ = lean_ctor_get_uint8(v___y_1081_, sizeof(void*)*3 + 4);
v_ref_1091_ = l_Lean_replaceRef(v_ref_1074_, v_ref_1086_);
lean_inc(v_currRecDepth_1085_);
lean_inc_ref(v_toCold_1084_);
v___x_1092_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1092_, 0, v_toCold_1084_);
lean_ctor_set(v___x_1092_, 1, v_currRecDepth_1085_);
lean_ctor_set(v___x_1092_, 2, v_ref_1091_);
lean_ctor_set_uint16(v___x_1092_, sizeof(void*)*3, v_optionFlags_1087_);
lean_ctor_set_uint8(v___x_1092_, sizeof(void*)*3 + 2, v_suppressElabErrors_1088_);
lean_ctor_set_uint8(v___x_1092_, sizeof(void*)*3 + 3, v_checkDeprecated_1089_);
lean_ctor_set_uint8(v___x_1092_, sizeof(void*)*3 + 4, v_isRecordingDeps_1090_);
v___x_1093_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1_spec__8___redArg(v_msg_1075_, v___y_1079_, v___y_1080_, v___x_1092_, v___y_1082_);
lean_dec_ref_known(v___x_1092_, 3);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1___redArg___boxed(lean_object* v_ref_1094_, lean_object* v_msg_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1___redArg(v_ref_1094_, v_msg_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec(v___y_1096_);
lean_dec(v_ref_1094_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg(lean_object* v_x_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v___x_1115_; lean_object* v_toCold_1116_; lean_object* v_env_1117_; lean_object* v_currRecDepth_1118_; lean_object* v_ref_1119_; lean_object* v_maxRecDepth_1120_; lean_object* v_currNamespace_1121_; lean_object* v_openDecls_1122_; lean_object* v_quotContext_1123_; lean_object* v_currMacroScope_1124_; lean_object* v___f_1125_; lean_object* v___f_1126_; lean_object* v___x_1127_; lean_object* v___f_1128_; lean_object* v___f_1129_; lean_object* v___f_1130_; lean_object* v_methods_1131_; lean_object* v___x_1132_; lean_object* v_nextMacroScope_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1115_ = lean_st_ref_get(v___y_1113_);
v_toCold_1116_ = lean_ctor_get(v___y_1112_, 0);
v_env_1117_ = lean_ctor_get(v___x_1115_, 0);
lean_inc_ref_n(v_env_1117_, 4);
lean_dec(v___x_1115_);
v_currRecDepth_1118_ = lean_ctor_get(v___y_1112_, 1);
v_ref_1119_ = lean_ctor_get(v___y_1112_, 2);
v_maxRecDepth_1120_ = lean_ctor_get(v_toCold_1116_, 3);
v_currNamespace_1121_ = lean_ctor_get(v_toCold_1116_, 4);
v_openDecls_1122_ = lean_ctor_get(v_toCold_1116_, 5);
v_quotContext_1123_ = lean_ctor_get(v_toCold_1116_, 8);
v_currMacroScope_1124_ = lean_ctor_get(v_toCold_1116_, 9);
v___f_1125_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1125_, 0, v_env_1117_);
v___f_1126_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1126_, 0, v_env_1117_);
v___x_1127_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1112_);
lean_inc_n(v_currNamespace_1121_, 3);
v___f_1128_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_1128_, 0, v_currNamespace_1121_);
lean_inc_n(v_openDecls_1122_, 2);
v___f_1129_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__3___boxed), 7, 4);
lean_closure_set(v___f_1129_, 0, v_env_1117_);
lean_closure_set(v___f_1129_, 1, v___x_1127_);
lean_closure_set(v___f_1129_, 2, v_currNamespace_1121_);
lean_closure_set(v___f_1129_, 3, v_openDecls_1122_);
v___f_1130_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_1130_, 0, v_env_1117_);
lean_closure_set(v___f_1130_, 1, v_currNamespace_1121_);
lean_closure_set(v___f_1130_, 2, v_openDecls_1122_);
v_methods_1131_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1131_, 0, v___f_1126_);
lean_ctor_set(v_methods_1131_, 1, v___f_1128_);
lean_ctor_set(v_methods_1131_, 2, v___f_1125_);
lean_ctor_set(v_methods_1131_, 3, v___f_1130_);
lean_ctor_set(v_methods_1131_, 4, v___f_1129_);
v___x_1132_ = lean_st_ref_get(v___y_1113_);
v_nextMacroScope_1133_ = lean_ctor_get(v___x_1132_, 1);
lean_inc(v_nextMacroScope_1133_);
lean_dec(v___x_1132_);
lean_inc(v_ref_1119_);
lean_inc(v_maxRecDepth_1120_);
lean_inc(v_currRecDepth_1118_);
lean_inc(v_currMacroScope_1124_);
lean_inc(v_quotContext_1123_);
v___x_1134_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1134_, 0, v_methods_1131_);
lean_ctor_set(v___x_1134_, 1, v_quotContext_1123_);
lean_ctor_set(v___x_1134_, 2, v_currMacroScope_1124_);
lean_ctor_set(v___x_1134_, 3, v_currRecDepth_1118_);
lean_ctor_set(v___x_1134_, 4, v_maxRecDepth_1120_);
lean_ctor_set(v___x_1134_, 5, v_ref_1119_);
v___x_1135_ = lean_box(0);
v___x_1136_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1136_, 0, v_nextMacroScope_1133_);
lean_ctor_set(v___x_1136_, 1, v___x_1135_);
lean_ctor_set(v___x_1136_, 2, v___x_1135_);
v___x_1137_ = lean_apply_2(v_x_1106_, v___x_1134_, v___x_1136_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v_a_1138_; lean_object* v_a_1139_; lean_object* v_macroScope_1140_; lean_object* v_traceMsgs_1141_; lean_object* v_expandedMacroDecls_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v_a_1138_ = lean_ctor_get(v___x_1137_, 1);
lean_inc(v_a_1138_);
v_a_1139_ = lean_ctor_get(v___x_1137_, 0);
lean_inc(v_a_1139_);
lean_dec_ref_known(v___x_1137_, 2);
v_macroScope_1140_ = lean_ctor_get(v_a_1138_, 0);
lean_inc(v_macroScope_1140_);
v_traceMsgs_1141_ = lean_ctor_get(v_a_1138_, 1);
lean_inc(v_traceMsgs_1141_);
v_expandedMacroDecls_1142_ = lean_ctor_get(v_a_1138_, 2);
lean_inc(v_expandedMacroDecls_1142_);
lean_dec(v_a_1138_);
v___x_1143_ = lean_box(0);
v___x_1144_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3___redArg(v_expandedMacroDecls_1142_, v___x_1143_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
lean_dec(v_expandedMacroDecls_1142_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v___x_1145_; lean_object* v_env_1146_; lean_object* v_ngen_1147_; lean_object* v_auxDeclNGen_1148_; lean_object* v_traceState_1149_; lean_object* v_cache_1150_; lean_object* v_recordedDeps_1151_; lean_object* v_messages_1152_; lean_object* v_infoState_1153_; lean_object* v_snapshotTasks_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1180_; 
lean_dec_ref_known(v___x_1144_, 1);
v___x_1145_ = lean_st_ref_take(v___y_1113_);
v_env_1146_ = lean_ctor_get(v___x_1145_, 0);
v_ngen_1147_ = lean_ctor_get(v___x_1145_, 2);
v_auxDeclNGen_1148_ = lean_ctor_get(v___x_1145_, 3);
v_traceState_1149_ = lean_ctor_get(v___x_1145_, 4);
v_cache_1150_ = lean_ctor_get(v___x_1145_, 5);
v_recordedDeps_1151_ = lean_ctor_get(v___x_1145_, 6);
v_messages_1152_ = lean_ctor_get(v___x_1145_, 7);
v_infoState_1153_ = lean_ctor_get(v___x_1145_, 8);
v_snapshotTasks_1154_ = lean_ctor_get(v___x_1145_, 9);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1180_ == 0)
{
lean_object* v_unused_1181_; 
v_unused_1181_ = lean_ctor_get(v___x_1145_, 1);
lean_dec(v_unused_1181_);
v___x_1156_ = v___x_1145_;
v_isShared_1157_ = v_isSharedCheck_1180_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_snapshotTasks_1154_);
lean_inc(v_infoState_1153_);
lean_inc(v_messages_1152_);
lean_inc(v_recordedDeps_1151_);
lean_inc(v_cache_1150_);
lean_inc(v_traceState_1149_);
lean_inc(v_auxDeclNGen_1148_);
lean_inc(v_ngen_1147_);
lean_inc(v_env_1146_);
lean_dec(v___x_1145_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1180_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1159_; 
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 1, v_macroScope_1140_);
v___x_1159_ = v___x_1156_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_env_1146_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v_macroScope_1140_);
lean_ctor_set(v_reuseFailAlloc_1179_, 2, v_ngen_1147_);
lean_ctor_set(v_reuseFailAlloc_1179_, 3, v_auxDeclNGen_1148_);
lean_ctor_set(v_reuseFailAlloc_1179_, 4, v_traceState_1149_);
lean_ctor_set(v_reuseFailAlloc_1179_, 5, v_cache_1150_);
lean_ctor_set(v_reuseFailAlloc_1179_, 6, v_recordedDeps_1151_);
lean_ctor_set(v_reuseFailAlloc_1179_, 7, v_messages_1152_);
lean_ctor_set(v_reuseFailAlloc_1179_, 8, v_infoState_1153_);
lean_ctor_set(v_reuseFailAlloc_1179_, 9, v_snapshotTasks_1154_);
v___x_1159_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1160_ = lean_st_ref_put(v___y_1113_, v___x_1159_);
v___x_1161_ = l_List_reverse___redArg(v_traceMsgs_1141_);
v___x_1162_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4(v___x_1161_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1169_; 
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1169_ == 0)
{
lean_object* v_unused_1170_; 
v_unused_1170_ = lean_ctor_get(v___x_1162_, 0);
lean_dec(v_unused_1170_);
v___x_1164_ = v___x_1162_;
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
else
{
lean_dec(v___x_1162_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1167_; 
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 0, v_a_1139_);
v___x_1167_ = v___x_1164_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_a_1139_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
else
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1178_; 
lean_dec(v_a_1139_);
v_a_1171_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1173_ = v___x_1162_;
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1162_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1176_; 
if (v_isShared_1174_ == 0)
{
v___x_1176_ = v___x_1173_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_a_1171_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
}
}
}
else
{
lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1189_; 
lean_dec(v_traceMsgs_1141_);
lean_dec(v_macroScope_1140_);
lean_dec(v_a_1139_);
v_a_1182_ = lean_ctor_get(v___x_1144_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1184_ = v___x_1144_;
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_dec(v___x_1144_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1187_; 
if (v_isShared_1185_ == 0)
{
v___x_1187_ = v___x_1184_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_a_1182_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
}
else
{
lean_object* v_a_1190_; 
v_a_1190_ = lean_ctor_get(v___x_1137_, 0);
lean_inc(v_a_1190_);
lean_dec_ref_known(v___x_1137_, 2);
if (lean_obj_tag(v_a_1190_) == 0)
{
lean_object* v_a_1191_; lean_object* v_a_1192_; lean_object* v___x_1193_; uint8_t v___x_1194_; 
v_a_1191_ = lean_ctor_get(v_a_1190_, 0);
lean_inc(v_a_1191_);
v_a_1192_ = lean_ctor_get(v_a_1190_, 1);
lean_inc_ref(v_a_1192_);
lean_dec_ref_known(v_a_1190_, 2);
v___x_1193_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___closed__0));
v___x_1194_ = lean_string_dec_eq(v_a_1192_, v___x_1193_);
if (v___x_1194_ == 0)
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1195_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1195_, 0, v_a_1192_);
v___x_1196_ = l_Lean_MessageData_ofFormat(v___x_1195_);
v___x_1197_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1___redArg(v_a_1191_, v___x_1196_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
lean_dec(v_a_1191_);
return v___x_1197_;
}
else
{
lean_object* v___x_1198_; 
lean_dec_ref(v_a_1192_);
v___x_1198_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg(v_a_1191_);
return v___x_1198_;
}
}
else
{
lean_object* v___x_1199_; 
v___x_1199_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
return v___x_1199_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___boxed(lean_object* v_x_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg(v_x_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
lean_dec(v___y_1201_);
return v_res_1209_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheck___closed__1(void){
_start:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheck___closed__0));
v___x_1212_ = l_Lean_stringToMessageData(v___x_1211_);
return v___x_1212_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheck___closed__3(void){
_start:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1214_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheck___closed__2));
v___x_1215_ = l_Lean_stringToMessageData(v___x_1214_);
return v___x_1215_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheck___closed__5(void){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1217_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheck___closed__4));
v___x_1218_ = l_Lean_stringToMessageData(v___x_1217_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheck(lean_object* v_stx_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_){
_start:
{
lean_object* v___y_1229_; lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; lean_object* v___x_1276_; 
lean_inc(v_stx_1219_);
v___x_1276_ = l_Lean_Elab_checkDeprecatedQuotedSyntax(v_stx_1219_, v_a_1225_, v_a_1226_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v___x_1277_; lean_object* v_env_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
lean_dec_ref_known(v___x_1276_, 1);
v___x_1277_ = lean_st_ref_get(v_a_1226_);
v_env_1278_ = lean_ctor_get(v___x_1277_, 0);
lean_inc_ref(v_env_1278_);
lean_dec(v___x_1277_);
v___x_1279_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
lean_inc(v_stx_1219_);
v___x_1280_ = l_Lean_Syntax_getKind(v_stx_1219_);
v___x_1281_ = l_Lean_KeyedDeclsAttribute_getValues___redArg(v___x_1279_, v_env_1278_, v___x_1280_);
lean_dec(v___x_1280_);
if (lean_obj_tag(v___x_1281_) == 1)
{
lean_object* v_head_1282_; lean_object* v_toCold_1283_; lean_object* v_currRecDepth_1284_; lean_object* v_ref_1285_; uint16_t v_optionFlags_1286_; uint8_t v_suppressElabErrors_1287_; uint8_t v_checkDeprecated_1288_; uint8_t v_isRecordingDeps_1289_; lean_object* v___x_1290_; lean_object* v_ref_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
v_head_1282_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_head_1282_);
lean_dec_ref_known(v___x_1281_, 2);
v_toCold_1283_ = lean_ctor_get(v_a_1225_, 0);
v_currRecDepth_1284_ = lean_ctor_get(v_a_1225_, 1);
v_ref_1285_ = lean_ctor_get(v_a_1225_, 2);
v_optionFlags_1286_ = lean_ctor_get_uint16(v_a_1225_, sizeof(void*)*3);
v_suppressElabErrors_1287_ = lean_ctor_get_uint8(v_a_1225_, sizeof(void*)*3 + 2);
v_checkDeprecated_1288_ = lean_ctor_get_uint8(v_a_1225_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1289_ = lean_ctor_get_uint8(v_a_1225_, sizeof(void*)*3 + 4);
v___x_1290_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v_ref_1291_ = l_Lean_replaceRef(v_stx_1219_, v_ref_1285_);
lean_inc(v_currRecDepth_1284_);
lean_inc_ref(v_toCold_1283_);
v___x_1292_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1292_, 0, v_toCold_1283_);
lean_ctor_set(v___x_1292_, 1, v_currRecDepth_1284_);
lean_ctor_set(v___x_1292_, 2, v_ref_1291_);
lean_ctor_set_uint16(v___x_1292_, sizeof(void*)*3, v_optionFlags_1286_);
lean_ctor_set_uint8(v___x_1292_, sizeof(void*)*3 + 2, v_suppressElabErrors_1287_);
lean_ctor_set_uint8(v___x_1292_, sizeof(void*)*3 + 3, v_checkDeprecated_1288_);
lean_ctor_set_uint8(v___x_1292_, sizeof(void*)*3 + 4, v_isRecordingDeps_1289_);
lean_inc(v_a_1226_);
lean_inc(v_a_1224_);
lean_inc_ref(v_a_1223_);
lean_inc(v_a_1222_);
lean_inc_ref(v_a_1221_);
lean_inc(v_a_1220_);
lean_inc(v_stx_1219_);
v___x_1293_ = lean_apply_9(v_head_1282_, v_stx_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v___x_1292_, v_a_1226_, lean_box(0));
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1301_; 
lean_dec(v_stx_1219_);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1301_ == 0)
{
lean_object* v_unused_1302_; 
v_unused_1302_ = lean_ctor_get(v___x_1293_, 0);
lean_dec(v_unused_1302_);
v___x_1295_ = v___x_1293_;
v_isShared_1296_ = v_isSharedCheck_1301_;
goto v_resetjp_1294_;
}
else
{
lean_dec(v___x_1293_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1301_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1297_; lean_object* v___x_1299_; 
v___x_1297_ = lean_box(0);
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 0, v___x_1297_);
v___x_1299_ = v___x_1295_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v___x_1297_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
else
{
lean_object* v_a_1303_; uint8_t v___x_1304_; 
v_a_1303_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_a_1303_);
v___x_1304_ = l_Lean_Exception_isInterrupt(v_a_1303_);
if (v___x_1304_ == 0)
{
uint8_t v___x_1305_; 
lean_inc(v_a_1303_);
v___x_1305_ = l_Lean_Exception_isRuntime(v_a_1303_);
if (v___x_1305_ == 0)
{
if (lean_obj_tag(v_a_1303_) == 0)
{
lean_dec_ref_known(v_a_1303_, 2);
lean_dec(v_stx_1219_);
return v___x_1293_;
}
else
{
lean_object* v_id_1306_; uint8_t v___x_1307_; 
v_id_1306_ = lean_ctor_get(v_a_1303_, 0);
lean_inc(v_id_1306_);
lean_dec_ref_known(v_a_1303_, 2);
v___x_1307_ = l_Lean_instBEqInternalExceptionId_beq(v___x_1290_, v_id_1306_);
lean_dec(v_id_1306_);
if (v___x_1307_ == 0)
{
lean_dec(v_stx_1219_);
return v___x_1293_;
}
else
{
lean_dec_ref_known(v___x_1293_, 1);
v___y_1229_ = v_a_1220_;
v___y_1230_ = v_a_1221_;
v___y_1231_ = v_a_1222_;
v___y_1232_ = v_a_1223_;
v___y_1233_ = v_a_1224_;
v___y_1234_ = v_a_1225_;
v___y_1235_ = v_a_1226_;
goto v___jp_1228_;
}
}
}
else
{
lean_dec(v_a_1303_);
lean_dec(v_stx_1219_);
return v___x_1293_;
}
}
else
{
lean_dec(v_a_1303_);
lean_dec(v_stx_1219_);
return v___x_1293_;
}
}
}
else
{
lean_dec(v___x_1281_);
v___y_1229_ = v_a_1220_;
v___y_1230_ = v_a_1221_;
v___y_1231_ = v_a_1222_;
v___y_1232_ = v_a_1223_;
v___y_1233_ = v_a_1224_;
v___y_1234_ = v_a_1225_;
v___y_1235_ = v_a_1226_;
goto v___jp_1228_;
}
}
else
{
lean_dec(v_stx_1219_);
return v___x_1276_;
}
v___jp_1228_:
{
uint8_t v___x_1236_; 
lean_inc(v_stx_1219_);
v___x_1236_ = l_Lean_Syntax_isAnyAntiquot(v_stx_1219_);
if (v___x_1236_ == 0)
{
uint8_t v___x_1237_; 
lean_inc(v_stx_1219_);
v___x_1237_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent(v_stx_1219_);
if (v___x_1237_ == 0)
{
lean_object* v___x_1238_; lean_object* v___x_1239_; 
lean_dec(v_stx_1219_);
v___x_1238_ = lean_box(0);
v___x_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1238_);
return v___x_1239_;
}
else
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
lean_inc(v_stx_1219_);
v___x_1240_ = lean_alloc_closure((void*)(l_Lean_Macro_expandMacro_x3f___boxed), 3, 1);
lean_closure_set(v___x_1240_, 0, v_stx_1219_);
v___x_1241_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg(v___x_1240_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1242_; 
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_a_1242_);
lean_dec_ref_known(v___x_1241_, 1);
if (lean_obj_tag(v_a_1242_) == 1)
{
lean_object* v_val_1243_; lean_object* v___x_1244_; 
lean_dec(v_stx_1219_);
v_val_1243_ = lean_ctor_get(v_a_1242_, 0);
lean_inc(v_val_1243_);
lean_dec_ref_known(v_a_1242_, 1);
v___x_1244_ = l_Lean_Elab_Term_Quotation_precheck(v_val_1243_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1252_; 
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1252_ == 0)
{
lean_object* v_unused_1253_; 
v_unused_1253_ = lean_ctor_get(v___x_1244_, 0);
lean_dec(v_unused_1253_);
v___x_1246_ = v___x_1244_;
v_isShared_1247_ = v_isSharedCheck_1252_;
goto v_resetjp_1245_;
}
else
{
lean_dec(v___x_1244_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1252_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1248_; lean_object* v___x_1250_; 
v___x_1248_ = lean_box(0);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 0, v___x_1248_);
v___x_1250_ = v___x_1246_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v___x_1248_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
else
{
return v___x_1244_;
}
}
else
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
lean_dec(v_a_1242_);
v___x_1254_ = lean_obj_once(&l_Lean_Elab_Term_Quotation_precheck___closed__1, &l_Lean_Elab_Term_Quotation_precheck___closed__1_once, _init_l_Lean_Elab_Term_Quotation_precheck___closed__1);
lean_inc_n(v_stx_1219_, 2);
v___x_1255_ = l_Lean_Syntax_getKind(v_stx_1219_);
v___x_1256_ = l_Lean_MessageData_ofName(v___x_1255_);
v___x_1257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1254_);
lean_ctor_set(v___x_1257_, 1, v___x_1256_);
v___x_1258_ = lean_obj_once(&l_Lean_Elab_Term_Quotation_precheck___closed__3, &l_Lean_Elab_Term_Quotation_precheck___closed__3_once, _init_l_Lean_Elab_Term_Quotation_precheck___closed__3);
v___x_1259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1257_);
lean_ctor_set(v___x_1259_, 1, v___x_1258_);
v___x_1260_ = l_Lean_MessageData_ofSyntax(v_stx_1219_);
v___x_1261_ = l_Lean_indentD(v___x_1260_);
v___x_1262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1259_);
lean_ctor_set(v___x_1262_, 1, v___x_1261_);
v___x_1263_ = lean_obj_once(&l_Lean_Elab_Term_Quotation_precheck___closed__5, &l_Lean_Elab_Term_Quotation_precheck___closed__5_once, _init_l_Lean_Elab_Term_Quotation_precheck___closed__5);
v___x_1264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1262_);
lean_ctor_set(v___x_1264_, 1, v___x_1263_);
v___x_1265_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1___redArg(v_stx_1219_, v___x_1264_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
lean_dec(v_stx_1219_);
return v___x_1265_;
}
}
else
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_dec(v_stx_1219_);
v_a_1266_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1241_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1241_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
}
else
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
lean_dec(v_stx_1219_);
v___x_1274_ = lean_box(0);
v___x_1275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1274_);
return v___x_1275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheck___boxed(lean_object* v_stx_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_Lean_Elab_Term_Quotation_precheck(v_stx_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_);
lean_dec(v_a_1315_);
lean_dec_ref(v_a_1314_);
lean_dec(v_a_1313_);
lean_dec_ref(v_a_1312_);
lean_dec(v_a_1311_);
lean_dec_ref(v_a_1310_);
lean_dec(v_a_1309_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1(lean_object* v_00_u03b1_1318_, lean_object* v_x_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_){
_start:
{
lean_object* v___x_1322_; 
v___x_1322_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___redArg(v_x_1319_, v___y_1321_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1323_, lean_object* v_x_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1(v_00_u03b1_1323_, v_x_1324_, v___y_1325_, v___y_1326_);
lean_dec_ref(v___y_1325_);
lean_dec_ref(v_x_1324_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5(lean_object* v_00_u03b1_1328_, lean_object* v_ref_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
lean_object* v___x_1338_; 
v___x_1338_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg(v_ref_1329_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1339_, lean_object* v_ref_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5(v_00_u03b1_1339_, v_ref_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec(v___y_1341_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6(lean_object* v_00_u03b1_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v___x_1359_; 
v___x_1359_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___boxed(lean_object* v_00_u03b1_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6(v_00_u03b1_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
lean_dec(v___y_1367_);
lean_dec_ref(v___y_1366_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
lean_dec(v___y_1361_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0(lean_object* v_00_u03b1_1370_, lean_object* v_x_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v___x_1380_; 
v___x_1380_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg(v_x_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___boxed(lean_object* v_00_u03b1_1381_, lean_object* v_x_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0(v_00_u03b1_1381_, v_x_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec(v___y_1383_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1(lean_object* v_00_u03b1_1392_, lean_object* v_ref_1393_, lean_object* v_msg_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v___x_1403_; 
v___x_1403_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1___redArg(v_ref_1393_, v_msg_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1___boxed(lean_object* v_00_u03b1_1404_, lean_object* v_ref_1405_, lean_object* v_msg_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1(v_00_u03b1_1404_, v_ref_1405_, v_msg_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
lean_dec(v___y_1407_);
lean_dec(v_ref_1405_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0(lean_object* v_cls_1416_, lean_object* v_msg_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v___x_1426_; 
v___x_1426_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg(v_cls_1416_, v_msg_1417_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___boxed(lean_object* v_cls_1427_, lean_object* v_msg_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0(v_cls_1427_, v_msg_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
lean_dec(v___y_1429_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3(lean_object* v_as_1438_, lean_object* v_as_x27_1439_, lean_object* v_b_1440_, lean_object* v_a_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3___redArg(v_as_x27_1439_, v_b_1440_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3___boxed(lean_object* v_as_1451_, lean_object* v_as_x27_1452_, lean_object* v_b_1453_, lean_object* v_a_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_){
_start:
{
lean_object* v_res_1463_; 
v_res_1463_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3(v_as_1451_, v_as_x27_1452_, v_b_1453_, v_a_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v___y_1455_);
lean_dec(v_as_x27_1452_);
lean_dec(v_as_1451_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1_spec__8(lean_object* v_00_u03b1_1464_, lean_object* v_msg_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
lean_object* v___x_1474_; 
v___x_1474_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1_spec__8___redArg(v_msg_1465_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1_spec__8___boxed(lean_object* v_00_u03b1_1475_, lean_object* v_msg_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_){
_start:
{
lean_object* v_res_1485_; 
v_res_1485_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1_spec__8(v_00_u03b1_1475_, v_msg_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_);
lean_dec(v___y_1483_);
lean_dec_ref(v___y_1482_);
lean_dec(v___y_1481_);
lean_dec_ref(v___y_1480_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v___y_1477_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_1486_, lean_object* v_m_1487_, lean_object* v_a_1488_){
_start:
{
lean_object* v___x_1489_; 
v___x_1489_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6___redArg(v_m_1487_, v_a_1488_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6___boxed(lean_object* v_00_u03b2_1490_, lean_object* v_m_1491_, lean_object* v_a_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6(v_00_u03b2_1490_, v_m_1491_, v_a_1492_);
lean_dec(v_a_1492_);
lean_dec_ref(v_m_1491_);
return v_res_1493_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_1494_, lean_object* v_x_1495_, lean_object* v_x_1496_){
_start:
{
uint8_t v___x_1497_; 
v___x_1497_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__8___redArg(v_x_1495_, v_x_1496_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_1498_, lean_object* v_x_1499_, lean_object* v_x_1500_){
_start:
{
uint8_t v_res_1501_; lean_object* v_r_1502_; 
v_res_1501_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__8(v_00_u03b2_1498_, v_x_1499_, v_x_1500_);
lean_dec_ref(v_x_1500_);
lean_dec_ref(v_x_1499_);
v_r_1502_ = lean_box(v_res_1501_);
return v_r_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__14(lean_object* v_00_u03b2_1503_){
_start:
{
lean_object* v___x_1504_; 
v___x_1504_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__2);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9___redArg(){
_start:
{
lean_object* v___x_1506_; 
v___x_1506_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__2);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9___redArg___boxed(lean_object* v___dummy_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9___redArg();
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9(lean_object* v_00_u03b2_1509_){
_start:
{
lean_object* v___x_1510_; 
v___x_1510_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__2);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6_spec__12(lean_object* v_00_u03b2_1511_, lean_object* v_a_1512_, lean_object* v_x_1513_){
_start:
{
lean_object* v___x_1514_; 
v___x_1514_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6_spec__12___redArg(v_a_1512_, v_x_1513_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6_spec__12___boxed(lean_object* v_00_u03b2_1515_, lean_object* v_a_1516_, lean_object* v_x_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6_spec__12(v_00_u03b2_1515_, v_a_1516_, v_x_1517_);
lean_dec(v_x_1517_);
lean_dec(v_a_1516_);
return v_res_1518_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__8_spec__12(lean_object* v_00_u03b2_1519_, lean_object* v_x_1520_, size_t v_x_1521_, lean_object* v_x_1522_){
_start:
{
uint8_t v___x_1523_; 
v___x_1523_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__8_spec__12___redArg(v_x_1520_, v_x_1521_, v_x_1522_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__8_spec__12___boxed(lean_object* v_00_u03b2_1524_, lean_object* v_x_1525_, lean_object* v_x_1526_, lean_object* v_x_1527_){
_start:
{
size_t v_x_29825__boxed_1528_; uint8_t v_res_1529_; lean_object* v_r_1530_; 
v_x_29825__boxed_1528_ = lean_unbox_usize(v_x_1526_);
lean_dec(v_x_1526_);
v_res_1529_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__8_spec__12(v_00_u03b2_1524_, v_x_1525_, v_x_29825__boxed_1528_, v_x_1527_);
lean_dec_ref(v_x_1527_);
lean_dec_ref(v_x_1525_);
v_r_1530_ = lean_box(v_res_1529_);
return v_r_1530_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__8_spec__12_spec__15(lean_object* v_00_u03b2_1531_, lean_object* v_keys_1532_, lean_object* v_vals_1533_, lean_object* v_heq_1534_, lean_object* v_i_1535_, lean_object* v_k_1536_){
_start:
{
uint8_t v___x_1537_; 
v___x_1537_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__8_spec__12_spec__15___redArg(v_keys_1532_, v_i_1535_, v_k_1536_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__8_spec__12_spec__15___boxed(lean_object* v_00_u03b2_1538_, lean_object* v_keys_1539_, lean_object* v_vals_1540_, lean_object* v_heq_1541_, lean_object* v_i_1542_, lean_object* v_k_1543_){
_start:
{
uint8_t v_res_1544_; lean_object* v_r_1545_; 
v_res_1544_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__8_spec__12_spec__15(v_00_u03b2_1538_, v_keys_1539_, v_vals_1540_, v_heq_1541_, v_i_1542_, v_k_1543_);
lean_dec_ref(v_k_1543_);
lean_dec_ref(v_vals_1540_);
lean_dec_ref(v_keys_1539_);
v_r_1545_ = lean_box(v_res_1544_);
return v_r_1545_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Term_Quotation_runPrecheck_spec__0(lean_object* v_opts_1546_, lean_object* v_opt_1547_){
_start:
{
lean_object* v_name_1548_; lean_object* v_defValue_1549_; lean_object* v_map_1550_; lean_object* v___x_1551_; 
v_name_1548_ = lean_ctor_get(v_opt_1547_, 0);
v_defValue_1549_ = lean_ctor_get(v_opt_1547_, 1);
v_map_1550_ = lean_ctor_get(v_opts_1546_, 0);
v___x_1551_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1550_, v_name_1548_);
if (lean_obj_tag(v___x_1551_) == 0)
{
uint8_t v___x_1552_; 
v___x_1552_ = lean_unbox(v_defValue_1549_);
return v___x_1552_;
}
else
{
lean_object* v_val_1553_; 
v_val_1553_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_val_1553_);
lean_dec_ref_known(v___x_1551_, 1);
if (lean_obj_tag(v_val_1553_) == 1)
{
uint8_t v_v_1554_; 
v_v_1554_ = lean_ctor_get_uint8(v_val_1553_, 0);
lean_dec_ref_known(v_val_1553_, 0);
return v_v_1554_;
}
else
{
uint8_t v___x_1555_; 
lean_dec(v_val_1553_);
v___x_1555_ = lean_unbox(v_defValue_1549_);
return v___x_1555_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Term_Quotation_runPrecheck_spec__0___boxed(lean_object* v_opts_1556_, lean_object* v_opt_1557_){
_start:
{
uint8_t v_res_1558_; lean_object* v_r_1559_; 
v_res_1558_ = l_Lean_Option_get___at___00Lean_Elab_Term_Quotation_runPrecheck_spec__0(v_opts_1556_, v_opt_1557_);
lean_dec_ref(v_opt_1557_);
lean_dec_ref(v_opts_1556_);
v_r_1559_ = lean_box(v_res_1558_);
return v_r_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_runPrecheck(lean_object* v_stx_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_){
_start:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; uint8_t v___x_1573_; 
v___x_1571_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_1565_);
v___x_1572_ = l_Lean_Elab_Term_Quotation_quotPrecheck;
v___x_1573_ = l_Lean_Option_get___at___00Lean_Elab_Term_Quotation_runPrecheck_spec__0(v___x_1571_, v___x_1572_);
if (v___x_1573_ == 0)
{
lean_dec_ref(v___x_1571_);
lean_dec(v_stx_1560_);
goto v___jp_1568_;
}
else
{
lean_object* v___x_1574_; uint8_t v___x_1575_; 
v___x_1574_ = l_Lean_Elab_Term_Quotation_hygiene;
v___x_1575_ = l_Lean_Option_get___at___00Lean_Elab_Term_Quotation_runPrecheck_spec__0(v___x_1571_, v___x_1574_);
lean_dec_ref(v___x_1571_);
if (v___x_1575_ == 0)
{
lean_dec(v_stx_1560_);
goto v___jp_1568_;
}
else
{
lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1576_ = l_Lean_NameSet_empty;
v___x_1577_ = l_Lean_Elab_Term_Quotation_precheck(v_stx_1560_, v___x_1576_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_);
return v___x_1577_;
}
}
v___jp_1568_:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1569_ = lean_box(0);
v___x_1570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1569_);
return v___x_1570_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_runPrecheck___boxed(lean_object* v_stx_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_){
_start:
{
lean_object* v_res_1586_; 
v_res_1586_ = l_Lean_Elab_Term_Quotation_runPrecheck(v_stx_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_);
lean_dec(v_a_1584_);
lean_dec_ref(v_a_1583_);
lean_dec(v_a_1582_);
lean_dec_ref(v_a_1581_);
lean_dec(v_a_1580_);
lean_dec_ref(v_a_1579_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable_spec__0(lean_object* v_e_1590_, lean_object* v_init_1591_, lean_object* v_x_1592_){
_start:
{
if (lean_obj_tag(v_x_1592_) == 0)
{
lean_object* v_v_1593_; lean_object* v_l_1594_; lean_object* v_r_1595_; lean_object* v___x_1596_; 
v_v_1593_ = lean_ctor_get(v_x_1592_, 2);
v_l_1594_ = lean_ctor_get(v_x_1592_, 3);
v_r_1595_ = lean_ctor_get(v_x_1592_, 4);
v___x_1596_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable_spec__0(v_e_1590_, v_init_1591_, v_l_1594_);
if (lean_obj_tag(v___x_1596_) == 0)
{
return v___x_1596_;
}
else
{
lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1610_; 
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1610_ == 0)
{
lean_object* v_unused_1611_; 
v_unused_1611_ = lean_ctor_get(v___x_1596_, 0);
lean_dec(v_unused_1611_);
v___x_1598_ = v___x_1596_;
v_isShared_1599_ = v_isSharedCheck_1610_;
goto v_resetjp_1597_;
}
else
{
lean_dec(v___x_1596_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1610_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1600_; uint8_t v___x_1601_; 
v___x_1600_ = lean_box(0);
v___x_1601_ = lean_expr_eqv(v_e_1590_, v_v_1593_);
if (v___x_1601_ == 0)
{
lean_object* v___x_1602_; 
lean_del_object(v___x_1598_);
v___x_1602_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable_spec__0___closed__0));
v_init_1591_ = v___x_1602_;
v_x_1592_ = v_r_1595_;
goto _start;
}
else
{
lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1608_; 
v___x_1604_ = lean_box(v___x_1601_);
v___x_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1604_);
v___x_1606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1605_);
lean_ctor_set(v___x_1606_, 1, v___x_1600_);
if (v_isShared_1599_ == 0)
{
lean_ctor_set_tag(v___x_1598_, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1606_);
v___x_1608_ = v___x_1598_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v___x_1606_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
}
else
{
lean_object* v___x_1612_; 
v___x_1612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1612_, 0, v_init_1591_);
return v___x_1612_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable_spec__0___boxed(lean_object* v_e_1613_, lean_object* v_init_1614_, lean_object* v_x_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable_spec__0(v_e_1613_, v_init_1614_, v_x_1615_);
lean_dec(v_x_1615_);
lean_dec_ref(v_e_1613_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable___redArg(lean_object* v_e_1617_, lean_object* v_a_1618_){
_start:
{
lean_object* v___y_1621_; lean_object* v_sectionFVars_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v_a_1637_; 
v_sectionFVars_1634_ = lean_ctor_get(v_a_1618_, 5);
v___x_1635_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable_spec__0___closed__0));
v___x_1636_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable_spec__0(v_e_1617_, v___x_1635_, v_sectionFVars_1634_);
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
lean_inc(v_a_1637_);
lean_dec_ref(v___x_1636_);
v___y_1621_ = v_a_1637_;
goto v___jp_1620_;
v___jp_1620_:
{
lean_object* v_fst_1622_; 
v_fst_1622_ = lean_ctor_get(v___y_1621_, 0);
lean_inc(v_fst_1622_);
lean_dec_ref(v___y_1621_);
if (lean_obj_tag(v_fst_1622_) == 0)
{
uint8_t v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1623_ = 0;
v___x_1624_ = lean_box(v___x_1623_);
v___x_1625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1624_);
return v___x_1625_;
}
else
{
lean_object* v_val_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1633_; 
v_val_1626_ = lean_ctor_get(v_fst_1622_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v_fst_1622_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1628_ = v_fst_1622_;
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_val_1626_);
lean_dec(v_fst_1622_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1631_; 
if (v_isShared_1629_ == 0)
{
lean_ctor_set_tag(v___x_1628_, 0);
v___x_1631_ = v___x_1628_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_val_1626_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable___redArg___boxed(lean_object* v_e_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable___redArg(v_e_1638_, v_a_1639_);
lean_dec_ref(v_a_1639_);
lean_dec_ref(v_e_1638_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable(lean_object* v_e_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable___redArg(v_e_1642_, v_a_1643_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable___boxed(lean_object* v_e_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable(v_e_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_);
lean_dec(v_a_1657_);
lean_dec_ref(v_a_1656_);
lean_dec(v_a_1655_);
lean_dec_ref(v_a_1654_);
lean_dec(v_a_1653_);
lean_dec_ref(v_a_1652_);
lean_dec_ref(v_e_1651_);
return v_res_1659_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isQuotLocal_loop(lean_object* v_quotLCtx_1660_, lean_object* v_view_1661_, lean_object* v_a_1662_){
_start:
{
if (lean_obj_tag(v_a_1662_) == 1)
{
lean_object* v_pre_1663_; lean_object* v_imported_1664_; lean_object* v_ctx_1665_; lean_object* v_scopes_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; uint8_t v___x_1669_; 
v_pre_1663_ = lean_ctor_get(v_a_1662_, 0);
lean_inc(v_pre_1663_);
v_imported_1664_ = lean_ctor_get(v_view_1661_, 1);
v_ctx_1665_ = lean_ctor_get(v_view_1661_, 2);
v_scopes_1666_ = lean_ctor_get(v_view_1661_, 3);
lean_inc(v_scopes_1666_);
lean_inc(v_ctx_1665_);
lean_inc(v_imported_1664_);
v___x_1667_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1667_, 0, v_a_1662_);
lean_ctor_set(v___x_1667_, 1, v_imported_1664_);
lean_ctor_set(v___x_1667_, 2, v_ctx_1665_);
lean_ctor_set(v___x_1667_, 3, v_scopes_1666_);
v___x_1668_ = l_Lean_MacroScopesView_review(v___x_1667_);
v___x_1669_ = l_Lean_NameSet_contains(v_quotLCtx_1660_, v___x_1668_);
lean_dec(v___x_1668_);
if (v___x_1669_ == 0)
{
v_a_1662_ = v_pre_1663_;
goto _start;
}
else
{
lean_dec(v_pre_1663_);
return v___x_1669_;
}
}
else
{
uint8_t v___x_1671_; 
lean_dec(v_a_1662_);
v___x_1671_ = 0;
return v___x_1671_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isQuotLocal_loop___boxed(lean_object* v_quotLCtx_1672_, lean_object* v_view_1673_, lean_object* v_a_1674_){
_start:
{
uint8_t v_res_1675_; lean_object* v_r_1676_; 
v_res_1675_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isQuotLocal_loop(v_quotLCtx_1672_, v_view_1673_, v_a_1674_);
lean_dec_ref(v_view_1673_);
lean_dec(v_quotLCtx_1672_);
v_r_1676_ = lean_box(v_res_1675_);
return v_r_1676_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isQuotLocal(lean_object* v_quotLCtx_1677_, lean_object* v_n_1678_){
_start:
{
lean_object* v_view_1679_; lean_object* v_name_1680_; uint8_t v___x_1681_; 
v_view_1679_ = l_Lean_extractMacroScopes(v_n_1678_);
v_name_1680_ = lean_ctor_get(v_view_1679_, 0);
lean_inc(v_name_1680_);
v___x_1681_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isQuotLocal_loop(v_quotLCtx_1677_, v_view_1679_, v_name_1680_);
lean_dec_ref(v_view_1679_);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isQuotLocal___boxed(lean_object* v_quotLCtx_1682_, lean_object* v_n_1683_){
_start:
{
uint8_t v_res_1684_; lean_object* v_r_1685_; 
v_res_1684_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isQuotLocal(v_quotLCtx_1682_, v_n_1683_);
lean_dec(v_quotLCtx_1682_);
v_r_1685_ = lean_box(v_res_1684_);
return v_r_1685_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg(lean_object* v_as_x27_1694_, lean_object* v_b_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
if (lean_obj_tag(v_as_x27_1694_) == 0)
{
lean_object* v___x_1699_; 
v___x_1699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1699_, 0, v_b_1695_);
return v___x_1699_;
}
else
{
lean_object* v_head_1700_; lean_object* v_tail_1701_; lean_object* v_fst_1702_; lean_object* v___x_1703_; 
lean_dec_ref(v_b_1695_);
v_head_1700_ = lean_ctor_get(v_as_x27_1694_, 0);
v_tail_1701_ = lean_ctor_get(v_as_x27_1694_, 1);
v_fst_1702_ = lean_ctor_get(v_head_1700_, 0);
v___x_1703_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___closed__0));
if (lean_obj_tag(v_fst_1702_) == 1)
{
lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v_a_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1719_; 
v___x_1704_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1697_);
v___x_1705_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable___redArg(v_fst_1702_, v___y_1696_);
v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1708_ = v___x_1705_;
v_isShared_1709_ = v_isSharedCheck_1719_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_a_1706_);
lean_dec(v___x_1705_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1719_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1710_; uint8_t v___x_1711_; 
v___x_1710_ = l_Lean_Elab_Term_Quotation_quotPrecheck_allowSectionVars;
v___x_1711_ = l_Lean_Option_get___at___00Lean_Elab_Term_Quotation_runPrecheck_spec__0(v___x_1704_, v___x_1710_);
lean_dec_ref(v___x_1704_);
if (v___x_1711_ == 0)
{
lean_del_object(v___x_1708_);
lean_dec(v_a_1706_);
v_as_x27_1694_ = v_tail_1701_;
v_b_1695_ = v___x_1703_;
goto _start;
}
else
{
uint8_t v___x_1713_; 
v___x_1713_ = lean_unbox(v_a_1706_);
lean_dec(v_a_1706_);
if (v___x_1713_ == 0)
{
lean_del_object(v___x_1708_);
v_as_x27_1694_ = v_tail_1701_;
v_b_1695_ = v___x_1703_;
goto _start;
}
else
{
lean_object* v___x_1715_; lean_object* v___x_1717_; 
v___x_1715_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___closed__2));
if (v_isShared_1709_ == 0)
{
lean_ctor_set(v___x_1708_, 0, v___x_1715_);
v___x_1717_ = v___x_1708_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v___x_1715_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
}
}
else
{
v_as_x27_1694_ = v_tail_1701_;
v_b_1695_ = v___x_1703_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___boxed(lean_object* v_as_x27_1721_, lean_object* v_b_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg(v_as_x27_1721_, v_b_1722_, v___y_1723_, v___y_1724_);
lean_dec_ref(v___y_1724_);
lean_dec_ref(v___y_1723_);
lean_dec(v_as_x27_1721_);
return v_res_1726_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckIdent___closed__1(void){
_start:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1728_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckIdent___closed__0));
v___x_1729_ = l_Lean_stringToMessageData(v___x_1728_);
return v___x_1729_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckIdent___closed__3(void){
_start:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1731_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckIdent___closed__2));
v___x_1732_ = l_Lean_stringToMessageData(v___x_1731_);
return v___x_1732_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckIdent___closed__6(void){
_start:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1736_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckIdent___closed__5));
v___x_1737_ = l_Lean_MessageData_ofFormat(v___x_1736_);
return v___x_1737_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckIdent___closed__7(void){
_start:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1738_ = lean_obj_once(&l_Lean_Elab_Term_Quotation_precheckIdent___closed__6, &l_Lean_Elab_Term_Quotation_precheckIdent___closed__6_once, _init_l_Lean_Elab_Term_Quotation_precheckIdent___closed__6);
v___x_1739_ = l_Lean_MessageData_note(v___x_1738_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckIdent(lean_object* v_stx_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_){
_start:
{
if (lean_obj_tag(v_stx_1740_) == 3)
{
lean_object* v_val_1752_; lean_object* v_preresolved_1753_; lean_object* v_a_1755_; uint8_t v___x_1791_; 
v_val_1752_ = lean_ctor_get(v_stx_1740_, 2);
lean_inc(v_val_1752_);
v_preresolved_1753_ = lean_ctor_get(v_stx_1740_, 3);
v___x_1791_ = l_List_isEmpty___redArg(v_preresolved_1753_);
if (v___x_1791_ == 0)
{
lean_object* v___x_1792_; lean_object* v___x_1793_; 
lean_dec(v_val_1752_);
lean_dec_ref_known(v_stx_1740_, 4);
v___x_1792_ = lean_box(0);
v___x_1793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1792_);
return v___x_1793_;
}
else
{
lean_object* v___x_1794_; 
lean_inc(v_val_1752_);
lean_inc_ref(v_stx_1740_);
v___x_1794_ = l_Lean_Elab_realizeGlobalNameWithInfos(v_stx_1740_, v_val_1752_, v_a_1746_, v_a_1747_);
if (lean_obj_tag(v___x_1794_) == 0)
{
lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1830_; 
v_a_1795_ = lean_ctor_get(v___x_1794_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1797_ = v___x_1794_;
v_isShared_1798_ = v_isSharedCheck_1830_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1794_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1830_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
if (lean_obj_tag(v_a_1795_) == 1)
{
lean_object* v_head_1799_; lean_object* v_tail_1800_; 
lean_del_object(v___x_1797_);
v_head_1799_ = lean_ctor_get(v_a_1795_, 0);
lean_inc(v_head_1799_);
v_tail_1800_ = lean_ctor_get(v_a_1795_, 1);
lean_inc(v_tail_1800_);
lean_dec_ref_known(v_a_1795_, 2);
if (lean_obj_tag(v_tail_1800_) == 0)
{
lean_object* v_fst_1801_; lean_object* v___x_1802_; 
v_fst_1801_ = lean_ctor_get(v_head_1799_, 0);
lean_inc(v_fst_1801_);
lean_dec(v_head_1799_);
v___x_1802_ = l_Lean_Syntax_getHeadInfo(v_stx_1740_);
lean_dec_ref_known(v_stx_1740_, 4);
if (lean_obj_tag(v___x_1802_) == 1)
{
lean_dec_ref_known(v___x_1802_, 2);
lean_dec(v_fst_1801_);
lean_dec(v_val_1752_);
goto v___jp_1749_;
}
else
{
uint8_t v___x_1803_; 
lean_dec(v___x_1802_);
lean_inc(v_val_1752_);
v___x_1803_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isQuotLocal(v_a_1741_, v_val_1752_);
if (v___x_1803_ == 0)
{
lean_object* v_sectionVars_1804_; lean_object* v___x_1805_; uint8_t v___x_1806_; 
v_sectionVars_1804_ = lean_ctor_get(v_a_1742_, 4);
v___x_1805_ = l_Lean_Elab_Term_Quotation_resolveSectionVariable(v_sectionVars_1804_, v_val_1752_);
v___x_1806_ = l_List_isEmpty___redArg(v___x_1805_);
lean_dec(v___x_1805_);
if (v___x_1806_ == 0)
{
lean_dec(v_fst_1801_);
goto v___jp_1749_;
}
else
{
lean_object* v___x_1807_; 
v___x_1807_ = l_Lean_Elab_Term_checkDeprecatedCore___redArg(v_fst_1801_, v___x_1791_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_dec_ref_known(v___x_1807_, 1);
goto v___jp_1749_;
}
else
{
return v___x_1807_;
}
}
}
else
{
lean_dec(v_fst_1801_);
lean_dec(v_val_1752_);
goto v___jp_1749_;
}
}
}
else
{
lean_dec(v_tail_1800_);
lean_dec(v_head_1799_);
lean_dec(v_val_1752_);
lean_dec_ref_known(v_stx_1740_, 4);
goto v___jp_1749_;
}
}
else
{
uint8_t v___x_1808_; 
lean_dec(v_a_1795_);
lean_inc(v_val_1752_);
v___x_1808_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isQuotLocal(v_a_1741_, v_val_1752_);
if (v___x_1808_ == 0)
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
lean_del_object(v___x_1797_);
v___x_1809_ = lean_box(0);
v___x_1810_ = lean_box(0);
lean_inc(v_val_1752_);
v___x_1811_ = l_Lean_Elab_Term_resolveName(v_stx_1740_, v_val_1752_, v___x_1809_, v___x_1809_, v___x_1810_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v_a_1812_; 
v_a_1812_ = lean_ctor_get(v___x_1811_, 0);
lean_inc(v_a_1812_);
lean_dec_ref_known(v___x_1811_, 1);
v_a_1755_ = v_a_1812_;
goto v___jp_1754_;
}
else
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1825_; 
v_a_1813_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1815_ = v___x_1811_;
v_isShared_1816_ = v_isSharedCheck_1825_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1811_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1825_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
uint8_t v___x_1817_; 
v___x_1817_ = l_Lean_Exception_isInterrupt(v_a_1813_);
if (v___x_1817_ == 0)
{
uint8_t v___x_1818_; 
lean_inc(v_a_1813_);
v___x_1818_ = l_Lean_Exception_isRuntime(v_a_1813_);
if (v___x_1818_ == 0)
{
lean_del_object(v___x_1815_);
lean_dec(v_a_1813_);
v_a_1755_ = v___x_1809_;
goto v___jp_1754_;
}
else
{
lean_object* v___x_1820_; 
lean_dec(v_val_1752_);
if (v_isShared_1816_ == 0)
{
v___x_1820_ = v___x_1815_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_a_1813_);
v___x_1820_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
return v___x_1820_;
}
}
}
else
{
lean_object* v___x_1823_; 
lean_dec(v_val_1752_);
if (v_isShared_1816_ == 0)
{
v___x_1823_ = v___x_1815_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_a_1813_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
}
}
}
else
{
lean_object* v___x_1826_; lean_object* v___x_1828_; 
lean_dec(v_val_1752_);
lean_dec_ref_known(v_stx_1740_, 4);
v___x_1826_ = lean_box(0);
if (v_isShared_1798_ == 0)
{
lean_ctor_set(v___x_1797_, 0, v___x_1826_);
v___x_1828_ = v___x_1797_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v___x_1826_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
}
}
}
else
{
lean_object* v_a_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1838_; 
lean_dec(v_val_1752_);
lean_dec_ref_known(v_stx_1740_, 4);
v_a_1831_ = lean_ctor_get(v___x_1794_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1833_ = v___x_1794_;
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_a_1831_);
lean_dec(v___x_1794_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1836_; 
if (v_isShared_1834_ == 0)
{
v___x_1836_ = v___x_1833_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v_a_1831_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
return v___x_1836_;
}
}
}
}
v___jp_1754_:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1756_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___closed__0));
v___x_1757_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg(v_a_1755_, v___x_1756_, v_a_1742_, v_a_1746_);
lean_dec(v_a_1755_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1782_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1760_ = v___x_1757_;
v_isShared_1761_ = v_isSharedCheck_1782_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1757_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1782_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v_fst_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1780_; 
v_fst_1762_ = lean_ctor_get(v_a_1758_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v_a_1758_);
if (v_isSharedCheck_1780_ == 0)
{
lean_object* v_unused_1781_; 
v_unused_1781_ = lean_ctor_get(v_a_1758_, 1);
lean_dec(v_unused_1781_);
v___x_1764_ = v_a_1758_;
v_isShared_1765_ = v_isSharedCheck_1780_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_fst_1762_);
lean_dec(v_a_1758_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1780_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
if (lean_obj_tag(v_fst_1762_) == 0)
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1769_; 
lean_del_object(v___x_1760_);
v___x_1766_ = lean_obj_once(&l_Lean_Elab_Term_Quotation_precheckIdent___closed__1, &l_Lean_Elab_Term_Quotation_precheckIdent___closed__1_once, _init_l_Lean_Elab_Term_Quotation_precheckIdent___closed__1);
v___x_1767_ = l_Lean_MessageData_ofName(v_val_1752_);
if (v_isShared_1765_ == 0)
{
lean_ctor_set_tag(v___x_1764_, 7);
lean_ctor_set(v___x_1764_, 1, v___x_1767_);
lean_ctor_set(v___x_1764_, 0, v___x_1766_);
v___x_1769_ = v___x_1764_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v___x_1766_);
lean_ctor_set(v_reuseFailAlloc_1775_, 1, v___x_1767_);
v___x_1769_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1770_ = lean_obj_once(&l_Lean_Elab_Term_Quotation_precheckIdent___closed__3, &l_Lean_Elab_Term_Quotation_precheckIdent___closed__3_once, _init_l_Lean_Elab_Term_Quotation_precheckIdent___closed__3);
v___x_1771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1769_);
lean_ctor_set(v___x_1771_, 1, v___x_1770_);
v___x_1772_ = lean_obj_once(&l_Lean_Elab_Term_Quotation_precheckIdent___closed__7, &l_Lean_Elab_Term_Quotation_precheckIdent___closed__7_once, _init_l_Lean_Elab_Term_Quotation_precheckIdent___closed__7);
v___x_1773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1771_);
lean_ctor_set(v___x_1773_, 1, v___x_1772_);
v___x_1774_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1_spec__8___redArg(v___x_1773_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_);
return v___x_1774_;
}
}
else
{
lean_object* v_val_1776_; lean_object* v___x_1778_; 
lean_del_object(v___x_1764_);
lean_dec(v_val_1752_);
v_val_1776_ = lean_ctor_get(v_fst_1762_, 0);
lean_inc(v_val_1776_);
lean_dec_ref_known(v_fst_1762_, 1);
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 0, v_val_1776_);
v___x_1778_ = v___x_1760_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_val_1776_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
}
}
else
{
lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1790_; 
lean_dec(v_val_1752_);
v_a_1783_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1785_ = v___x_1757_;
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v___x_1757_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1788_; 
if (v_isShared_1786_ == 0)
{
v___x_1788_ = v___x_1785_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_a_1783_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
}
}
}
else
{
lean_object* v___x_1839_; 
lean_dec(v_stx_1740_);
v___x_1839_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
return v___x_1839_;
}
v___jp_1749_:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1750_ = lean_box(0);
v___x_1751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1750_);
return v___x_1751_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___boxed(lean_object* v_stx_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l_Lean_Elab_Term_Quotation_precheckIdent(v_stx_1840_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_, v_a_1846_, v_a_1847_);
lean_dec(v_a_1847_);
lean_dec_ref(v_a_1846_);
lean_dec(v_a_1845_);
lean_dec_ref(v_a_1844_);
lean_dec(v_a_1843_);
lean_dec_ref(v_a_1842_);
lean_dec(v_a_1841_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0(lean_object* v_as_1850_, lean_object* v_as_x27_1851_, lean_object* v_b_1852_, lean_object* v_a_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_){
_start:
{
lean_object* v___x_1862_; 
v___x_1862_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg(v_as_x27_1851_, v_b_1852_, v___y_1855_, v___y_1859_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___boxed(lean_object* v_as_1863_, lean_object* v_as_x27_1864_, lean_object* v_b_1865_, lean_object* v_a_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0(v_as_1863_, v_as_x27_1864_, v_b_1865_, v_a_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1872_);
lean_dec(v___y_1871_);
lean_dec_ref(v___y_1870_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
lean_dec(v___y_1867_);
lean_dec(v_as_x27_1864_);
lean_dec(v_as_1863_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1(){
_start:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1887_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
v___x_1888_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__1));
v___x_1889_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__3));
v___x_1890_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckIdent___boxed), 9, 0);
v___x_1891_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1887_, v___x_1888_, v___x_1889_, v___x_1890_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___boxed(lean_object* v_a_1892_){
_start:
{
lean_object* v_res_1893_; 
v_res_1893_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1();
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0(lean_object* v_as_1907_, size_t v_sz_1908_, size_t v_i_1909_, lean_object* v_b_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_){
_start:
{
lean_object* v_a_1920_; uint8_t v___x_1924_; 
v___x_1924_ = lean_usize_dec_lt(v_i_1909_, v_sz_1908_);
if (v___x_1924_ == 0)
{
lean_object* v___x_1925_; 
v___x_1925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1925_, 0, v_b_1910_);
return v___x_1925_;
}
else
{
lean_object* v___x_1926_; lean_object* v_a_1927_; lean_object* v___x_1928_; uint8_t v___x_1929_; 
v___x_1926_ = lean_box(0);
v_a_1927_ = lean_array_uget_borrowed(v_as_1907_, v_i_1909_);
v___x_1928_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__2));
lean_inc(v_a_1927_);
v___x_1929_ = l_Lean_Syntax_isOfKind(v_a_1927_, v___x_1928_);
if (v___x_1929_ == 0)
{
lean_object* v___x_1930_; uint8_t v___x_1931_; 
v___x_1930_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__4));
lean_inc(v_a_1927_);
v___x_1931_ = l_Lean_Syntax_isOfKind(v_a_1927_, v___x_1930_);
if (v___x_1931_ == 0)
{
lean_object* v___x_1932_; 
lean_inc(v_a_1927_);
v___x_1932_ = l_Lean_Elab_Term_Quotation_precheck(v_a_1927_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_dec_ref_known(v___x_1932_, 1);
v_a_1920_ = v___x_1926_;
goto v___jp_1919_;
}
else
{
return v___x_1932_;
}
}
else
{
v_a_1920_ = v___x_1926_;
goto v___jp_1919_;
}
}
else
{
lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1933_ = lean_unsigned_to_nat(3u);
v___x_1934_ = l_Lean_Syntax_getArg(v_a_1927_, v___x_1933_);
v___x_1935_ = l_Lean_Elab_Term_Quotation_precheck(v___x_1934_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_dec_ref_known(v___x_1935_, 1);
v_a_1920_ = v___x_1926_;
goto v___jp_1919_;
}
else
{
return v___x_1935_;
}
}
}
v___jp_1919_:
{
size_t v___x_1921_; size_t v___x_1922_; 
v___x_1921_ = ((size_t)1ULL);
v___x_1922_ = lean_usize_add(v_i_1909_, v___x_1921_);
v_i_1909_ = v___x_1922_;
v_b_1910_ = v_a_1920_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___boxed(lean_object* v_as_1936_, lean_object* v_sz_1937_, lean_object* v_i_1938_, lean_object* v_b_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_){
_start:
{
size_t v_sz_boxed_1948_; size_t v_i_boxed_1949_; lean_object* v_res_1950_; 
v_sz_boxed_1948_ = lean_unbox_usize(v_sz_1937_);
lean_dec(v_sz_1937_);
v_i_boxed_1949_ = lean_unbox_usize(v_i_1938_);
lean_dec(v_i_1938_);
v_res_1950_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0(v_as_1936_, v_sz_boxed_1948_, v_i_boxed_1949_, v_b_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
lean_dec(v___y_1942_);
lean_dec_ref(v___y_1941_);
lean_dec(v___y_1940_);
lean_dec_ref(v_as_1936_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckApp(lean_object* v_x_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_){
_start:
{
lean_object* v___x_1966_; uint8_t v___x_1967_; 
v___x_1966_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckApp___closed__1));
lean_inc(v_x_1957_);
v___x_1967_ = l_Lean_Syntax_isOfKind(v_x_1957_, v___x_1966_);
if (v___x_1967_ == 0)
{
lean_object* v___x_1968_; 
lean_dec(v_x_1957_);
v___x_1968_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
return v___x_1968_;
}
else
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v_args_1973_; lean_object* v___x_1974_; 
v___x_1969_ = lean_unsigned_to_nat(0u);
v___x_1970_ = l_Lean_Syntax_getArg(v_x_1957_, v___x_1969_);
v___x_1971_ = lean_unsigned_to_nat(1u);
v___x_1972_ = l_Lean_Syntax_getArg(v_x_1957_, v___x_1971_);
lean_dec(v_x_1957_);
v_args_1973_ = l_Lean_Syntax_getArgs(v___x_1972_);
lean_dec(v___x_1972_);
v___x_1974_ = l_Lean_Elab_Term_Quotation_precheck(v___x_1970_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v___x_1975_; size_t v_sz_1976_; size_t v___x_1977_; lean_object* v___x_1978_; 
lean_dec_ref_known(v___x_1974_, 1);
v___x_1975_ = lean_box(0);
v_sz_1976_ = lean_array_size(v_args_1973_);
v___x_1977_ = ((size_t)0ULL);
v___x_1978_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0(v_args_1973_, v_sz_1976_, v___x_1977_, v___x_1975_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_);
lean_dec_ref(v_args_1973_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1985_; 
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_1985_ == 0)
{
lean_object* v_unused_1986_; 
v_unused_1986_ = lean_ctor_get(v___x_1978_, 0);
lean_dec(v_unused_1986_);
v___x_1980_ = v___x_1978_;
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
else
{
lean_dec(v___x_1978_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1983_; 
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 0, v___x_1975_);
v___x_1983_ = v___x_1980_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v___x_1975_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
else
{
return v___x_1978_;
}
}
else
{
lean_dec_ref(v_args_1973_);
return v___x_1974_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckApp___boxed(lean_object* v_x_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l_Lean_Elab_Term_Quotation_precheckApp(v_x_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_);
lean_dec(v_a_1994_);
lean_dec_ref(v_a_1993_);
lean_dec(v_a_1992_);
lean_dec_ref(v_a_1991_);
lean_dec(v_a_1990_);
lean_dec_ref(v_a_1989_);
lean_dec(v_a_1988_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1(){
_start:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2005_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
v___x_2006_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckApp___closed__1));
v___x_2007_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__1));
v___x_2008_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckApp___boxed), 9, 0);
v___x_2009_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2005_, v___x_2006_, v___x_2007_, v___x_2008_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___boxed(lean_object* v_a_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1();
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckTypeAscription(lean_object* v_x_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_){
_start:
{
lean_object* v___x_2033_; uint8_t v___x_2034_; 
v___x_2033_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__1));
lean_inc(v_x_2024_);
v___x_2034_ = l_Lean_Syntax_isOfKind(v_x_2024_, v___x_2033_);
if (v___x_2034_ == 0)
{
lean_object* v___x_2035_; 
lean_dec(v_x_2024_);
v___x_2035_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
return v___x_2035_;
}
else
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; uint8_t v___x_2039_; 
v___x_2036_ = lean_unsigned_to_nat(0u);
v___x_2037_ = l_Lean_Syntax_getArg(v_x_2024_, v___x_2036_);
v___x_2038_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__3));
lean_inc(v___x_2037_);
v___x_2039_ = l_Lean_Syntax_isOfKind(v___x_2037_, v___x_2038_);
if (v___x_2039_ == 0)
{
lean_object* v___x_2040_; 
lean_dec(v___x_2037_);
lean_dec(v_x_2024_);
v___x_2040_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
return v___x_2040_;
}
else
{
lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; uint8_t v___x_2044_; 
v___x_2041_ = lean_unsigned_to_nat(1u);
v___x_2042_ = l_Lean_Syntax_getArg(v___x_2037_, v___x_2041_);
lean_dec(v___x_2037_);
v___x_2043_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___closed__1));
lean_inc(v___x_2042_);
v___x_2044_ = l_Lean_Syntax_isOfKind(v___x_2042_, v___x_2043_);
if (v___x_2044_ == 0)
{
lean_object* v___x_2045_; 
lean_dec(v___x_2042_);
lean_dec(v_x_2024_);
v___x_2045_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
return v___x_2045_;
}
else
{
lean_object* v___x_2046_; lean_object* v___x_2047_; uint8_t v___x_2048_; 
v___x_2046_ = l_Lean_Syntax_getArg(v___x_2042_, v___x_2036_);
lean_dec(v___x_2042_);
v___x_2047_ = lean_box(0);
v___x_2048_ = l_Lean_Syntax_matchesIdent(v___x_2046_, v___x_2047_);
lean_dec(v___x_2046_);
if (v___x_2048_ == 0)
{
lean_object* v___x_2049_; 
lean_dec(v_x_2024_);
v___x_2049_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
return v___x_2049_;
}
else
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; uint8_t v___x_2053_; 
v___x_2050_ = l_Lean_Syntax_getArg(v_x_2024_, v___x_2041_);
v___x_2051_ = lean_unsigned_to_nat(3u);
v___x_2052_ = l_Lean_Syntax_getArg(v_x_2024_, v___x_2051_);
lean_dec(v_x_2024_);
lean_inc(v___x_2052_);
v___x_2053_ = l_Lean_Syntax_matchesNull(v___x_2052_, v___x_2041_);
if (v___x_2053_ == 0)
{
uint8_t v___x_2054_; 
v___x_2054_ = l_Lean_Syntax_matchesNull(v___x_2052_, v___x_2036_);
if (v___x_2054_ == 0)
{
lean_object* v___x_2055_; 
lean_dec(v___x_2050_);
v___x_2055_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
return v___x_2055_;
}
else
{
lean_object* v___x_2056_; 
v___x_2056_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2050_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_);
return v___x_2056_;
}
}
else
{
lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2057_ = l_Lean_Syntax_getArg(v___x_2052_, v___x_2036_);
lean_dec(v___x_2052_);
v___x_2058_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2050_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v___x_2059_; 
lean_dec_ref_known(v___x_2058_, 1);
v___x_2059_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2057_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_);
return v___x_2059_;
}
else
{
lean_dec(v___x_2057_);
return v___x_2058_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckTypeAscription___boxed(lean_object* v_x_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_){
_start:
{
lean_object* v_res_2069_; 
v_res_2069_ = l_Lean_Elab_Term_Quotation_precheckTypeAscription(v_x_2060_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_);
lean_dec(v_a_2067_);
lean_dec_ref(v_a_2066_);
lean_dec(v_a_2065_);
lean_dec_ref(v_a_2064_);
lean_dec(v_a_2063_);
lean_dec_ref(v_a_2062_);
lean_dec(v_a_2061_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1(){
_start:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2078_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
v___x_2079_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__1));
v___x_2080_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__1));
v___x_2081_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckTypeAscription___boxed), 9, 0);
v___x_2082_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2078_, v___x_2079_, v___x_2080_, v___x_2081_);
return v___x_2082_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___boxed(lean_object* v_a_2083_){
_start:
{
lean_object* v_res_2084_; 
v_res_2084_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1();
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckExplicit(lean_object* v_x_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_){
_start:
{
lean_object* v___x_2100_; uint8_t v___x_2101_; 
v___x_2100_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckExplicit___closed__1));
lean_inc(v_x_2091_);
v___x_2101_ = l_Lean_Syntax_isOfKind(v_x_2091_, v___x_2100_);
if (v___x_2101_ == 0)
{
lean_object* v___x_2102_; 
lean_dec(v_x_2091_);
v___x_2102_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
return v___x_2102_;
}
else
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2103_ = lean_unsigned_to_nat(1u);
v___x_2104_ = l_Lean_Syntax_getArg(v_x_2091_, v___x_2103_);
lean_dec(v_x_2091_);
v___x_2105_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2104_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_);
return v___x_2105_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckExplicit___boxed(lean_object* v_x_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_){
_start:
{
lean_object* v_res_2115_; 
v_res_2115_ = l_Lean_Elab_Term_Quotation_precheckExplicit(v_x_2106_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_);
lean_dec(v_a_2113_);
lean_dec_ref(v_a_2112_);
lean_dec(v_a_2111_);
lean_dec_ref(v_a_2110_);
lean_dec(v_a_2109_);
lean_dec_ref(v_a_2108_);
lean_dec(v_a_2107_);
return v_res_2115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1(){
_start:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2124_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
v___x_2125_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckExplicit___closed__1));
v___x_2126_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__1));
v___x_2127_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckExplicit___boxed), 9, 0);
v___x_2128_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2124_, v___x_2125_, v___x_2126_, v___x_2127_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___boxed(lean_object* v_a_2129_){
_start:
{
lean_object* v_res_2130_; 
v_res_2130_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1();
return v_res_2130_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2132_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1___closed__0));
v___x_2133_ = l_Lean_stringToMessageData(v___x_2132_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1(lean_object* v_as_2134_, size_t v_i_2135_, size_t v_stop_2136_, lean_object* v_b_2137_){
_start:
{
lean_object* v___y_2139_; uint8_t v___x_2143_; 
v___x_2143_ = lean_usize_dec_eq(v_i_2135_, v_stop_2136_);
if (v___x_2143_ == 0)
{
lean_object* v___x_2144_; lean_object* v_fst_2145_; 
v___x_2144_ = lean_array_uget(v_as_2134_, v_i_2135_);
v_fst_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_fst_2145_);
if (lean_obj_tag(v_fst_2145_) == 0)
{
lean_object* v_snd_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2159_; 
v_snd_2146_ = lean_ctor_get(v___x_2144_, 1);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2159_ == 0)
{
lean_object* v_unused_2160_; 
v_unused_2160_ = lean_ctor_get(v___x_2144_, 0);
lean_dec(v_unused_2160_);
v___x_2148_ = v___x_2144_;
v_isShared_2149_ = v_isSharedCheck_2159_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_snd_2146_);
lean_dec(v___x_2144_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2159_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v_a_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2154_; 
v_a_2150_ = lean_ctor_get(v_fst_2145_, 0);
lean_inc(v_a_2150_);
lean_dec_ref_known(v_fst_2145_, 1);
v___x_2151_ = l_Lean_MessageData_ofSyntax(v_snd_2146_);
v___x_2152_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1___closed__1);
if (v_isShared_2149_ == 0)
{
lean_ctor_set_tag(v___x_2148_, 7);
lean_ctor_set(v___x_2148_, 1, v___x_2152_);
lean_ctor_set(v___x_2148_, 0, v___x_2151_);
v___x_2154_ = v___x_2148_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v___x_2151_);
lean_ctor_set(v_reuseFailAlloc_2158_, 1, v___x_2152_);
v___x_2154_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2155_ = l_Lean_Exception_toMessageData(v_a_2150_);
v___x_2156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2154_);
lean_ctor_set(v___x_2156_, 1, v___x_2155_);
v___x_2157_ = lean_array_push(v_b_2137_, v___x_2156_);
v___y_2139_ = v___x_2157_;
goto v___jp_2138_;
}
}
}
else
{
lean_dec(v_fst_2145_);
lean_dec(v___x_2144_);
v___y_2139_ = v_b_2137_;
goto v___jp_2138_;
}
}
else
{
return v_b_2137_;
}
v___jp_2138_:
{
size_t v___x_2140_; size_t v___x_2141_; 
v___x_2140_ = ((size_t)1ULL);
v___x_2141_ = lean_usize_add(v_i_2135_, v___x_2140_);
v_i_2135_ = v___x_2141_;
v_b_2137_ = v___y_2139_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1___boxed(lean_object* v_as_2161_, lean_object* v_i_2162_, lean_object* v_stop_2163_, lean_object* v_b_2164_){
_start:
{
size_t v_i_boxed_2165_; size_t v_stop_boxed_2166_; lean_object* v_res_2167_; 
v_i_boxed_2165_ = lean_unbox_usize(v_i_2162_);
lean_dec(v_i_2162_);
v_stop_boxed_2166_ = lean_unbox_usize(v_stop_2163_);
lean_dec(v_stop_2163_);
v_res_2167_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1(v_as_2161_, v_i_boxed_2165_, v_stop_boxed_2166_, v_b_2164_);
lean_dec_ref(v_as_2161_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1(lean_object* v_as_2168_, lean_object* v_start_2169_, lean_object* v_stop_2170_){
_start:
{
lean_object* v___x_2171_; uint8_t v___x_2172_; 
v___x_2171_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___closed__2));
v___x_2172_ = lean_nat_dec_lt(v_start_2169_, v_stop_2170_);
if (v___x_2172_ == 0)
{
return v___x_2171_;
}
else
{
lean_object* v___x_2173_; uint8_t v___x_2174_; 
v___x_2173_ = lean_array_get_size(v_as_2168_);
v___x_2174_ = lean_nat_dec_le(v_stop_2170_, v___x_2173_);
if (v___x_2174_ == 0)
{
uint8_t v___x_2175_; 
v___x_2175_ = lean_nat_dec_lt(v_start_2169_, v___x_2173_);
if (v___x_2175_ == 0)
{
return v___x_2171_;
}
else
{
size_t v___x_2176_; size_t v___x_2177_; lean_object* v___x_2178_; 
v___x_2176_ = lean_usize_of_nat(v_start_2169_);
v___x_2177_ = lean_usize_of_nat(v___x_2173_);
v___x_2178_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1(v_as_2168_, v___x_2176_, v___x_2177_, v___x_2171_);
return v___x_2178_;
}
}
else
{
size_t v___x_2179_; size_t v___x_2180_; lean_object* v___x_2181_; 
v___x_2179_ = lean_usize_of_nat(v_start_2169_);
v___x_2180_ = lean_usize_of_nat(v_stop_2170_);
v___x_2181_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1(v_as_2168_, v___x_2179_, v___x_2180_, v___x_2171_);
return v___x_2181_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1___boxed(lean_object* v_as_2182_, lean_object* v_start_2183_, lean_object* v_stop_2184_){
_start:
{
lean_object* v_res_2185_; 
v_res_2185_ = l_Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1(v_as_2182_, v_start_2183_, v_stop_2184_);
lean_dec(v_stop_2184_);
lean_dec(v_start_2183_);
lean_dec_ref(v_as_2182_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__0(size_t v_sz_2186_, size_t v_i_2187_, lean_object* v_bs_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_){
_start:
{
uint8_t v___x_2197_; 
v___x_2197_ = lean_usize_dec_lt(v_i_2187_, v_sz_2186_);
if (v___x_2197_ == 0)
{
lean_object* v___x_2198_; 
v___x_2198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2198_, 0, v_bs_2188_);
return v___x_2198_;
}
else
{
lean_object* v_v_2199_; lean_object* v___x_2200_; lean_object* v_bs_x27_2201_; lean_object* v_a_2203_; lean_object* v___x_2208_; 
v_v_2199_ = lean_array_uget(v_bs_2188_, v_i_2187_);
v___x_2200_ = lean_unsigned_to_nat(0u);
v_bs_x27_2201_ = lean_array_uset(v_bs_2188_, v_i_2187_, v___x_2200_);
v___x_2208_ = l_Lean_Elab_Term_Quotation_precheck(v_v_2199_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_);
if (lean_obj_tag(v___x_2208_) == 0)
{
lean_object* v_a_2209_; lean_object* v___x_2210_; 
v_a_2209_ = lean_ctor_get(v___x_2208_, 0);
lean_inc(v_a_2209_);
lean_dec_ref_known(v___x_2208_, 1);
v___x_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2210_, 0, v_a_2209_);
v_a_2203_ = v___x_2210_;
goto v___jp_2202_;
}
else
{
lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2224_; 
v_a_2211_ = lean_ctor_get(v___x_2208_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2213_ = v___x_2208_;
v_isShared_2214_ = v_isSharedCheck_2224_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_dec(v___x_2208_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2224_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
uint8_t v___x_2215_; 
v___x_2215_ = l_Lean_Exception_isInterrupt(v_a_2211_);
if (v___x_2215_ == 0)
{
uint8_t v___x_2216_; 
lean_inc(v_a_2211_);
v___x_2216_ = l_Lean_Exception_isRuntime(v_a_2211_);
if (v___x_2216_ == 0)
{
lean_object* v___x_2217_; 
lean_del_object(v___x_2213_);
v___x_2217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2217_, 0, v_a_2211_);
v_a_2203_ = v___x_2217_;
goto v___jp_2202_;
}
else
{
lean_object* v___x_2219_; 
lean_dec_ref(v_bs_x27_2201_);
if (v_isShared_2214_ == 0)
{
v___x_2219_ = v___x_2213_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_a_2211_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
else
{
lean_object* v___x_2222_; 
lean_dec_ref(v_bs_x27_2201_);
if (v_isShared_2214_ == 0)
{
v___x_2222_ = v___x_2213_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_a_2211_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
}
v___jp_2202_:
{
size_t v___x_2204_; size_t v___x_2205_; lean_object* v___x_2206_; 
v___x_2204_ = ((size_t)1ULL);
v___x_2205_ = lean_usize_add(v_i_2187_, v___x_2204_);
v___x_2206_ = lean_array_uset(v_bs_x27_2201_, v_i_2187_, v_a_2203_);
v_i_2187_ = v___x_2205_;
v_bs_2188_ = v___x_2206_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__0___boxed(lean_object* v_sz_2225_, lean_object* v_i_2226_, lean_object* v_bs_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_){
_start:
{
size_t v_sz_boxed_2236_; size_t v_i_boxed_2237_; lean_object* v_res_2238_; 
v_sz_boxed_2236_ = lean_unbox_usize(v_sz_2225_);
lean_dec(v_sz_2225_);
v_i_boxed_2237_ = lean_unbox_usize(v_i_2226_);
lean_dec(v_i_2226_);
v_res_2238_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__0(v_sz_boxed_2236_, v_i_boxed_2237_, v_bs_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec(v___y_2232_);
lean_dec_ref(v___y_2231_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec(v___y_2228_);
return v_res_2238_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckChoice___closed__1(void){
_start:
{
lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2240_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckChoice___closed__0));
v___x_2241_ = l_Lean_stringToMessageData(v___x_2240_);
return v___x_2241_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckChoice___closed__3(void){
_start:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2243_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckChoice___closed__2));
v___x_2244_ = l_Lean_stringToMessageData(v___x_2243_);
return v___x_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckChoice(lean_object* v_stx_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_){
_start:
{
lean_object* v___x_2254_; size_t v_sz_2255_; size_t v___x_2256_; lean_object* v___x_2257_; 
v___x_2254_ = l_Lean_Syntax_getArgs(v_stx_2245_);
v_sz_2255_ = lean_array_size(v___x_2254_);
v___x_2256_ = ((size_t)0ULL);
lean_inc_ref(v___x_2254_);
v___x_2257_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__0(v_sz_2255_, v___x_2256_, v___x_2254_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_);
if (lean_obj_tag(v___x_2257_) == 0)
{
lean_object* v_a_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2279_; 
v_a_2258_ = lean_ctor_get(v___x_2257_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2260_ = v___x_2257_;
v_isShared_2261_ = v_isSharedCheck_2279_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_a_2258_);
lean_dec(v___x_2257_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2279_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; uint8_t v___x_2267_; 
v___x_2262_ = l_Array_zip___redArg(v_a_2258_, v___x_2254_);
lean_dec_ref(v___x_2254_);
lean_dec(v_a_2258_);
v___x_2263_ = lean_unsigned_to_nat(0u);
v___x_2264_ = lean_array_get_size(v___x_2262_);
v___x_2265_ = l_Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1(v___x_2262_, v___x_2263_, v___x_2264_);
lean_dec_ref(v___x_2262_);
v___x_2266_ = lean_array_get_size(v___x_2265_);
v___x_2267_ = lean_nat_dec_eq(v___x_2266_, v___x_2263_);
if (v___x_2267_ == 0)
{
lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
lean_del_object(v___x_2260_);
v___x_2268_ = lean_obj_once(&l_Lean_Elab_Term_Quotation_precheckChoice___closed__1, &l_Lean_Elab_Term_Quotation_precheckChoice___closed__1_once, _init_l_Lean_Elab_Term_Quotation_precheckChoice___closed__1);
v___x_2269_ = lean_array_to_list(v___x_2265_);
v___x_2270_ = lean_obj_once(&l_Lean_Elab_Term_Quotation_precheckChoice___closed__3, &l_Lean_Elab_Term_Quotation_precheckChoice___closed__3_once, _init_l_Lean_Elab_Term_Quotation_precheckChoice___closed__3);
v___x_2271_ = l_Lean_MessageData_joinSep(v___x_2269_, v___x_2270_);
v___x_2272_ = l_Lean_indentD(v___x_2271_);
v___x_2273_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2268_);
lean_ctor_set(v___x_2273_, 1, v___x_2272_);
v___x_2274_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1___redArg(v_stx_2245_, v___x_2273_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_);
return v___x_2274_;
}
else
{
lean_object* v___x_2275_; lean_object* v___x_2277_; 
lean_dec_ref(v___x_2265_);
v___x_2275_ = lean_box(0);
if (v_isShared_2261_ == 0)
{
lean_ctor_set(v___x_2260_, 0, v___x_2275_);
v___x_2277_ = v___x_2260_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v___x_2275_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
}
else
{
lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2287_; 
lean_dec_ref(v___x_2254_);
v_a_2280_ = lean_ctor_get(v___x_2257_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2282_ = v___x_2257_;
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_dec(v___x_2257_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v___x_2285_; 
if (v_isShared_2283_ == 0)
{
v___x_2285_ = v___x_2282_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_a_2280_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
return v___x_2285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckChoice___boxed(lean_object* v_stx_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_){
_start:
{
lean_object* v_res_2297_; 
v_res_2297_ = l_Lean_Elab_Term_Quotation_precheckChoice(v_stx_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_);
lean_dec(v_a_2295_);
lean_dec_ref(v_a_2294_);
lean_dec(v_a_2293_);
lean_dec_ref(v_a_2292_);
lean_dec(v_a_2291_);
lean_dec_ref(v_a_2290_);
lean_dec(v_a_2289_);
lean_dec(v_stx_2288_);
return v_res_2297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1(){
_start:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2309_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
v___x_2310_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__1));
v___x_2311_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__3));
v___x_2312_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckChoice___boxed), 9, 0);
v___x_2313_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2309_, v___x_2310_, v___x_2311_, v___x_2312_);
return v___x_2313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___boxed(lean_object* v_a_2314_){
_start:
{
lean_object* v_res_2315_; 
v_res_2315_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1();
return v_res_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___lam__0(lean_object* v_singleQuot_2316_, lean_object* v_x_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_){
_start:
{
lean_object* v___x_2325_; 
v___x_2325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2325_, 0, v_singleQuot_2316_);
return v___x_2325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___lam__0___boxed(lean_object* v_singleQuot_2326_, lean_object* v_x_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_){
_start:
{
lean_object* v_res_2335_; 
v_res_2335_ = l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___lam__0(v_singleQuot_2326_, v_x_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
lean_dec(v_x_2327_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot(lean_object* v_stx_2336_, lean_object* v_expectedType_x3f_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_){
_start:
{
lean_object* v___x_2345_; lean_object* v_singleQuot_2346_; lean_object* v___f_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2345_ = lean_unsigned_to_nat(1u);
v_singleQuot_2346_ = l_Lean_Syntax_getArg(v_stx_2336_, v___x_2345_);
lean_inc(v_singleQuot_2346_);
v___f_2347_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___lam__0___boxed), 9, 1);
lean_closure_set(v___f_2347_, 0, v_singleQuot_2346_);
v___x_2348_ = l_Lean_Syntax_getQuotContent(v_singleQuot_2346_);
v___x_2349_ = l_Lean_Elab_Term_Quotation_runPrecheck(v___x_2348_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_);
if (lean_obj_tag(v___x_2349_) == 0)
{
lean_object* v___x_2350_; 
lean_dec_ref_known(v___x_2349_, 1);
v___x_2350_ = l_Lean_Elab_Term_adaptExpander(v___f_2347_, v_stx_2336_, v_expectedType_x3f_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_);
return v___x_2350_;
}
else
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2358_; 
lean_dec_ref(v___f_2347_);
lean_dec(v_expectedType_x3f_2337_);
lean_dec(v_stx_2336_);
v_a_2351_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2353_ = v___x_2349_;
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2349_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2356_; 
if (v_isShared_2354_ == 0)
{
v___x_2356_ = v___x_2353_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_a_2351_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___boxed(lean_object* v_stx_2359_, lean_object* v_expectedType_x3f_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_){
_start:
{
lean_object* v_res_2368_; 
v_res_2368_ = l_Lean_Elab_Term_Quotation_elabPrecheckedQuot(v_stx_2359_, v_expectedType_x3f_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_);
lean_dec(v_a_2366_);
lean_dec_ref(v_a_2365_);
lean_dec(v_a_2364_);
lean_dec_ref(v_a_2363_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
return v_res_2368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1(){
_start:
{
lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___x_2383_ = l_Lean_Elab_Term_termElabAttribute;
v___x_2384_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__1));
v___x_2385_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3));
v___x_2386_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___boxed), 9, 0);
v___x_2387_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2383_, v___x_2384_, v___x_2385_, v___x_2386_);
return v___x_2387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___boxed(lean_object* v_a_2388_){
_start:
{
lean_object* v_res_2389_; 
v_res_2389_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1();
return v_res_2389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3(){
_start:
{
lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___x_2416_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3));
v___x_2417_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__6));
v___x_2418_ = l_Lean_addBuiltinDeclarationRanges(v___x_2416_, v___x_2417_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___boxed(lean_object* v_a_2419_){
_start:
{
lean_object* v_res_2420_; 
v_res_2420_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3();
return v_res_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinrel(lean_object* v_x_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_){
_start:
{
lean_object* v___x_2436_; uint8_t v___x_2437_; 
v___x_2436_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckBinrel___closed__1));
lean_inc(v_x_2427_);
v___x_2437_ = l_Lean_Syntax_isOfKind(v_x_2427_, v___x_2436_);
if (v___x_2437_ == 0)
{
lean_object* v___x_2438_; 
lean_dec(v_x_2427_);
v___x_2438_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
return v___x_2438_;
}
else
{
lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2439_ = lean_unsigned_to_nat(1u);
v___x_2440_ = l_Lean_Syntax_getArg(v_x_2427_, v___x_2439_);
v___x_2441_ = lean_unsigned_to_nat(2u);
v___x_2442_ = l_Lean_Syntax_getArg(v_x_2427_, v___x_2441_);
v___x_2443_ = lean_unsigned_to_nat(3u);
v___x_2444_ = l_Lean_Syntax_getArg(v_x_2427_, v___x_2443_);
lean_dec(v_x_2427_);
v___x_2445_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2440_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_);
if (lean_obj_tag(v___x_2445_) == 0)
{
lean_object* v___x_2446_; 
lean_dec_ref_known(v___x_2445_, 1);
v___x_2446_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2442_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_);
if (lean_obj_tag(v___x_2446_) == 0)
{
lean_object* v___x_2447_; 
lean_dec_ref_known(v___x_2446_, 1);
v___x_2447_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2444_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_);
return v___x_2447_;
}
else
{
lean_dec(v___x_2444_);
return v___x_2446_;
}
}
else
{
lean_dec(v___x_2444_);
lean_dec(v___x_2442_);
return v___x_2445_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinrel___boxed(lean_object* v_x_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_){
_start:
{
lean_object* v_res_2457_; 
v_res_2457_ = l_Lean_Elab_Term_Quotation_precheckBinrel(v_x_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_);
lean_dec(v_a_2455_);
lean_dec_ref(v_a_2454_);
lean_dec(v_a_2453_);
lean_dec_ref(v_a_2452_);
lean_dec(v_a_2451_);
lean_dec_ref(v_a_2450_);
lean_dec(v_a_2449_);
return v_res_2457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1(){
_start:
{
lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
v___x_2466_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
v___x_2467_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckBinrel___closed__1));
v___x_2468_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__1));
v___x_2469_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckBinrel___boxed), 9, 0);
v___x_2470_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2466_, v___x_2467_, v___x_2468_, v___x_2469_);
return v___x_2470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___boxed(lean_object* v_a_2471_){
_start:
{
lean_object* v_res_2472_; 
v_res_2472_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1();
return v_res_2472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinrelNoProp(lean_object* v_x_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_){
_start:
{
lean_object* v___x_2488_; uint8_t v___x_2489_; 
v___x_2488_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__1));
lean_inc(v_x_2479_);
v___x_2489_ = l_Lean_Syntax_isOfKind(v_x_2479_, v___x_2488_);
if (v___x_2489_ == 0)
{
lean_object* v___x_2490_; 
lean_dec(v_x_2479_);
v___x_2490_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
return v___x_2490_;
}
else
{
lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2491_ = lean_unsigned_to_nat(1u);
v___x_2492_ = l_Lean_Syntax_getArg(v_x_2479_, v___x_2491_);
v___x_2493_ = lean_unsigned_to_nat(2u);
v___x_2494_ = l_Lean_Syntax_getArg(v_x_2479_, v___x_2493_);
v___x_2495_ = lean_unsigned_to_nat(3u);
v___x_2496_ = l_Lean_Syntax_getArg(v_x_2479_, v___x_2495_);
lean_dec(v_x_2479_);
v___x_2497_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2492_, v_a_2480_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_, v_a_2486_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v___x_2498_; 
lean_dec_ref_known(v___x_2497_, 1);
v___x_2498_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2494_, v_a_2480_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_, v_a_2486_);
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_object* v___x_2499_; 
lean_dec_ref_known(v___x_2498_, 1);
v___x_2499_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2496_, v_a_2480_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_, v_a_2486_);
return v___x_2499_;
}
else
{
lean_dec(v___x_2496_);
return v___x_2498_;
}
}
else
{
lean_dec(v___x_2496_);
lean_dec(v___x_2494_);
return v___x_2497_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___boxed(lean_object* v_x_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_){
_start:
{
lean_object* v_res_2509_; 
v_res_2509_ = l_Lean_Elab_Term_Quotation_precheckBinrelNoProp(v_x_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_);
lean_dec(v_a_2507_);
lean_dec_ref(v_a_2506_);
lean_dec(v_a_2505_);
lean_dec_ref(v_a_2504_);
lean_dec(v_a_2503_);
lean_dec_ref(v_a_2502_);
lean_dec(v_a_2501_);
return v_res_2509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1(){
_start:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2518_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
v___x_2519_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__1));
v___x_2520_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__1));
v___x_2521_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___boxed), 9, 0);
v___x_2522_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2518_, v___x_2519_, v___x_2520_, v___x_2521_);
return v___x_2522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___boxed(lean_object* v_a_2523_){
_start:
{
lean_object* v_res_2524_; 
v_res_2524_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1();
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinop(lean_object* v_x_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_){
_start:
{
lean_object* v___x_2540_; uint8_t v___x_2541_; 
v___x_2540_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckBinop___closed__1));
lean_inc(v_x_2531_);
v___x_2541_ = l_Lean_Syntax_isOfKind(v_x_2531_, v___x_2540_);
if (v___x_2541_ == 0)
{
lean_object* v___x_2542_; 
lean_dec(v_x_2531_);
v___x_2542_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
return v___x_2542_;
}
else
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2543_ = lean_unsigned_to_nat(1u);
v___x_2544_ = l_Lean_Syntax_getArg(v_x_2531_, v___x_2543_);
v___x_2545_ = lean_unsigned_to_nat(2u);
v___x_2546_ = l_Lean_Syntax_getArg(v_x_2531_, v___x_2545_);
v___x_2547_ = lean_unsigned_to_nat(3u);
v___x_2548_ = l_Lean_Syntax_getArg(v_x_2531_, v___x_2547_);
lean_dec(v_x_2531_);
v___x_2549_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2544_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_);
if (lean_obj_tag(v___x_2549_) == 0)
{
lean_object* v___x_2550_; 
lean_dec_ref_known(v___x_2549_, 1);
v___x_2550_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2546_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_);
if (lean_obj_tag(v___x_2550_) == 0)
{
lean_object* v___x_2551_; 
lean_dec_ref_known(v___x_2550_, 1);
v___x_2551_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2548_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_);
return v___x_2551_;
}
else
{
lean_dec(v___x_2548_);
return v___x_2550_;
}
}
else
{
lean_dec(v___x_2548_);
lean_dec(v___x_2546_);
return v___x_2549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinop___boxed(lean_object* v_x_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_){
_start:
{
lean_object* v_res_2561_; 
v_res_2561_ = l_Lean_Elab_Term_Quotation_precheckBinop(v_x_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_);
lean_dec(v_a_2559_);
lean_dec_ref(v_a_2558_);
lean_dec(v_a_2557_);
lean_dec_ref(v_a_2556_);
lean_dec(v_a_2555_);
lean_dec_ref(v_a_2554_);
lean_dec(v_a_2553_);
return v_res_2561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1(){
_start:
{
lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2570_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
v___x_2571_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckBinop___closed__1));
v___x_2572_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__1));
v___x_2573_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckBinop___boxed), 9, 0);
v___x_2574_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2570_, v___x_2571_, v___x_2572_, v___x_2573_);
return v___x_2574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___boxed(lean_object* v_a_2575_){
_start:
{
lean_object* v_res_2576_; 
v_res_2576_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1();
return v_res_2576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinopLazy(lean_object* v_x_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_){
_start:
{
lean_object* v___x_2592_; uint8_t v___x_2593_; 
v___x_2592_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__1));
lean_inc(v_x_2583_);
v___x_2593_ = l_Lean_Syntax_isOfKind(v_x_2583_, v___x_2592_);
if (v___x_2593_ == 0)
{
lean_object* v___x_2594_; 
lean_dec(v_x_2583_);
v___x_2594_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
return v___x_2594_;
}
else
{
lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2595_ = lean_unsigned_to_nat(1u);
v___x_2596_ = l_Lean_Syntax_getArg(v_x_2583_, v___x_2595_);
v___x_2597_ = lean_unsigned_to_nat(2u);
v___x_2598_ = l_Lean_Syntax_getArg(v_x_2583_, v___x_2597_);
v___x_2599_ = lean_unsigned_to_nat(3u);
v___x_2600_ = l_Lean_Syntax_getArg(v_x_2583_, v___x_2599_);
lean_dec(v_x_2583_);
v___x_2601_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2596_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_object* v___x_2602_; 
lean_dec_ref_known(v___x_2601_, 1);
v___x_2602_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2598_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_);
if (lean_obj_tag(v___x_2602_) == 0)
{
lean_object* v___x_2603_; 
lean_dec_ref_known(v___x_2602_, 1);
v___x_2603_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2600_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_);
return v___x_2603_;
}
else
{
lean_dec(v___x_2600_);
return v___x_2602_;
}
}
else
{
lean_dec(v___x_2600_);
lean_dec(v___x_2598_);
return v___x_2601_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinopLazy___boxed(lean_object* v_x_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_){
_start:
{
lean_object* v_res_2613_; 
v_res_2613_ = l_Lean_Elab_Term_Quotation_precheckBinopLazy(v_x_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_, v_a_2611_);
lean_dec(v_a_2611_);
lean_dec_ref(v_a_2610_);
lean_dec(v_a_2609_);
lean_dec_ref(v_a_2608_);
lean_dec(v_a_2607_);
lean_dec_ref(v_a_2606_);
lean_dec(v_a_2605_);
return v_res_2613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1(){
_start:
{
lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2622_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
v___x_2623_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__1));
v___x_2624_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__1));
v___x_2625_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckBinopLazy___boxed), 9, 0);
v___x_2626_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2622_, v___x_2623_, v___x_2624_, v___x_2625_);
return v___x_2626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___boxed(lean_object* v_a_2627_){
_start:
{
lean_object* v_res_2628_; 
v_res_2628_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1();
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckLeftact(lean_object* v_x_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_){
_start:
{
lean_object* v___x_2644_; uint8_t v___x_2645_; 
v___x_2644_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckLeftact___closed__1));
lean_inc(v_x_2635_);
v___x_2645_ = l_Lean_Syntax_isOfKind(v_x_2635_, v___x_2644_);
if (v___x_2645_ == 0)
{
lean_object* v___x_2646_; 
lean_dec(v_x_2635_);
v___x_2646_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
return v___x_2646_;
}
else
{
lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; 
v___x_2647_ = lean_unsigned_to_nat(1u);
v___x_2648_ = l_Lean_Syntax_getArg(v_x_2635_, v___x_2647_);
v___x_2649_ = lean_unsigned_to_nat(2u);
v___x_2650_ = l_Lean_Syntax_getArg(v_x_2635_, v___x_2649_);
v___x_2651_ = lean_unsigned_to_nat(3u);
v___x_2652_ = l_Lean_Syntax_getArg(v_x_2635_, v___x_2651_);
lean_dec(v_x_2635_);
v___x_2653_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2648_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_);
if (lean_obj_tag(v___x_2653_) == 0)
{
lean_object* v___x_2654_; 
lean_dec_ref_known(v___x_2653_, 1);
v___x_2654_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2650_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_);
if (lean_obj_tag(v___x_2654_) == 0)
{
lean_object* v___x_2655_; 
lean_dec_ref_known(v___x_2654_, 1);
v___x_2655_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2652_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_);
return v___x_2655_;
}
else
{
lean_dec(v___x_2652_);
return v___x_2654_;
}
}
else
{
lean_dec(v___x_2652_);
lean_dec(v___x_2650_);
return v___x_2653_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckLeftact___boxed(lean_object* v_x_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_){
_start:
{
lean_object* v_res_2665_; 
v_res_2665_ = l_Lean_Elab_Term_Quotation_precheckLeftact(v_x_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_);
lean_dec(v_a_2663_);
lean_dec_ref(v_a_2662_);
lean_dec(v_a_2661_);
lean_dec_ref(v_a_2660_);
lean_dec(v_a_2659_);
lean_dec_ref(v_a_2658_);
lean_dec(v_a_2657_);
return v_res_2665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1(){
_start:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; 
v___x_2674_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
v___x_2675_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckLeftact___closed__1));
v___x_2676_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__1));
v___x_2677_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckLeftact___boxed), 9, 0);
v___x_2678_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2674_, v___x_2675_, v___x_2676_, v___x_2677_);
return v___x_2678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___boxed(lean_object* v_a_2679_){
_start:
{
lean_object* v_res_2680_; 
v_res_2680_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1();
return v_res_2680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckRightact(lean_object* v_x_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_){
_start:
{
lean_object* v___x_2696_; uint8_t v___x_2697_; 
v___x_2696_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckRightact___closed__1));
lean_inc(v_x_2687_);
v___x_2697_ = l_Lean_Syntax_isOfKind(v_x_2687_, v___x_2696_);
if (v___x_2697_ == 0)
{
lean_object* v___x_2698_; 
lean_dec(v_x_2687_);
v___x_2698_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
return v___x_2698_;
}
else
{
lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v___x_2699_ = lean_unsigned_to_nat(1u);
v___x_2700_ = l_Lean_Syntax_getArg(v_x_2687_, v___x_2699_);
v___x_2701_ = lean_unsigned_to_nat(2u);
v___x_2702_ = l_Lean_Syntax_getArg(v_x_2687_, v___x_2701_);
v___x_2703_ = lean_unsigned_to_nat(3u);
v___x_2704_ = l_Lean_Syntax_getArg(v_x_2687_, v___x_2703_);
lean_dec(v_x_2687_);
v___x_2705_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2700_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_);
if (lean_obj_tag(v___x_2705_) == 0)
{
lean_object* v___x_2706_; 
lean_dec_ref_known(v___x_2705_, 1);
v___x_2706_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2702_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_);
if (lean_obj_tag(v___x_2706_) == 0)
{
lean_object* v___x_2707_; 
lean_dec_ref_known(v___x_2706_, 1);
v___x_2707_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2704_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_);
return v___x_2707_;
}
else
{
lean_dec(v___x_2704_);
return v___x_2706_;
}
}
else
{
lean_dec(v___x_2704_);
lean_dec(v___x_2702_);
return v___x_2705_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckRightact___boxed(lean_object* v_x_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_){
_start:
{
lean_object* v_res_2717_; 
v_res_2717_ = l_Lean_Elab_Term_Quotation_precheckRightact(v_x_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_);
lean_dec(v_a_2715_);
lean_dec_ref(v_a_2714_);
lean_dec(v_a_2713_);
lean_dec_ref(v_a_2712_);
lean_dec(v_a_2711_);
lean_dec_ref(v_a_2710_);
lean_dec(v_a_2709_);
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1(){
_start:
{
lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
v___x_2726_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
v___x_2727_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckRightact___closed__1));
v___x_2728_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__1));
v___x_2729_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckRightact___boxed), 9, 0);
v___x_2730_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2726_, v___x_2727_, v___x_2728_, v___x_2729_);
return v___x_2730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___boxed(lean_object* v_a_2731_){
_start:
{
lean_object* v_res_2732_; 
v_res_2732_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1();
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckUnop(lean_object* v_x_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_){
_start:
{
lean_object* v___x_2748_; uint8_t v___x_2749_; 
v___x_2748_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckUnop___closed__1));
lean_inc(v_x_2739_);
v___x_2749_ = l_Lean_Syntax_isOfKind(v_x_2739_, v___x_2748_);
if (v___x_2749_ == 0)
{
lean_object* v___x_2750_; 
lean_dec(v_x_2739_);
v___x_2750_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
return v___x_2750_;
}
else
{
lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; 
v___x_2751_ = lean_unsigned_to_nat(1u);
v___x_2752_ = l_Lean_Syntax_getArg(v_x_2739_, v___x_2751_);
v___x_2753_ = lean_unsigned_to_nat(2u);
v___x_2754_ = l_Lean_Syntax_getArg(v_x_2739_, v___x_2753_);
lean_dec(v_x_2739_);
v___x_2755_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2752_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_);
if (lean_obj_tag(v___x_2755_) == 0)
{
lean_object* v___x_2756_; 
lean_dec_ref_known(v___x_2755_, 1);
v___x_2756_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2754_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_);
return v___x_2756_;
}
else
{
lean_dec(v___x_2754_);
return v___x_2755_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckUnop___boxed(lean_object* v_x_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_){
_start:
{
lean_object* v_res_2766_; 
v_res_2766_ = l_Lean_Elab_Term_Quotation_precheckUnop(v_x_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_);
lean_dec(v_a_2764_);
lean_dec_ref(v_a_2763_);
lean_dec(v_a_2762_);
lean_dec_ref(v_a_2761_);
lean_dec(v_a_2760_);
lean_dec_ref(v_a_2759_);
lean_dec(v_a_2758_);
return v_res_2766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1(){
_start:
{
lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; 
v___x_2775_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
v___x_2776_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckUnop___closed__1));
v___x_2777_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__1));
v___x_2778_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckUnop___boxed), 9, 0);
v___x_2779_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2775_, v___x_2776_, v___x_2777_, v___x_2778_);
return v___x_2779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___boxed(lean_object* v_a_2780_){
_start:
{
lean_object* v_res_2781_; 
v_res_2781_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1();
return v_res_2781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckHygieneInfo___redArg(){
_start:
{
lean_object* v___x_2783_; lean_object* v___x_2784_; 
v___x_2783_ = lean_box(0);
v___x_2784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2784_, 0, v___x_2783_);
return v___x_2784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckHygieneInfo___redArg___boxed(lean_object* v_a_2785_){
_start:
{
lean_object* v_res_2786_; 
v_res_2786_ = l_Lean_Elab_Term_Quotation_precheckHygieneInfo___redArg();
return v_res_2786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckHygieneInfo(lean_object* v_x_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_){
_start:
{
lean_object* v___x_2796_; 
v___x_2796_ = l_Lean_Elab_Term_Quotation_precheckHygieneInfo___redArg();
return v___x_2796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckHygieneInfo___boxed(lean_object* v_x_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_){
_start:
{
lean_object* v_res_2806_; 
v_res_2806_ = l_Lean_Elab_Term_Quotation_precheckHygieneInfo(v_x_2797_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_);
lean_dec(v_a_2804_);
lean_dec_ref(v_a_2803_);
lean_dec(v_a_2802_);
lean_dec_ref(v_a_2801_);
lean_dec(v_a_2800_);
lean_dec_ref(v_a_2799_);
lean_dec(v_a_2798_);
lean_dec(v_x_2797_);
return v_res_2806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1(){
_start:
{
lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; 
v___x_2820_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
v___x_2821_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__0));
v___x_2822_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__2));
v___x_2823_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckHygieneInfo___boxed), 9, 0);
v___x_2824_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2820_, v___x_2821_, v___x_2822_, v___x_2823_);
return v___x_2824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___boxed(lean_object* v_a_2825_){
_start:
{
lean_object* v_res_2826_; 
v_res_2826_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1();
return v_res_2826_;
}
}
lean_object* runtime_initialize_Lean_Elab_Quotation_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_DeprecatedSyntax_Basic(uint8_t builtin);
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
res = runtime_initialize_Lean_Elab_DeprecatedSyntax_Basic(builtin);
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
lean_object* initialize_Lean_Elab_DeprecatedSyntax_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Quotation_Precheck(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Quotation_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DeprecatedSyntax_Basic(builtin);
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
