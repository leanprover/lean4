// Lean compiler output
// Module: Lean.Elab.Quotation.Precheck
// Imports: public import Lean.Elab.Quotation.Util
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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Syntax_isAnyAntiquot(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Macro_expandMacro_x3f___boxed(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
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
lean_object* l_Lean_KeyedDeclsAttribute_evalIdentKey(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_init___redArg(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_getValues___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getQuotContent(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_Quotation_hygiene;
lean_object* l_Lean_Elab_Term_adaptExpander(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Elab_realizeGlobalNameWithInfos(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resolveName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesIdent(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "quotPrecheck"};
static const lean_object* l_Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(232, 232, 129, 207, 165, 21, 210, 151)}};
static const lean_object* l_Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 236, .m_capacity = 236, .m_length = 235, .m_data = "Enable eager name analysis on notations in order to find unbound identifiers early.\nNote that type-sensitive syntax (\"elaborators\") needs special support for this kind of check, so it might need to be turned off when using such syntax."};
static const lean_object* l_Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Quotation"};
static const lean_object* l_Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(14, 125, 73, 172, 99, 41, 123, 101)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value_aux_3),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(65, 56, 228, 97, 200, 215, 173, 209)}};
static const lean_object* l_Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_quotPrecheck;
static const lean_string_object l_Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "allowSectionVars"};
static const lean_object* l_Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(232, 232, 129, 207, 165, 21, 210, 151)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(88, 69, 101, 149, 23, 62, 51, 0)}};
static const lean_object* l_Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 106, .m_capacity = 106, .m_length = 105, .m_data = "Allow occurrences of section variables in checked quotations, it is useful when declaring local notation."};
static const lean_object* l_Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(14, 125, 73, 172, 99, 41, 123, 101)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value_aux_3),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(65, 56, 228, 97, 200, 215, 173, 209)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value_aux_4),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(37, 117, 254, 154, 34, 204, 1, 44)}};
static const lean_object* l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_quotPrecheck_allowSectionVars;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_initFn___lam__0_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_initFn___lam__0_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_initFn___lam__1_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_initFn___lam__1_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_Quotation_initFn___lam__0_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_Quotation_initFn___lam__1_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2____boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "builtin_quot_precheck"};
static const lean_object* l_Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(174, 247, 11, 123, 196, 4, 137, 247)}};
static const lean_object* l_Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "quot_precheck"};
static const lean_object* l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(136, 16, 194, 46, 122, 138, 84, 224)}};
static const lean_object* l_Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "Register a double backtick syntax quotation pre-check."};
static const lean_object* l_Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Precheck"};
static const lean_object* l_Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(14, 125, 73, 172, 99, 41, 123, 101)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_3),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(169, 189, 97, 153, 33, 221, 10, 105)}};
static const lean_object* l_Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_initFn___closed__9_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_Elab_Term_Quotation_initFn___closed__9_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__9_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Term_Quotation_initFn___closed__10_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "precheckAttribute"};
static const lean_object* l_Lean_Elab_Term_Quotation_initFn___closed__10_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__10_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_initFn___closed__11_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_initFn___closed__11_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__11_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_initFn___closed__11_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__11_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_initFn___closed__11_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__11_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(14, 125, 73, 172, 99, 41, 123, 101)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_initFn___closed__11_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__11_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_3),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__10_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(197, 91, 218, 200, 14, 173, 229, 62)}};
static const lean_object* l_Lean_Elab_Term_Quotation_initFn___closed__11_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__11_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute;
static const lean_string_object l_Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 522, .m_capacity = 522, .m_length = 521, .m_data = "Registers a double backtick syntax quotation pre-check.\n\n`@[quot_precheck k]` registers a declaration of type `Lean.Elab.Term.Quotation.Precheck` for the\nsyntax node kind `k`. It should implement eager name analysis on the passed syntax by throwing an\nexception on unbound identifiers, and calling `precheck` recursively on nested terms, potentially\nwith an extended local context (`withNewLocal`). Macros without registered precheck hook are\nunfolded, and identifier-less syntax is ultimately assumed to be well-formed.\n"};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_docString__1___closed__0 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_docString__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_docString__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(40) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(56) << 1) | 1)),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__1_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(26) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__3_value),((lean_object*)(((size_t)(26) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__4_value),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___closed__0 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___closed__0_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___closed__1 = (const lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___closed__1_value;
LEAN_EXPORT uint8_t l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__7___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__7___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__7___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__7_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__7_spec__12___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__7___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9_spec__13_spec__16___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9_spec__13_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9_spec__13___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9_spec__13___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9_spec__13___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9_spec__13___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9_spec__13___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__4;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__5;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__7_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__7_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__8_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__12;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__13;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__14_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__15;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__16_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__17;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__18_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__20_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__21 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__21_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__7_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__7_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9_spec__13(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9_spec__13_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9_spec__13_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__0 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__1 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "precheckIdent"};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__2 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(14, 125, 73, 172, 99, 41, 123, 101)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__3_value_aux_3),((lean_object*)&l_Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(130, 137, 165, 162, 174, 93, 212, 1)}};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__3 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___boxed(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "namedArgument"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__2_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(226, 89, 129, 113, 173, 121, 169, 188)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ellipsis"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(101, 52, 71, 179, 21, 116, 195, 217)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__4_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_Quotation_precheckApp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckApp___closed__0 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckApp___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckApp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckApp___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckApp___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckApp___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckApp___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckApp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckApp___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_Quotation_precheckApp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckApp___closed__1 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckApp___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "precheckApp"};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__0 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(14, 125, 73, 172, 99, 41, 123, 101)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(163, 232, 133, 146, 248, 6, 112, 147)}};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__1 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "typeAscription"};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__0 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 209, 88, 141, 5, 195, 49, 74)}};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__1 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__1_value;
static const lean_string_object l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__2 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__2_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__3 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckTypeAscription(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckTypeAscription___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "precheckTypeAscription"};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__0 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(14, 125, 73, 172, 99, 41, 123, 101)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 182, 167, 232, 99, 17, 44, 94)}};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__1 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Term_Quotation_precheckExplicit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "explicit"};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckExplicit___closed__0 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckExplicit___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckExplicit___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckExplicit___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckExplicit___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckExplicit___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckExplicit___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckExplicit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckExplicit___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_Quotation_precheckExplicit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(141, 201, 75, 195, 250, 223, 114, 184)}};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckExplicit___closed__1 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckExplicit___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckExplicit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckExplicit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "precheckExplicit"};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__0 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(14, 125, 73, 172, 99, 41, 123, 101)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(186, 174, 145, 115, 15, 112, 132, 151)}};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__1 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___boxed(lean_object*);
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
static const lean_string_object l_Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "choice"};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__0 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 66, 148, 42, 181, 100, 85, 166)}};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__1 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "precheckChoice"};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__2 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(14, 125, 73, 172, 99, 41, 123, 101)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__3_value_aux_3),((lean_object*)&l_Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(219, 120, 91, 227, 172, 108, 142, 184)}};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__3 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "precheckedQuot"};
static const lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__0 = (const lean_object*)&l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(110, 214, 3, 29, 194, 190, 3, 97)}};
static const lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__1 = (const lean_object*)&l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "elabPrecheckedQuot"};
static const lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__2 = (const lean_object*)&l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(14, 125, 73, 172, 99, 41, 123, 101)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3_value_aux_3),((lean_object*)&l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(60, 249, 149, 118, 59, 253, 255, 197)}};
static const lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3 = (const lean_object*)&l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(139) << 1) | 1)),((lean_object*)(((size_t)(36) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(142) << 1) | 1)),((lean_object*)(((size_t)(60) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__0_value),((lean_object*)(((size_t)(36) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__1_value),((lean_object*)(((size_t)(60) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(139) << 1) | 1)),((lean_object*)(((size_t)(40) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(139) << 1) | 1)),((lean_object*)(((size_t)(58) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__3_value),((lean_object*)(((size_t)(40) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__4_value),((lean_object*)(((size_t)(58) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Term_Quotation_precheckBinrel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "binrel"};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckBinrel___closed__0 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinrel___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinrel___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinrel___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinrel___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinrel___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinrel___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinrel___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinrel___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinrel___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 238, 75, 93, 70, 164, 233, 165)}};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckBinrel___closed__1 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinrel___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinrel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinrel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "precheckBinrel"};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__0 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(14, 125, 73, 172, 99, 41, 123, 101)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(83, 230, 82, 89, 81, 213, 228, 178)}};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__1 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "binrel_no_prop"};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__0 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 122, 90, 92, 171, 187, 176, 37)}};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__1 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinrelNoProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "precheckBinrelNoProp"};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__0 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(14, 125, 73, 172, 99, 41, 123, 101)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(225, 10, 254, 77, 93, 46, 3, 51)}};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__1 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Term_Quotation_precheckBinop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "binop"};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckBinop___closed__0 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinop___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinop___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinop___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinop___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinop___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinop___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinop___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinop___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinop___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 253, 231, 222, 243, 42, 73, 191)}};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckBinop___closed__1 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinop___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "precheckBinop"};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__0 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(14, 125, 73, 172, 99, 41, 123, 101)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(208, 17, 13, 13, 42, 64, 96, 27)}};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__1 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "binop_lazy"};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__0 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__0_value),LEAN_SCALAR_PTR_LITERAL(35, 222, 106, 2, 24, 145, 254, 163)}};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__1 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinopLazy(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinopLazy___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "precheckBinopLazy"};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__0 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(14, 125, 73, 172, 99, 41, 123, 101)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(220, 63, 127, 230, 166, 233, 146, 124)}};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__1 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Term_Quotation_precheckLeftact___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "leftact"};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckLeftact___closed__0 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckLeftact___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckLeftact___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckLeftact___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckLeftact___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckLeftact___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckLeftact___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckLeftact___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckLeftact___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_Quotation_precheckLeftact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(235, 190, 22, 58, 115, 190, 112, 107)}};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckLeftact___closed__1 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckLeftact___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckLeftact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckLeftact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "precheckLeftact"};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__0 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(14, 125, 73, 172, 99, 41, 123, 101)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 14, 84, 189, 210, 228, 161, 228)}};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__1 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Term_Quotation_precheckRightact___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "rightact"};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckRightact___closed__0 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckRightact___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckRightact___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckRightact___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckRightact___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckRightact___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckRightact___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckRightact___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckRightact___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_Quotation_precheckRightact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(147, 6, 66, 125, 81, 188, 156, 70)}};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckRightact___closed__1 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckRightact___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckRightact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckRightact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "precheckRightact"};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__0 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(14, 125, 73, 172, 99, 41, 123, 101)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(110, 63, 207, 226, 148, 187, 163, 109)}};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__1 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Term_Quotation_precheckUnop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "unop"};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckUnop___closed__0 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckUnop___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckUnop___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckUnop___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckUnop___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckUnop___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckUnop___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckUnop___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckUnop___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_Quotation_precheckUnop___closed__0_value),LEAN_SCALAR_PTR_LITERAL(68, 253, 109, 39, 185, 175, 169, 133)}};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckUnop___closed__1 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckUnop___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckUnop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckUnop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "precheckUnop"};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__0 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(14, 125, 73, 172, 99, 41, 123, 101)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 68, 33, 200, 202, 154, 57, 80)}};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__1 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckHygieneInfo___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckHygieneInfo___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckHygieneInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckHygieneInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__0_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__0_value_aux_1),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__0_value_aux_2),((lean_object*)&l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___closed__0_value),LEAN_SCALAR_PTR_LITERAL(11, 171, 53, 55, 110, 181, 251, 200)}};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__0 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "precheckHygieneInfo"};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__1 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(14, 125, 73, 172, 99, 41, 123, 101)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__2_value_aux_3),((lean_object*)&l_Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 51, 232, 44, 217, 70, 133, 185)}};
static const lean_object* l_Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__2 = (const lean_object*)&l_Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__spec__0(lean_object* v_name_124_, lean_object* v_decl_125_, lean_object* v_ref_126_){
_start:
{
lean_object* v_defValue_128_; lean_object* v_descr_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_156_; 
v_defValue_128_ = lean_ctor_get(v_decl_125_, 0);
v_descr_129_ = lean_ctor_get(v_decl_125_, 1);
v_isSharedCheck_156_ = !lean_is_exclusive(v_decl_125_);
if (v_isSharedCheck_156_ == 0)
{
v___x_131_ = v_decl_125_;
v_isShared_132_ = v_isSharedCheck_156_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_descr_129_);
lean_inc(v_defValue_128_);
lean_dec(v_decl_125_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_156_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v___x_133_; uint8_t v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_133_ = lean_alloc_ctor(1, 0, 1);
v___x_134_ = lean_unbox(v_defValue_128_);
lean_ctor_set_uint8(v___x_133_, 0, v___x_134_);
lean_inc(v_name_124_);
v___x_135_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_135_, 0, v_name_124_);
lean_ctor_set(v___x_135_, 1, v_ref_126_);
lean_ctor_set(v___x_135_, 2, v___x_133_);
lean_ctor_set(v___x_135_, 3, v_descr_129_);
lean_inc(v_name_124_);
v___x_136_ = lean_register_option(v_name_124_, v___x_135_);
if (lean_obj_tag(v___x_136_) == 0)
{
lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_146_; 
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_136_);
if (v_isSharedCheck_146_ == 0)
{
lean_object* v_unused_147_; 
v_unused_147_ = lean_ctor_get(v___x_136_, 0);
lean_dec(v_unused_147_);
v___x_138_ = v___x_136_;
v_isShared_139_ = v_isSharedCheck_146_;
goto v_resetjp_137_;
}
else
{
lean_dec(v___x_136_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_146_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_141_; 
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 1, v_defValue_128_);
lean_ctor_set(v___x_131_, 0, v_name_124_);
v___x_141_ = v___x_131_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_name_124_);
lean_ctor_set(v_reuseFailAlloc_145_, 1, v_defValue_128_);
v___x_141_ = v_reuseFailAlloc_145_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
lean_object* v___x_143_; 
if (v_isShared_139_ == 0)
{
lean_ctor_set(v___x_138_, 0, v___x_141_);
v___x_143_ = v___x_138_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v___x_141_);
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
else
{
lean_object* v_a_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_155_; 
lean_del_object(v___x_131_);
lean_dec(v_defValue_128_);
lean_dec(v_name_124_);
v_a_148_ = lean_ctor_get(v___x_136_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v___x_136_);
if (v_isSharedCheck_155_ == 0)
{
v___x_150_ = v___x_136_;
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_a_148_);
lean_dec(v___x_136_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_153_; 
if (v_isShared_151_ == 0)
{
v___x_153_ = v___x_150_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_a_148_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_157_, lean_object* v_decl_158_, lean_object* v_ref_159_, lean_object* v_a_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Lean_Option_register___at___00Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__spec__0(v_name_157_, v_decl_158_, v_ref_159_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_181_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_));
v___x_182_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_));
v___x_183_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_));
v___x_184_ = l_Lean_Option_register___at___00Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__spec__0(v___x_181_, v___x_182_, v___x_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4____boxed(lean_object* v_a_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_();
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_204_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4_));
v___x_205_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4_));
v___x_206_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4_));
v___x_207_ = l_Lean_Option_register___at___00Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__spec__0(v___x_204_, v___x_205_, v___x_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4____boxed(lean_object* v_a_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4_();
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_initFn___lam__0_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_(uint8_t v_builtin_210_, lean_object* v_stx_211_, lean_object* v___y_212_, lean_object* v___y_213_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l_Lean_KeyedDeclsAttribute_evalIdentKey(v_stx_211_, v___y_212_, v___y_213_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_initFn___lam__0_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2____boxed(lean_object* v_builtin_216_, lean_object* v_stx_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
uint8_t v_builtin_boxed_221_; lean_object* v_res_222_; 
v_builtin_boxed_221_ = lean_unbox(v_builtin_216_);
v_res_222_ = l_Lean_Elab_Term_Quotation_initFn___lam__0_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_(v_builtin_boxed_221_, v_stx_217_, v___y_218_, v___y_219_);
lean_dec(v___y_219_);
lean_dec_ref(v___y_218_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_initFn___lam__1_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_(uint8_t v_builtin_223_, lean_object* v_declName_224_, lean_object* v_key_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_229_ = lean_box(0);
v___x_230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_initFn___lam__1_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2____boxed(lean_object* v_builtin_231_, lean_object* v_declName_232_, lean_object* v_key_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_){
_start:
{
uint8_t v_builtin_boxed_237_; lean_object* v_res_238_; 
v_builtin_boxed_237_ = lean_unbox(v_builtin_231_);
v_res_238_ = l_Lean_Elab_Term_Quotation_initFn___lam__1_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_(v_builtin_boxed_237_, v_declName_232_, v_key_233_, v___y_234_, v___y_235_);
lean_dec(v___y_235_);
lean_dec_ref(v___y_234_);
lean_dec(v_key_233_);
lean_dec(v_declName_232_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_270_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_initFn___closed__9_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_));
v___x_271_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_initFn___closed__11_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_));
v___x_272_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_270_, v___x_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2____boxed(lean_object* v_a_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_();
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_docString__1(){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_277_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_initFn___closed__11_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_));
v___x_278_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_docString__1___closed__0));
v___x_279_ = l_Lean_addBuiltinDocString(v___x_277_, v___x_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_docString__1___boxed(lean_object* v_a_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_docString__1();
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3(){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_308_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_initFn___closed__11_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_));
v___x_309_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__6));
v___x_310_ = l_Lean_addBuiltinDeclarationRanges(v___x_308_, v___x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___boxed(lean_object* v_a_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3();
return v_res_312_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent(lean_object* v_x_316_){
_start:
{
if (lean_obj_tag(v_x_316_) == 3)
{
uint8_t v___x_317_; 
lean_dec_ref(v_x_316_);
v___x_317_ = 1;
return v___x_317_;
}
else
{
uint8_t v___x_318_; 
lean_inc(v_x_316_);
v___x_318_ = l_Lean_Syntax_isAnyAntiquot(v_x_316_);
if (v___x_318_ == 0)
{
lean_object* v___x_319_; uint8_t v___x_320_; 
v___x_319_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___closed__1));
lean_inc(v_x_316_);
v___x_320_ = l_Lean_Syntax_isOfKind(v_x_316_, v___x_319_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; uint8_t v___x_324_; 
v___x_321_ = l_Lean_Syntax_getArgs(v_x_316_);
lean_dec(v_x_316_);
v___x_322_ = lean_unsigned_to_nat(0u);
v___x_323_ = lean_array_get_size(v___x_321_);
v___x_324_ = lean_nat_dec_lt(v___x_322_, v___x_323_);
if (v___x_324_ == 0)
{
lean_dec_ref(v___x_321_);
return v___x_320_;
}
else
{
if (v___x_324_ == 0)
{
lean_dec_ref(v___x_321_);
return v___x_320_;
}
else
{
size_t v___x_325_; size_t v___x_326_; uint8_t v___x_327_; 
v___x_325_ = ((size_t)0ULL);
v___x_326_ = lean_usize_of_nat(v___x_323_);
v___x_327_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent_spec__0(v___x_321_, v___x_325_, v___x_326_);
lean_dec_ref(v___x_321_);
return v___x_327_;
}
}
}
else
{
lean_dec(v_x_316_);
return v___x_318_;
}
}
else
{
uint8_t v___x_328_; 
lean_dec(v_x_316_);
v___x_328_ = 0;
return v___x_328_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent_spec__0(lean_object* v_as_329_, size_t v_i_330_, size_t v_stop_331_){
_start:
{
uint8_t v___x_332_; 
v___x_332_ = lean_usize_dec_eq(v_i_330_, v_stop_331_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_333_ = lean_array_uget_borrowed(v_as_329_, v_i_330_);
lean_inc(v___x_333_);
v___x_334_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent(v___x_333_);
if (v___x_334_ == 0)
{
size_t v___x_335_; size_t v___x_336_; 
v___x_335_ = ((size_t)1ULL);
v___x_336_ = lean_usize_add(v_i_330_, v___x_335_);
v_i_330_ = v___x_336_;
goto _start;
}
else
{
return v___x_334_;
}
}
else
{
uint8_t v___x_338_; 
v___x_338_ = 0;
return v___x_338_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent_spec__0___boxed(lean_object* v_as_339_, lean_object* v_i_340_, lean_object* v_stop_341_){
_start:
{
size_t v_i_boxed_342_; size_t v_stop_boxed_343_; uint8_t v_res_344_; lean_object* v_r_345_; 
v_i_boxed_342_ = lean_unbox_usize(v_i_340_);
lean_dec(v_i_340_);
v_stop_boxed_343_ = lean_unbox_usize(v_stop_341_);
lean_dec(v_stop_341_);
v_res_344_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent_spec__0(v_as_339_, v_i_boxed_342_, v_stop_boxed_343_);
lean_dec_ref(v_as_339_);
v_r_345_ = lean_box(v_res_344_);
return v_r_345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___boxed(lean_object* v_x_346_){
_start:
{
uint8_t v_res_347_; lean_object* v_r_348_; 
v_res_347_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent(v_x_346_);
v_r_348_ = lean_box(v_res_347_);
return v_r_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__3(lean_object* v_currNamespace_349_, lean_object* v___y_350_, lean_object* v___y_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_352_, 0, v_currNamespace_349_);
lean_ctor_set(v___x_352_, 1, v___y_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__3___boxed(lean_object* v_currNamespace_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__3(v_currNamespace_353_, v___y_354_, v___y_355_);
lean_dec_ref(v___y_354_);
return v_res_356_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_357_ = lean_box(0);
v___x_358_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
lean_ctor_set(v___x_359_, 1, v___x_357_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__7___redArg(){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__7___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__7___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__7___redArg___closed__0);
v___x_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_362_, 0, v___x_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__7___redArg___boxed(lean_object* v___y_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__7___redArg();
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__2(lean_object* v_env_365_, lean_object* v_currNamespace_366_, lean_object* v_openDecls_367_, lean_object* v_n_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = l_Lean_ResolveName_resolveNamespace(v_env_365_, v_currNamespace_366_, v_openDecls_367_, v_n_368_);
v___x_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
lean_ctor_set(v___x_372_, 1, v___y_370_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__2___boxed(lean_object* v_env_373_, lean_object* v_currNamespace_374_, lean_object* v_openDecls_375_, lean_object* v_n_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__2(v_env_373_, v_currNamespace_374_, v_openDecls_375_, v_n_376_, v___y_377_, v___y_378_);
lean_dec_ref(v___y_377_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__1(lean_object* v_env_380_, lean_object* v_declName_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
uint8_t v___x_384_; lean_object* v_env_385_; lean_object* v___x_386_; uint8_t v___x_387_; uint8_t v___x_388_; 
v___x_384_ = 0;
v_env_385_ = l_Lean_Environment_setExporting(v_env_380_, v___x_384_);
lean_inc(v_declName_381_);
v___x_386_ = l_Lean_mkPrivateName(v_env_385_, v_declName_381_);
v___x_387_ = 1;
lean_inc_ref(v_env_385_);
v___x_388_ = l_Lean_Environment_contains(v_env_385_, v___x_386_, v___x_387_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; uint8_t v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_389_ = l_Lean_privateToUserName(v_declName_381_);
v___x_390_ = l_Lean_Environment_contains(v_env_385_, v___x_389_, v___x_387_);
v___x_391_ = lean_box(v___x_390_);
v___x_392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
lean_ctor_set(v___x_392_, 1, v___y_383_);
return v___x_392_;
}
else
{
lean_object* v___x_393_; lean_object* v___x_394_; 
lean_dec_ref(v_env_385_);
lean_dec(v_declName_381_);
v___x_393_ = lean_box(v___x_388_);
v___x_394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
lean_ctor_set(v___x_394_, 1, v___y_383_);
return v___x_394_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__1___boxed(lean_object* v_env_395_, lean_object* v_declName_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__1(v_env_395_, v_declName_396_, v___y_397_, v___y_398_);
lean_dec_ref(v___y_397_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___redArg(lean_object* v_x_400_, lean_object* v___y_401_){
_start:
{
if (lean_obj_tag(v_x_400_) == 0)
{
lean_object* v_a_402_; lean_object* v___x_403_; 
v_a_402_ = lean_ctor_get(v_x_400_, 0);
lean_inc(v_a_402_);
v___x_403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_403_, 0, v_a_402_);
lean_ctor_set(v___x_403_, 1, v___y_401_);
return v___x_403_;
}
else
{
lean_object* v_a_404_; lean_object* v___x_405_; 
v_a_404_ = lean_ctor_get(v_x_400_, 0);
lean_inc(v_a_404_);
v___x_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_405_, 0, v_a_404_);
lean_ctor_set(v___x_405_, 1, v___y_401_);
return v___x_405_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___redArg___boxed(lean_object* v_x_406_, lean_object* v___y_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___redArg(v_x_406_, v___y_407_);
lean_dec_ref(v_x_406_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__0(lean_object* v_env_409_, lean_object* v_stx_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_409_, v_stx_410_, v___y_411_, v___y_412_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_object* v_a_414_; 
v_a_414_ = lean_ctor_get(v___x_413_, 0);
lean_inc(v_a_414_);
if (lean_obj_tag(v_a_414_) == 0)
{
lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_423_; 
v_a_415_ = lean_ctor_get(v___x_413_, 1);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_423_ == 0)
{
lean_object* v_unused_424_; 
v_unused_424_ = lean_ctor_get(v___x_413_, 0);
lean_dec(v_unused_424_);
v___x_417_ = v___x_413_;
v_isShared_418_ = v_isSharedCheck_423_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v___x_413_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_423_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_419_; lean_object* v___x_421_; 
v___x_419_ = lean_box(0);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 0, v___x_419_);
v___x_421_ = v___x_417_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_419_);
lean_ctor_set(v_reuseFailAlloc_422_, 1, v_a_415_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
else
{
lean_object* v_val_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_453_; 
v_val_425_ = lean_ctor_get(v_a_414_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v_a_414_);
if (v_isSharedCheck_453_ == 0)
{
v___x_427_ = v_a_414_;
v_isShared_428_ = v_isSharedCheck_453_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_val_425_);
lean_dec(v_a_414_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_453_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v_snd_429_; 
v_snd_429_ = lean_ctor_get(v_val_425_, 1);
lean_inc(v_snd_429_);
lean_dec(v_val_425_);
if (lean_obj_tag(v_snd_429_) == 0)
{
lean_object* v_a_430_; lean_object* v_a_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_439_; 
lean_del_object(v___x_427_);
v_a_430_ = lean_ctor_get(v___x_413_, 1);
lean_inc(v_a_430_);
lean_dec_ref(v___x_413_);
v_a_431_ = lean_ctor_get(v_snd_429_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v_snd_429_);
if (v_isSharedCheck_439_ == 0)
{
v___x_433_ = v_snd_429_;
v_isShared_434_ = v_isSharedCheck_439_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_a_431_);
lean_dec(v_snd_429_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_439_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_436_; 
if (v_isShared_434_ == 0)
{
v___x_436_ = v___x_433_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_a_431_);
v___x_436_ = v_reuseFailAlloc_438_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
lean_object* v___x_437_; 
v___x_437_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___redArg(v___x_436_, v_a_430_);
lean_dec_ref(v___x_436_);
return v___x_437_;
}
}
}
else
{
lean_object* v_a_440_; lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_452_; 
v_a_440_ = lean_ctor_get(v___x_413_, 1);
lean_inc(v_a_440_);
lean_dec_ref(v___x_413_);
v_a_441_ = lean_ctor_get(v_snd_429_, 0);
v_isSharedCheck_452_ = !lean_is_exclusive(v_snd_429_);
if (v_isSharedCheck_452_ == 0)
{
v___x_443_ = v_snd_429_;
v_isShared_444_ = v_isSharedCheck_452_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v_snd_429_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_452_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_446_; 
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 0, v_a_441_);
v___x_446_ = v___x_427_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_a_441_);
v___x_446_ = v_reuseFailAlloc_451_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
lean_object* v___x_448_; 
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 0, v___x_446_);
v___x_448_ = v___x_443_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v___x_446_);
v___x_448_ = v_reuseFailAlloc_450_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
lean_object* v___x_449_; 
v___x_449_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___redArg(v___x_448_, v_a_440_);
lean_dec_ref(v___x_448_);
return v___x_449_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_454_; lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_462_; 
v_a_454_ = lean_ctor_get(v___x_413_, 0);
v_a_455_ = lean_ctor_get(v___x_413_, 1);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_462_ == 0)
{
v___x_457_ = v___x_413_;
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_inc(v_a_454_);
lean_dec(v___x_413_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_460_; 
if (v_isShared_458_ == 0)
{
v___x_460_ = v___x_457_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_a_454_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v_a_455_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__0___boxed(lean_object* v_env_463_, lean_object* v_stx_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__0(v_env_463_, v_stx_464_, v___y_465_, v___y_466_);
lean_dec_ref(v___y_465_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__4(lean_object* v_env_468_, lean_object* v_options_469_, lean_object* v_currNamespace_470_, lean_object* v_openDecls_471_, lean_object* v_n_472_, lean_object* v___y_473_, lean_object* v___y_474_){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = l_Lean_ResolveName_resolveGlobalName(v_env_468_, v_options_469_, v_currNamespace_470_, v_openDecls_471_, v_n_472_);
v___x_476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
lean_ctor_set(v___x_476_, 1, v___y_474_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__4___boxed(lean_object* v_env_477_, lean_object* v_options_478_, lean_object* v_currNamespace_479_, lean_object* v_openDecls_480_, lean_object* v_n_481_, lean_object* v___y_482_, lean_object* v___y_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__4(v_env_477_, v_options_478_, v_currNamespace_479_, v_openDecls_480_, v_n_481_, v___y_482_, v___y_483_);
lean_dec_ref(v___y_482_);
lean_dec_ref(v_options_478_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1_spec__2(lean_object* v_msgData_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v___x_491_; lean_object* v_env_492_; lean_object* v___x_493_; lean_object* v_mctx_494_; lean_object* v_lctx_495_; lean_object* v_options_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_491_ = lean_st_ref_get(v___y_489_);
v_env_492_ = lean_ctor_get(v___x_491_, 0);
lean_inc_ref(v_env_492_);
lean_dec(v___x_491_);
v___x_493_ = lean_st_ref_get(v___y_487_);
v_mctx_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc_ref(v_mctx_494_);
lean_dec(v___x_493_);
v_lctx_495_ = lean_ctor_get(v___y_486_, 2);
v_options_496_ = lean_ctor_get(v___y_488_, 2);
lean_inc_ref(v_options_496_);
lean_inc_ref(v_lctx_495_);
v___x_497_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_497_, 0, v_env_492_);
lean_ctor_set(v___x_497_, 1, v_mctx_494_);
lean_ctor_set(v___x_497_, 2, v_lctx_495_);
lean_ctor_set(v___x_497_, 3, v_options_496_);
v___x_498_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
lean_ctor_set(v___x_498_, 1, v_msgData_485_);
v___x_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1_spec__2(v_msgData_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
return v_res_506_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_507_; double v___x_508_; 
v___x_507_ = lean_unsigned_to_nat(0u);
v___x_508_ = lean_float_of_nat(v___x_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___redArg(lean_object* v_cls_512_, lean_object* v_msg_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
lean_object* v_ref_519_; lean_object* v___x_520_; lean_object* v_a_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_565_; 
v_ref_519_ = lean_ctor_get(v___y_516_, 5);
v___x_520_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1_spec__2(v_msg_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
v_a_521_ = lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_565_ == 0)
{
v___x_523_ = v___x_520_;
v_isShared_524_ = v_isSharedCheck_565_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_a_521_);
lean_dec(v___x_520_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_565_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_525_; lean_object* v_traceState_526_; lean_object* v_env_527_; lean_object* v_nextMacroScope_528_; lean_object* v_ngen_529_; lean_object* v_auxDeclNGen_530_; lean_object* v_cache_531_; lean_object* v_messages_532_; lean_object* v_infoState_533_; lean_object* v_snapshotTasks_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_564_; 
v___x_525_ = lean_st_ref_take(v___y_517_);
v_traceState_526_ = lean_ctor_get(v___x_525_, 4);
v_env_527_ = lean_ctor_get(v___x_525_, 0);
v_nextMacroScope_528_ = lean_ctor_get(v___x_525_, 1);
v_ngen_529_ = lean_ctor_get(v___x_525_, 2);
v_auxDeclNGen_530_ = lean_ctor_get(v___x_525_, 3);
v_cache_531_ = lean_ctor_get(v___x_525_, 5);
v_messages_532_ = lean_ctor_get(v___x_525_, 6);
v_infoState_533_ = lean_ctor_get(v___x_525_, 7);
v_snapshotTasks_534_ = lean_ctor_get(v___x_525_, 8);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_564_ == 0)
{
v___x_536_ = v___x_525_;
v_isShared_537_ = v_isSharedCheck_564_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_snapshotTasks_534_);
lean_inc(v_infoState_533_);
lean_inc(v_messages_532_);
lean_inc(v_cache_531_);
lean_inc(v_traceState_526_);
lean_inc(v_auxDeclNGen_530_);
lean_inc(v_ngen_529_);
lean_inc(v_nextMacroScope_528_);
lean_inc(v_env_527_);
lean_dec(v___x_525_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_564_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
uint64_t v_tid_538_; lean_object* v_traces_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_563_; 
v_tid_538_ = lean_ctor_get_uint64(v_traceState_526_, sizeof(void*)*1);
v_traces_539_ = lean_ctor_get(v_traceState_526_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v_traceState_526_);
if (v_isSharedCheck_563_ == 0)
{
v___x_541_ = v_traceState_526_;
v_isShared_542_ = v_isSharedCheck_563_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_traces_539_);
lean_dec(v_traceState_526_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_563_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_543_; double v___x_544_; uint8_t v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_553_; 
v___x_543_ = lean_box(0);
v___x_544_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___redArg___closed__0);
v___x_545_ = 0;
v___x_546_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___redArg___closed__1));
v___x_547_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_547_, 0, v_cls_512_);
lean_ctor_set(v___x_547_, 1, v___x_543_);
lean_ctor_set(v___x_547_, 2, v___x_546_);
lean_ctor_set_float(v___x_547_, sizeof(void*)*3, v___x_544_);
lean_ctor_set_float(v___x_547_, sizeof(void*)*3 + 8, v___x_544_);
lean_ctor_set_uint8(v___x_547_, sizeof(void*)*3 + 16, v___x_545_);
v___x_548_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___redArg___closed__2));
v___x_549_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_549_, 0, v___x_547_);
lean_ctor_set(v___x_549_, 1, v_a_521_);
lean_ctor_set(v___x_549_, 2, v___x_548_);
lean_inc(v_ref_519_);
v___x_550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_550_, 0, v_ref_519_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
v___x_551_ = l_Lean_PersistentArray_push___redArg(v_traces_539_, v___x_550_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 0, v___x_551_);
v___x_553_ = v___x_541_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_551_);
lean_ctor_set_uint64(v_reuseFailAlloc_562_, sizeof(void*)*1, v_tid_538_);
v___x_553_ = v_reuseFailAlloc_562_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
lean_object* v___x_555_; 
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 4, v___x_553_);
v___x_555_ = v___x_536_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_env_527_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_nextMacroScope_528_);
lean_ctor_set(v_reuseFailAlloc_561_, 2, v_ngen_529_);
lean_ctor_set(v_reuseFailAlloc_561_, 3, v_auxDeclNGen_530_);
lean_ctor_set(v_reuseFailAlloc_561_, 4, v___x_553_);
lean_ctor_set(v_reuseFailAlloc_561_, 5, v_cache_531_);
lean_ctor_set(v_reuseFailAlloc_561_, 6, v_messages_532_);
lean_ctor_set(v_reuseFailAlloc_561_, 7, v_infoState_533_);
lean_ctor_set(v_reuseFailAlloc_561_, 8, v_snapshotTasks_534_);
v___x_555_ = v_reuseFailAlloc_561_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_559_; 
v___x_556_ = lean_st_ref_set(v___y_517_, v___x_555_);
v___x_557_ = lean_box(0);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 0, v___x_557_);
v___x_559_ = v___x_523_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_557_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___redArg___boxed(lean_object* v_cls_566_, lean_object* v_msg_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___redArg(v_cls_566_, v_msg_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg(lean_object* v_cls_577_, lean_object* v___y_578_){
_start:
{
lean_object* v_options_580_; uint8_t v_hasTrace_581_; 
v_options_580_ = lean_ctor_get(v___y_578_, 2);
v_hasTrace_581_ = lean_ctor_get_uint8(v_options_580_, sizeof(void*)*1);
if (v_hasTrace_581_ == 0)
{
lean_object* v___x_582_; lean_object* v___x_583_; 
lean_dec(v_cls_577_);
v___x_582_ = lean_box(v_hasTrace_581_);
v___x_583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
return v___x_583_;
}
else
{
lean_object* v_inheritedTraceOptions_584_; lean_object* v___x_585_; lean_object* v___x_586_; uint8_t v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v_inheritedTraceOptions_584_ = lean_ctor_get(v___y_578_, 13);
v___x_585_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___closed__1));
v___x_586_ = l_Lean_Name_append(v___x_585_, v_cls_577_);
v___x_587_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_584_, v_options_580_, v___x_586_);
lean_dec(v___x_586_);
v___x_588_ = lean_box(v___x_587_);
v___x_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_589_, 0, v___x_588_);
return v___x_589_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___boxed(lean_object* v_cls_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg(v_cls_590_, v___y_591_);
lean_dec_ref(v___y_591_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5(lean_object* v_as_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
if (lean_obj_tag(v_as_594_) == 0)
{
lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_603_ = lean_box(0);
v___x_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
return v___x_604_;
}
else
{
lean_object* v_head_605_; lean_object* v_tail_606_; lean_object* v_fst_607_; lean_object* v_snd_608_; lean_object* v___x_609_; lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_622_; 
v_head_605_ = lean_ctor_get(v_as_594_, 0);
lean_inc(v_head_605_);
v_tail_606_ = lean_ctor_get(v_as_594_, 1);
lean_inc(v_tail_606_);
lean_dec_ref(v_as_594_);
v_fst_607_ = lean_ctor_get(v_head_605_, 0);
lean_inc(v_fst_607_);
v_snd_608_ = lean_ctor_get(v_head_605_, 1);
lean_inc(v_snd_608_);
lean_dec(v_head_605_);
lean_inc(v_fst_607_);
v___x_609_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg(v_fst_607_, v___y_600_);
v_a_610_ = lean_ctor_get(v___x_609_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_622_ == 0)
{
v___x_612_ = v___x_609_;
v_isShared_613_ = v_isSharedCheck_622_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_609_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_622_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
uint8_t v___x_614_; 
v___x_614_ = lean_unbox(v_a_610_);
lean_dec(v_a_610_);
if (v___x_614_ == 0)
{
lean_del_object(v___x_612_);
lean_dec(v_snd_608_);
lean_dec(v_fst_607_);
v_as_594_ = v_tail_606_;
goto _start;
}
else
{
lean_object* v___x_617_; 
if (v_isShared_613_ == 0)
{
lean_ctor_set_tag(v___x_612_, 3);
lean_ctor_set(v___x_612_, 0, v_snd_608_);
v___x_617_ = v___x_612_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_snd_608_);
v___x_617_ = v_reuseFailAlloc_621_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_618_ = l_Lean_MessageData_ofFormat(v___x_617_);
v___x_619_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___redArg(v_fst_607_, v___x_618_, v___y_598_, v___y_599_, v___y_600_, v___y_601_);
if (lean_obj_tag(v___x_619_) == 0)
{
lean_dec_ref(v___x_619_);
v_as_594_ = v_tail_606_;
goto _start;
}
else
{
lean_dec(v_tail_606_);
return v___x_619_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___boxed(lean_object* v_as_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5(v_as_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
return v_res_632_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = l_Lean_maxRecDepthErrorMessage;
v___x_639_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
return v___x_639_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__3);
v___x_641_ = l_Lean_MessageData_ofFormat(v___x_640_);
return v___x_641_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_642_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__4);
v___x_643_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__2));
v___x_644_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
lean_ctor_set(v___x_644_, 1, v___x_642_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg(lean_object* v_ref_645_){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_647_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__5);
v___x_648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_648_, 0, v_ref_645_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
v___x_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___boxed(lean_object* v_ref_650_, lean_object* v___y_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg(v_ref_650_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__7_spec__12___redArg(lean_object* v_a_653_, lean_object* v_x_654_){
_start:
{
if (lean_obj_tag(v_x_654_) == 0)
{
lean_object* v___x_655_; 
v___x_655_ = lean_box(0);
return v___x_655_;
}
else
{
lean_object* v_key_656_; lean_object* v_value_657_; lean_object* v_tail_658_; uint8_t v___x_659_; 
v_key_656_ = lean_ctor_get(v_x_654_, 0);
v_value_657_ = lean_ctor_get(v_x_654_, 1);
v_tail_658_ = lean_ctor_get(v_x_654_, 2);
v___x_659_ = lean_name_eq(v_key_656_, v_a_653_);
if (v___x_659_ == 0)
{
v_x_654_ = v_tail_658_;
goto _start;
}
else
{
lean_object* v___x_661_; 
lean_inc(v_value_657_);
v___x_661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_661_, 0, v_value_657_);
return v___x_661_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__7_spec__12___redArg___boxed(lean_object* v_a_662_, lean_object* v_x_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__7_spec__12___redArg(v_a_662_, v_x_663_);
lean_dec(v_x_663_);
lean_dec(v_a_662_);
return v_res_664_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_665_; uint64_t v___x_666_; 
v___x_665_ = lean_unsigned_to_nat(1723u);
v___x_666_ = lean_uint64_of_nat(v___x_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__7___redArg(lean_object* v_m_667_, lean_object* v_a_668_){
_start:
{
lean_object* v_buckets_669_; lean_object* v___x_670_; uint64_t v___y_672_; 
v_buckets_669_ = lean_ctor_get(v_m_667_, 1);
v___x_670_ = lean_array_get_size(v_buckets_669_);
if (lean_obj_tag(v_a_668_) == 0)
{
uint64_t v___x_686_; 
v___x_686_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__7___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__7___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__7___redArg___closed__0);
v___y_672_ = v___x_686_;
goto v___jp_671_;
}
else
{
uint64_t v_hash_687_; 
v_hash_687_ = lean_ctor_get_uint64(v_a_668_, sizeof(void*)*2);
v___y_672_ = v_hash_687_;
goto v___jp_671_;
}
v___jp_671_:
{
uint64_t v___x_673_; uint64_t v___x_674_; uint64_t v_fold_675_; uint64_t v___x_676_; uint64_t v___x_677_; uint64_t v___x_678_; size_t v___x_679_; size_t v___x_680_; size_t v___x_681_; size_t v___x_682_; size_t v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_673_ = 32ULL;
v___x_674_ = lean_uint64_shift_right(v___y_672_, v___x_673_);
v_fold_675_ = lean_uint64_xor(v___y_672_, v___x_674_);
v___x_676_ = 16ULL;
v___x_677_ = lean_uint64_shift_right(v_fold_675_, v___x_676_);
v___x_678_ = lean_uint64_xor(v_fold_675_, v___x_677_);
v___x_679_ = lean_uint64_to_usize(v___x_678_);
v___x_680_ = lean_usize_of_nat(v___x_670_);
v___x_681_ = ((size_t)1ULL);
v___x_682_ = lean_usize_sub(v___x_680_, v___x_681_);
v___x_683_ = lean_usize_land(v___x_679_, v___x_682_);
v___x_684_ = lean_array_uget_borrowed(v_buckets_669_, v___x_683_);
v___x_685_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__7_spec__12___redArg(v_a_668_, v___x_684_);
return v___x_685_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__7___redArg___boxed(lean_object* v_m_688_, lean_object* v_a_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__7___redArg(v_m_688_, v_a_689_);
lean_dec(v_a_689_);
lean_dec_ref(v_m_688_);
return v_res_690_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9_spec__13_spec__16___redArg(lean_object* v_keys_691_, lean_object* v_i_692_, lean_object* v_k_693_){
_start:
{
lean_object* v___x_694_; uint8_t v___x_695_; 
v___x_694_ = lean_array_get_size(v_keys_691_);
v___x_695_ = lean_nat_dec_lt(v_i_692_, v___x_694_);
if (v___x_695_ == 0)
{
lean_dec(v_i_692_);
return v___x_695_;
}
else
{
lean_object* v_k_x27_696_; uint8_t v___x_697_; 
v_k_x27_696_ = lean_array_fget_borrowed(v_keys_691_, v_i_692_);
v___x_697_ = l_Lean_instBEqExtraModUse_beq(v_k_693_, v_k_x27_696_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = lean_unsigned_to_nat(1u);
v___x_699_ = lean_nat_add(v_i_692_, v___x_698_);
lean_dec(v_i_692_);
v_i_692_ = v___x_699_;
goto _start;
}
else
{
lean_dec(v_i_692_);
return v___x_697_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9_spec__13_spec__16___redArg___boxed(lean_object* v_keys_701_, lean_object* v_i_702_, lean_object* v_k_703_){
_start:
{
uint8_t v_res_704_; lean_object* v_r_705_; 
v_res_704_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9_spec__13_spec__16___redArg(v_keys_701_, v_i_702_, v_k_703_);
lean_dec_ref(v_k_703_);
lean_dec_ref(v_keys_701_);
v_r_705_ = lean_box(v_res_704_);
return v_r_705_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9_spec__13___redArg___closed__0(void){
_start:
{
size_t v___x_706_; size_t v___x_707_; size_t v___x_708_; 
v___x_706_ = ((size_t)5ULL);
v___x_707_ = ((size_t)1ULL);
v___x_708_ = lean_usize_shift_left(v___x_707_, v___x_706_);
return v___x_708_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9_spec__13___redArg___closed__1(void){
_start:
{
size_t v___x_709_; size_t v___x_710_; size_t v___x_711_; 
v___x_709_ = ((size_t)1ULL);
v___x_710_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9_spec__13___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9_spec__13___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9_spec__13___redArg___closed__0);
v___x_711_ = lean_usize_sub(v___x_710_, v___x_709_);
return v___x_711_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9_spec__13___redArg(lean_object* v_x_712_, size_t v_x_713_, lean_object* v_x_714_){
_start:
{
if (lean_obj_tag(v_x_712_) == 0)
{
lean_object* v_es_715_; lean_object* v___x_716_; size_t v___x_717_; size_t v___x_718_; size_t v___x_719_; lean_object* v_j_720_; lean_object* v___x_721_; 
v_es_715_ = lean_ctor_get(v_x_712_, 0);
lean_inc_ref(v_es_715_);
lean_dec_ref(v_x_712_);
v___x_716_ = lean_box(2);
v___x_717_ = ((size_t)5ULL);
v___x_718_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9_spec__13___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9_spec__13___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9_spec__13___redArg___closed__1);
v___x_719_ = lean_usize_land(v_x_713_, v___x_718_);
v_j_720_ = lean_usize_to_nat(v___x_719_);
v___x_721_ = lean_array_get(v___x_716_, v_es_715_, v_j_720_);
lean_dec(v_j_720_);
lean_dec_ref(v_es_715_);
switch(lean_obj_tag(v___x_721_))
{
case 0:
{
lean_object* v_key_722_; uint8_t v___x_723_; 
v_key_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc(v_key_722_);
lean_dec_ref(v___x_721_);
v___x_723_ = l_Lean_instBEqExtraModUse_beq(v_x_714_, v_key_722_);
lean_dec(v_key_722_);
return v___x_723_;
}
case 1:
{
lean_object* v_node_724_; size_t v___x_725_; 
v_node_724_ = lean_ctor_get(v___x_721_, 0);
lean_inc(v_node_724_);
lean_dec_ref(v___x_721_);
v___x_725_ = lean_usize_shift_right(v_x_713_, v___x_717_);
v_x_712_ = v_node_724_;
v_x_713_ = v___x_725_;
goto _start;
}
default: 
{
uint8_t v___x_727_; 
v___x_727_ = 0;
return v___x_727_;
}
}
}
else
{
lean_object* v_ks_728_; lean_object* v___x_729_; uint8_t v___x_730_; 
v_ks_728_ = lean_ctor_get(v_x_712_, 0);
lean_inc_ref(v_ks_728_);
lean_dec_ref(v_x_712_);
v___x_729_ = lean_unsigned_to_nat(0u);
v___x_730_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9_spec__13_spec__16___redArg(v_ks_728_, v___x_729_, v_x_714_);
lean_dec_ref(v_ks_728_);
return v___x_730_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9_spec__13___redArg___boxed(lean_object* v_x_731_, lean_object* v_x_732_, lean_object* v_x_733_){
_start:
{
size_t v_x_27714__boxed_734_; uint8_t v_res_735_; lean_object* v_r_736_; 
v_x_27714__boxed_734_ = lean_unbox_usize(v_x_732_);
lean_dec(v_x_732_);
v_res_735_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9_spec__13___redArg(v_x_731_, v_x_27714__boxed_734_, v_x_733_);
lean_dec_ref(v_x_733_);
v_r_736_ = lean_box(v_res_735_);
return v_r_736_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9___redArg(lean_object* v_x_737_, lean_object* v_x_738_){
_start:
{
uint64_t v___x_739_; size_t v___x_740_; uint8_t v___x_741_; 
v___x_739_ = l_Lean_instHashableExtraModUse_hash(v_x_738_);
v___x_740_ = lean_uint64_to_usize(v___x_739_);
v___x_741_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9_spec__13___redArg(v_x_737_, v___x_740_, v_x_738_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_x_742_, lean_object* v_x_743_){
_start:
{
uint8_t v_res_744_; lean_object* v_r_745_; 
v_res_744_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9___redArg(v_x_742_, v_x_743_);
lean_dec_ref(v_x_743_);
v_r_745_ = lean_box(v_res_744_);
return v_r_745_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__2(void){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_748_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__1));
v___x_749_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__0));
v___x_750_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_749_, v___x_748_);
return v___x_750_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__3(void){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_751_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__4(void){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__3);
v___x_753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
return v___x_753_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__5(void){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__4);
v___x_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
lean_ctor_set(v___x_755_, 1, v___x_754_);
return v___x_755_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__6(void){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__4);
v___x_757_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
lean_ctor_set(v___x_757_, 2, v___x_756_);
lean_ctor_set(v___x_757_, 3, v___x_756_);
lean_ctor_set(v___x_757_, 4, v___x_756_);
lean_ctor_set(v___x_757_, 5, v___x_756_);
return v___x_757_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__10(void){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__9));
v___x_763_ = l_Lean_stringToMessageData(v___x_762_);
return v___x_763_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__12(void){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_765_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__11));
v___x_766_ = l_Lean_stringToMessageData(v___x_765_);
return v___x_766_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__13(void){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___redArg___closed__1));
v___x_768_ = l_Lean_stringToMessageData(v___x_767_);
return v___x_768_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__15(void){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_770_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__14));
v___x_771_ = l_Lean_stringToMessageData(v___x_770_);
return v___x_771_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__17(void){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__16));
v___x_774_ = l_Lean_stringToMessageData(v___x_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5(lean_object* v_mod_779_, uint8_t v_isMeta_780_, lean_object* v_hint_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v___x_790_; lean_object* v_env_791_; uint8_t v_isExporting_792_; lean_object* v___x_793_; lean_object* v_env_794_; lean_object* v___x_795_; lean_object* v_entry_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___x_842_; uint8_t v___x_843_; 
v___x_790_ = lean_st_ref_get(v___y_788_);
v_env_791_ = lean_ctor_get(v___x_790_, 0);
lean_inc_ref(v_env_791_);
lean_dec(v___x_790_);
v_isExporting_792_ = lean_ctor_get_uint8(v_env_791_, sizeof(void*)*8);
lean_dec_ref(v_env_791_);
v___x_793_ = lean_st_ref_get(v___y_788_);
v_env_794_ = lean_ctor_get(v___x_793_, 0);
lean_inc_ref(v_env_794_);
lean_dec(v___x_793_);
v___x_795_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__2);
lean_inc(v_mod_779_);
v_entry_796_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_796_, 0, v_mod_779_);
lean_ctor_set_uint8(v_entry_796_, sizeof(void*)*1, v_isExporting_792_);
lean_ctor_set_uint8(v_entry_796_, sizeof(void*)*1 + 1, v_isMeta_780_);
v___x_797_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_798_ = lean_box(1);
v___x_799_ = lean_box(0);
v___x_842_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_795_, v___x_797_, v_env_794_, v___x_798_, v___x_799_);
v___x_843_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9___redArg(v___x_842_, v_entry_796_);
if (v___x_843_ == 0)
{
lean_object* v_cls_844_; lean_object* v___x_845_; lean_object* v_a_846_; lean_object* v___y_848_; lean_object* v___y_849_; lean_object* v___y_853_; lean_object* v___y_854_; uint8_t v___x_866_; 
v_cls_844_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__8));
v___x_845_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg(v_cls_844_, v___y_787_);
v_a_846_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_a_846_);
lean_dec_ref(v___x_845_);
v___x_866_ = lean_unbox(v_a_846_);
lean_dec(v_a_846_);
if (v___x_866_ == 0)
{
lean_dec(v_hint_781_);
lean_dec(v_mod_779_);
v___y_801_ = v___y_786_;
v___y_802_ = v___y_788_;
goto v___jp_800_;
}
else
{
lean_object* v___x_867_; lean_object* v___y_869_; 
v___x_867_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__15, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__15_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__15);
if (v_isExporting_792_ == 0)
{
lean_object* v___x_876_; 
v___x_876_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__20));
v___y_869_ = v___x_876_;
goto v___jp_868_;
}
else
{
lean_object* v___x_877_; 
v___x_877_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__21));
v___y_869_ = v___x_877_;
goto v___jp_868_;
}
v___jp_868_:
{
lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_870_ = l_Lean_stringToMessageData(v___y_869_);
v___x_871_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_867_);
lean_ctor_set(v___x_871_, 1, v___x_870_);
v___x_872_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__17, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__17_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__17);
v___x_873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_871_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
if (v_isMeta_780_ == 0)
{
lean_object* v___x_874_; 
v___x_874_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__18));
v___y_853_ = v___x_873_;
v___y_854_ = v___x_874_;
goto v___jp_852_;
}
else
{
lean_object* v___x_875_; 
v___x_875_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__19));
v___y_853_ = v___x_873_;
v___y_854_ = v___x_875_;
goto v___jp_852_;
}
}
}
v___jp_847_:
{
lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_850_, 0, v___y_848_);
lean_ctor_set(v___x_850_, 1, v___y_849_);
v___x_851_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___redArg(v_cls_844_, v___x_850_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_dec_ref(v___x_851_);
v___y_801_ = v___y_786_;
v___y_802_ = v___y_788_;
goto v___jp_800_;
}
else
{
lean_dec_ref(v_entry_796_);
return v___x_851_;
}
}
v___jp_852_:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; uint8_t v___x_861_; 
v___x_855_ = l_Lean_stringToMessageData(v___y_854_);
v___x_856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_856_, 0, v___y_853_);
lean_ctor_set(v___x_856_, 1, v___x_855_);
v___x_857_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__10);
v___x_858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_856_);
lean_ctor_set(v___x_858_, 1, v___x_857_);
v___x_859_ = l_Lean_MessageData_ofName(v_mod_779_);
v___x_860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_860_, 0, v___x_858_);
lean_ctor_set(v___x_860_, 1, v___x_859_);
v___x_861_ = l_Lean_Name_isAnonymous(v_hint_781_);
if (v___x_861_ == 0)
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_862_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__12);
v___x_863_ = l_Lean_MessageData_ofName(v_hint_781_);
v___x_864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_862_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
v___y_848_ = v___x_860_;
v___y_849_ = v___x_864_;
goto v___jp_847_;
}
else
{
lean_object* v___x_865_; 
lean_dec(v_hint_781_);
v___x_865_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__13);
v___y_848_ = v___x_860_;
v___y_849_ = v___x_865_;
goto v___jp_847_;
}
}
}
else
{
lean_object* v___x_878_; lean_object* v___x_879_; 
lean_dec_ref(v_entry_796_);
lean_dec(v_hint_781_);
lean_dec(v_mod_779_);
v___x_878_ = lean_box(0);
v___x_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_879_, 0, v___x_878_);
return v___x_879_;
}
v___jp_800_:
{
lean_object* v___x_803_; lean_object* v_toEnvExtension_804_; lean_object* v_env_805_; lean_object* v_nextMacroScope_806_; lean_object* v_ngen_807_; lean_object* v_auxDeclNGen_808_; lean_object* v_traceState_809_; lean_object* v_messages_810_; lean_object* v_infoState_811_; lean_object* v_snapshotTasks_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_840_; 
v___x_803_ = lean_st_ref_take(v___y_802_);
v_toEnvExtension_804_ = lean_ctor_get(v___x_797_, 0);
lean_inc_ref(v_toEnvExtension_804_);
v_env_805_ = lean_ctor_get(v___x_803_, 0);
v_nextMacroScope_806_ = lean_ctor_get(v___x_803_, 1);
v_ngen_807_ = lean_ctor_get(v___x_803_, 2);
v_auxDeclNGen_808_ = lean_ctor_get(v___x_803_, 3);
v_traceState_809_ = lean_ctor_get(v___x_803_, 4);
v_messages_810_ = lean_ctor_get(v___x_803_, 6);
v_infoState_811_ = lean_ctor_get(v___x_803_, 7);
v_snapshotTasks_812_ = lean_ctor_get(v___x_803_, 8);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_840_ == 0)
{
lean_object* v_unused_841_; 
v_unused_841_ = lean_ctor_get(v___x_803_, 5);
lean_dec(v_unused_841_);
v___x_814_ = v___x_803_;
v_isShared_815_ = v_isSharedCheck_840_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_snapshotTasks_812_);
lean_inc(v_infoState_811_);
lean_inc(v_messages_810_);
lean_inc(v_traceState_809_);
lean_inc(v_auxDeclNGen_808_);
lean_inc(v_ngen_807_);
lean_inc(v_nextMacroScope_806_);
lean_inc(v_env_805_);
lean_dec(v___x_803_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_840_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v_asyncMode_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_820_; 
v_asyncMode_816_ = lean_ctor_get(v_toEnvExtension_804_, 2);
lean_inc(v_asyncMode_816_);
lean_dec_ref(v_toEnvExtension_804_);
v___x_817_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_797_, v_env_805_, v_entry_796_, v_asyncMode_816_, v___x_799_);
lean_dec(v_asyncMode_816_);
v___x_818_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__5);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 5, v___x_818_);
lean_ctor_set(v___x_814_, 0, v___x_817_);
v___x_820_ = v___x_814_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_817_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v_nextMacroScope_806_);
lean_ctor_set(v_reuseFailAlloc_839_, 2, v_ngen_807_);
lean_ctor_set(v_reuseFailAlloc_839_, 3, v_auxDeclNGen_808_);
lean_ctor_set(v_reuseFailAlloc_839_, 4, v_traceState_809_);
lean_ctor_set(v_reuseFailAlloc_839_, 5, v___x_818_);
lean_ctor_set(v_reuseFailAlloc_839_, 6, v_messages_810_);
lean_ctor_set(v_reuseFailAlloc_839_, 7, v_infoState_811_);
lean_ctor_set(v_reuseFailAlloc_839_, 8, v_snapshotTasks_812_);
v___x_820_ = v_reuseFailAlloc_839_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v_mctx_823_; lean_object* v_zetaDeltaFVarIds_824_; lean_object* v_postponed_825_; lean_object* v_diag_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_837_; 
v___x_821_ = lean_st_ref_set(v___y_802_, v___x_820_);
v___x_822_ = lean_st_ref_take(v___y_801_);
v_mctx_823_ = lean_ctor_get(v___x_822_, 0);
v_zetaDeltaFVarIds_824_ = lean_ctor_get(v___x_822_, 2);
v_postponed_825_ = lean_ctor_get(v___x_822_, 3);
v_diag_826_ = lean_ctor_get(v___x_822_, 4);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_837_ == 0)
{
lean_object* v_unused_838_; 
v_unused_838_ = lean_ctor_get(v___x_822_, 1);
lean_dec(v_unused_838_);
v___x_828_ = v___x_822_;
v_isShared_829_ = v_isSharedCheck_837_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_diag_826_);
lean_inc(v_postponed_825_);
lean_inc(v_zetaDeltaFVarIds_824_);
lean_inc(v_mctx_823_);
lean_dec(v___x_822_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_837_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_830_; lean_object* v___x_832_; 
v___x_830_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___closed__6);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 1, v___x_830_);
v___x_832_ = v___x_828_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_mctx_823_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v___x_830_);
lean_ctor_set(v_reuseFailAlloc_836_, 2, v_zetaDeltaFVarIds_824_);
lean_ctor_set(v_reuseFailAlloc_836_, 3, v_postponed_825_);
lean_ctor_set(v_reuseFailAlloc_836_, 4, v_diag_826_);
v___x_832_ = v_reuseFailAlloc_836_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_833_ = lean_st_ref_set(v___y_801_, v___x_832_);
v___x_834_ = lean_box(0);
v___x_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
return v___x_835_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5___boxed(lean_object* v_mod_880_, lean_object* v_isMeta_881_, lean_object* v_hint_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
uint8_t v_isMeta_boxed_891_; lean_object* v_res_892_; 
v_isMeta_boxed_891_ = lean_unbox(v_isMeta_881_);
v_res_892_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5(v_mod_880_, v_isMeta_boxed_891_, v_hint_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
lean_dec(v___y_883_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__6(lean_object* v___x_893_, lean_object* v_declName_894_, lean_object* v_as_895_, size_t v_sz_896_, size_t v_i_897_, lean_object* v_b_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
uint8_t v___x_907_; 
v___x_907_ = lean_usize_dec_lt(v_i_897_, v_sz_896_);
if (v___x_907_ == 0)
{
lean_object* v___x_908_; 
lean_dec(v_declName_894_);
v___x_908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_908_, 0, v_b_898_);
return v___x_908_;
}
else
{
lean_object* v___x_909_; lean_object* v_modules_910_; lean_object* v___x_911_; lean_object* v_a_912_; lean_object* v___x_913_; lean_object* v_toImport_914_; lean_object* v_module_915_; uint8_t v___x_916_; lean_object* v___x_917_; 
v___x_909_ = l_Lean_Environment_header(v___x_893_);
v_modules_910_ = lean_ctor_get(v___x_909_, 3);
lean_inc_ref(v_modules_910_);
lean_dec_ref(v___x_909_);
v___x_911_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_912_ = lean_array_uget_borrowed(v_as_895_, v_i_897_);
v___x_913_ = lean_array_get(v___x_911_, v_modules_910_, v_a_912_);
lean_dec_ref(v_modules_910_);
v_toImport_914_ = lean_ctor_get(v___x_913_, 0);
lean_inc_ref(v_toImport_914_);
lean_dec(v___x_913_);
v_module_915_ = lean_ctor_get(v_toImport_914_, 0);
lean_inc(v_module_915_);
lean_dec_ref(v_toImport_914_);
v___x_916_ = 0;
lean_inc(v_declName_894_);
v___x_917_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5(v_module_915_, v___x_916_, v_declName_894_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v___x_918_; size_t v___x_919_; size_t v___x_920_; 
lean_dec_ref(v___x_917_);
v___x_918_ = lean_box(0);
v___x_919_ = ((size_t)1ULL);
v___x_920_ = lean_usize_add(v_i_897_, v___x_919_);
v_i_897_ = v___x_920_;
v_b_898_ = v___x_918_;
goto _start;
}
else
{
lean_dec(v_declName_894_);
return v___x_917_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__6___boxed(lean_object* v___x_922_, lean_object* v_declName_923_, lean_object* v_as_924_, lean_object* v_sz_925_, lean_object* v_i_926_, lean_object* v_b_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
size_t v_sz_boxed_936_; size_t v_i_boxed_937_; lean_object* v_res_938_; 
v_sz_boxed_936_ = lean_unbox_usize(v_sz_925_);
lean_dec(v_sz_925_);
v_i_boxed_937_ = lean_unbox_usize(v_i_926_);
lean_dec(v_i_926_);
v_res_938_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__6(v___x_922_, v_declName_923_, v_as_924_, v_sz_boxed_936_, v_i_boxed_937_, v_b_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec(v___y_928_);
lean_dec_ref(v_as_924_);
lean_dec_ref(v___x_922_);
return v_res_938_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3___closed__2(void){
_start:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_941_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3___closed__1));
v___x_942_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3___closed__0));
v___x_943_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_942_, v___x_941_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3(lean_object* v_declName_946_, uint8_t v_isMeta_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_){
_start:
{
lean_object* v___x_956_; lean_object* v_env_960_; lean_object* v___y_962_; lean_object* v___x_975_; 
v___x_956_ = lean_st_ref_get(v___y_954_);
v_env_960_ = lean_ctor_get(v___x_956_, 0);
lean_inc_ref(v_env_960_);
lean_dec(v___x_956_);
v___x_975_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_960_, v_declName_946_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_dec_ref(v_env_960_);
lean_dec(v_declName_946_);
goto v___jp_957_;
}
else
{
lean_object* v_val_976_; lean_object* v___x_977_; lean_object* v_modules_978_; lean_object* v___x_979_; uint8_t v___x_980_; 
v_val_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_val_976_);
lean_dec_ref(v___x_975_);
v___x_977_ = l_Lean_Environment_header(v_env_960_);
v_modules_978_ = lean_ctor_get(v___x_977_, 3);
lean_inc_ref(v_modules_978_);
lean_dec_ref(v___x_977_);
v___x_979_ = lean_array_get_size(v_modules_978_);
v___x_980_ = lean_nat_dec_lt(v_val_976_, v___x_979_);
if (v___x_980_ == 0)
{
lean_dec_ref(v_modules_978_);
lean_dec(v_val_976_);
lean_dec_ref(v_env_960_);
lean_dec(v_declName_946_);
goto v___jp_957_;
}
else
{
lean_object* v___x_981_; lean_object* v_env_982_; lean_object* v___x_983_; lean_object* v___x_984_; uint8_t v___y_986_; 
v___x_981_ = lean_st_ref_get(v___y_954_);
v_env_982_ = lean_ctor_get(v___x_981_, 0);
lean_inc_ref(v_env_982_);
lean_dec(v___x_981_);
v___x_983_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3___closed__2);
v___x_984_ = lean_array_fget(v_modules_978_, v_val_976_);
lean_dec(v_val_976_);
lean_dec_ref(v_modules_978_);
if (v_isMeta_947_ == 0)
{
lean_dec_ref(v_env_982_);
v___y_986_ = v_isMeta_947_;
goto v___jp_985_;
}
else
{
uint8_t v___x_997_; 
lean_inc(v_declName_946_);
v___x_997_ = l_Lean_isMarkedMeta(v_env_982_, v_declName_946_);
if (v___x_997_ == 0)
{
v___y_986_ = v_isMeta_947_;
goto v___jp_985_;
}
else
{
uint8_t v___x_998_; 
v___x_998_ = 0;
v___y_986_ = v___x_998_;
goto v___jp_985_;
}
}
v___jp_985_:
{
lean_object* v_toImport_987_; lean_object* v_module_988_; lean_object* v___x_989_; 
v_toImport_987_ = lean_ctor_get(v___x_984_, 0);
lean_inc_ref(v_toImport_987_);
lean_dec(v___x_984_);
v_module_988_ = lean_ctor_get(v_toImport_987_, 0);
lean_inc(v_module_988_);
lean_dec_ref(v_toImport_987_);
lean_inc(v_declName_946_);
v___x_989_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5(v_module_988_, v___y_986_, v_declName_946_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
lean_dec_ref(v___x_989_);
v___x_990_ = l_Lean_indirectModUseExt;
v___x_991_ = lean_box(1);
v___x_992_ = lean_box(0);
lean_inc_ref(v_env_960_);
v___x_993_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_983_, v___x_990_, v_env_960_, v___x_991_, v___x_992_);
v___x_994_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__7___redArg(v___x_993_, v_declName_946_);
lean_dec(v___x_993_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v___x_995_; 
v___x_995_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3___closed__3));
v___y_962_ = v___x_995_;
goto v___jp_961_;
}
else
{
lean_object* v_val_996_; 
v_val_996_ = lean_ctor_get(v___x_994_, 0);
lean_inc(v_val_996_);
lean_dec_ref(v___x_994_);
v___y_962_ = v_val_996_;
goto v___jp_961_;
}
}
else
{
lean_dec_ref(v_env_960_);
lean_dec(v_declName_946_);
return v___x_989_;
}
}
}
}
v___jp_957_:
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = lean_box(0);
v___x_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
return v___x_959_;
}
v___jp_961_:
{
lean_object* v___x_963_; size_t v_sz_964_; size_t v___x_965_; lean_object* v___x_966_; 
v___x_963_ = lean_box(0);
v_sz_964_ = lean_array_size(v___y_962_);
v___x_965_ = ((size_t)0ULL);
v___x_966_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__6(v_env_960_, v_declName_946_, v___y_962_, v_sz_964_, v___x_965_, v___x_963_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
lean_dec_ref(v___y_962_);
lean_dec_ref(v_env_960_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_973_; 
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_973_ == 0)
{
lean_object* v_unused_974_; 
v_unused_974_ = lean_ctor_get(v___x_966_, 0);
lean_dec(v_unused_974_);
v___x_968_ = v___x_966_;
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
else
{
lean_dec(v___x_966_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 0, v___x_963_);
v___x_971_ = v___x_968_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_963_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
else
{
return v___x_966_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3___boxed(lean_object* v_declName_999_, lean_object* v_isMeta_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
uint8_t v_isMeta_boxed_1009_; lean_object* v_res_1010_; 
v_isMeta_boxed_1009_ = lean_unbox(v_isMeta_1000_);
v_res_1010_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3(v_declName_999_, v_isMeta_boxed_1009_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_dec(v___y_1001_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4___redArg(lean_object* v_as_x27_1011_, lean_object* v_b_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
if (lean_obj_tag(v_as_x27_1011_) == 0)
{
lean_object* v___x_1021_; 
v___x_1021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1021_, 0, v_b_1012_);
return v___x_1021_;
}
else
{
lean_object* v_head_1022_; lean_object* v_tail_1023_; uint8_t v___x_1024_; lean_object* v___x_1025_; 
v_head_1022_ = lean_ctor_get(v_as_x27_1011_, 0);
lean_inc(v_head_1022_);
v_tail_1023_ = lean_ctor_get(v_as_x27_1011_, 1);
lean_inc(v_tail_1023_);
lean_dec_ref(v_as_x27_1011_);
v___x_1024_ = 1;
v___x_1025_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3(v_head_1022_, v___x_1024_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v___x_1026_; 
lean_dec_ref(v___x_1025_);
v___x_1026_ = lean_box(0);
v_as_x27_1011_ = v_tail_1023_;
v_b_1012_ = v___x_1026_;
goto _start;
}
else
{
lean_dec(v_tail_1023_);
return v___x_1025_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4___redArg___boxed(lean_object* v_as_x27_1028_, lean_object* v_b_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4___redArg(v_as_x27_1028_, v_b_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1_spec__9___redArg(lean_object* v_msg_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v_ref_1045_; lean_object* v___x_1046_; lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1055_; 
v_ref_1045_ = lean_ctor_get(v___y_1042_, 5);
v___x_1046_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1_spec__2(v_msg_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
v_a_1047_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1049_ = v___x_1046_;
v_isShared_1050_ = v_isSharedCheck_1055_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1046_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1055_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1051_; lean_object* v___x_1053_; 
lean_inc(v_ref_1045_);
v___x_1051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1051_, 0, v_ref_1045_);
lean_ctor_set(v___x_1051_, 1, v_a_1047_);
if (v_isShared_1050_ == 0)
{
lean_ctor_set_tag(v___x_1049_, 1);
lean_ctor_set(v___x_1049_, 0, v___x_1051_);
v___x_1053_ = v___x_1049_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v___x_1051_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1_spec__9___redArg___boxed(lean_object* v_msg_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1_spec__9___redArg(v_msg_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1___redArg(lean_object* v_ref_1063_, lean_object* v_msg_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v_fileName_1073_; lean_object* v_fileMap_1074_; lean_object* v_options_1075_; lean_object* v_currRecDepth_1076_; lean_object* v_maxRecDepth_1077_; lean_object* v_ref_1078_; lean_object* v_currNamespace_1079_; lean_object* v_openDecls_1080_; lean_object* v_initHeartbeats_1081_; lean_object* v_maxHeartbeats_1082_; lean_object* v_quotContext_1083_; lean_object* v_currMacroScope_1084_; uint8_t v_diag_1085_; lean_object* v_cancelTk_x3f_1086_; uint8_t v_suppressElabErrors_1087_; lean_object* v_inheritedTraceOptions_1088_; lean_object* v_ref_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v_fileName_1073_ = lean_ctor_get(v___y_1070_, 0);
v_fileMap_1074_ = lean_ctor_get(v___y_1070_, 1);
v_options_1075_ = lean_ctor_get(v___y_1070_, 2);
v_currRecDepth_1076_ = lean_ctor_get(v___y_1070_, 3);
v_maxRecDepth_1077_ = lean_ctor_get(v___y_1070_, 4);
v_ref_1078_ = lean_ctor_get(v___y_1070_, 5);
v_currNamespace_1079_ = lean_ctor_get(v___y_1070_, 6);
v_openDecls_1080_ = lean_ctor_get(v___y_1070_, 7);
v_initHeartbeats_1081_ = lean_ctor_get(v___y_1070_, 8);
v_maxHeartbeats_1082_ = lean_ctor_get(v___y_1070_, 9);
v_quotContext_1083_ = lean_ctor_get(v___y_1070_, 10);
v_currMacroScope_1084_ = lean_ctor_get(v___y_1070_, 11);
v_diag_1085_ = lean_ctor_get_uint8(v___y_1070_, sizeof(void*)*14);
v_cancelTk_x3f_1086_ = lean_ctor_get(v___y_1070_, 12);
v_suppressElabErrors_1087_ = lean_ctor_get_uint8(v___y_1070_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1088_ = lean_ctor_get(v___y_1070_, 13);
v_ref_1089_ = l_Lean_replaceRef(v_ref_1063_, v_ref_1078_);
lean_inc_ref(v_inheritedTraceOptions_1088_);
lean_inc(v_cancelTk_x3f_1086_);
lean_inc(v_currMacroScope_1084_);
lean_inc(v_quotContext_1083_);
lean_inc(v_maxHeartbeats_1082_);
lean_inc(v_initHeartbeats_1081_);
lean_inc(v_openDecls_1080_);
lean_inc(v_currNamespace_1079_);
lean_inc(v_maxRecDepth_1077_);
lean_inc(v_currRecDepth_1076_);
lean_inc_ref(v_options_1075_);
lean_inc_ref(v_fileMap_1074_);
lean_inc_ref(v_fileName_1073_);
v___x_1090_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1090_, 0, v_fileName_1073_);
lean_ctor_set(v___x_1090_, 1, v_fileMap_1074_);
lean_ctor_set(v___x_1090_, 2, v_options_1075_);
lean_ctor_set(v___x_1090_, 3, v_currRecDepth_1076_);
lean_ctor_set(v___x_1090_, 4, v_maxRecDepth_1077_);
lean_ctor_set(v___x_1090_, 5, v_ref_1089_);
lean_ctor_set(v___x_1090_, 6, v_currNamespace_1079_);
lean_ctor_set(v___x_1090_, 7, v_openDecls_1080_);
lean_ctor_set(v___x_1090_, 8, v_initHeartbeats_1081_);
lean_ctor_set(v___x_1090_, 9, v_maxHeartbeats_1082_);
lean_ctor_set(v___x_1090_, 10, v_quotContext_1083_);
lean_ctor_set(v___x_1090_, 11, v_currMacroScope_1084_);
lean_ctor_set(v___x_1090_, 12, v_cancelTk_x3f_1086_);
lean_ctor_set(v___x_1090_, 13, v_inheritedTraceOptions_1088_);
lean_ctor_set_uint8(v___x_1090_, sizeof(void*)*14, v_diag_1085_);
lean_ctor_set_uint8(v___x_1090_, sizeof(void*)*14 + 1, v_suppressElabErrors_1087_);
v___x_1091_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1_spec__9___redArg(v_msg_1064_, v___y_1068_, v___y_1069_, v___x_1090_, v___y_1071_);
lean_dec_ref(v___x_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1___redArg___boxed(lean_object* v_ref_1092_, lean_object* v_msg_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1___redArg(v_ref_1092_, v_msg_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec(v___y_1094_);
lean_dec(v_ref_1092_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg(lean_object* v_x_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
lean_object* v___x_1113_; lean_object* v_env_1114_; lean_object* v_options_1115_; lean_object* v_currRecDepth_1116_; lean_object* v_maxRecDepth_1117_; lean_object* v_ref_1118_; lean_object* v_currNamespace_1119_; lean_object* v_openDecls_1120_; lean_object* v_quotContext_1121_; lean_object* v_currMacroScope_1122_; lean_object* v___x_1123_; lean_object* v_nextMacroScope_1124_; lean_object* v___f_1125_; lean_object* v___f_1126_; lean_object* v___f_1127_; lean_object* v___f_1128_; lean_object* v___f_1129_; lean_object* v_methods_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1113_ = lean_st_ref_get(v___y_1111_);
v_env_1114_ = lean_ctor_get(v___x_1113_, 0);
lean_inc_ref(v_env_1114_);
lean_dec(v___x_1113_);
v_options_1115_ = lean_ctor_get(v___y_1110_, 2);
v_currRecDepth_1116_ = lean_ctor_get(v___y_1110_, 3);
v_maxRecDepth_1117_ = lean_ctor_get(v___y_1110_, 4);
v_ref_1118_ = lean_ctor_get(v___y_1110_, 5);
v_currNamespace_1119_ = lean_ctor_get(v___y_1110_, 6);
v_openDecls_1120_ = lean_ctor_get(v___y_1110_, 7);
v_quotContext_1121_ = lean_ctor_get(v___y_1110_, 10);
v_currMacroScope_1122_ = lean_ctor_get(v___y_1110_, 11);
v___x_1123_ = lean_st_ref_get(v___y_1111_);
v_nextMacroScope_1124_ = lean_ctor_get(v___x_1123_, 1);
lean_inc(v_nextMacroScope_1124_);
lean_dec(v___x_1123_);
lean_inc_ref(v_env_1114_);
v___f_1125_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1125_, 0, v_env_1114_);
lean_inc_ref(v_env_1114_);
v___f_1126_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1126_, 0, v_env_1114_);
lean_inc(v_openDecls_1120_);
lean_inc(v_currNamespace_1119_);
lean_inc_ref(v_env_1114_);
v___f_1127_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_1127_, 0, v_env_1114_);
lean_closure_set(v___f_1127_, 1, v_currNamespace_1119_);
lean_closure_set(v___f_1127_, 2, v_openDecls_1120_);
lean_inc(v_currNamespace_1119_);
v___f_1128_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1128_, 0, v_currNamespace_1119_);
lean_inc(v_openDecls_1120_);
lean_inc(v_currNamespace_1119_);
lean_inc_ref(v_options_1115_);
v___f_1129_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_1129_, 0, v_env_1114_);
lean_closure_set(v___f_1129_, 1, v_options_1115_);
lean_closure_set(v___f_1129_, 2, v_currNamespace_1119_);
lean_closure_set(v___f_1129_, 3, v_openDecls_1120_);
v_methods_1130_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1130_, 0, v___f_1125_);
lean_ctor_set(v_methods_1130_, 1, v___f_1128_);
lean_ctor_set(v_methods_1130_, 2, v___f_1126_);
lean_ctor_set(v_methods_1130_, 3, v___f_1127_);
lean_ctor_set(v_methods_1130_, 4, v___f_1129_);
lean_inc(v_ref_1118_);
lean_inc(v_maxRecDepth_1117_);
lean_inc(v_currRecDepth_1116_);
lean_inc(v_currMacroScope_1122_);
lean_inc(v_quotContext_1121_);
v___x_1131_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1131_, 0, v_methods_1130_);
lean_ctor_set(v___x_1131_, 1, v_quotContext_1121_);
lean_ctor_set(v___x_1131_, 2, v_currMacroScope_1122_);
lean_ctor_set(v___x_1131_, 3, v_currRecDepth_1116_);
lean_ctor_set(v___x_1131_, 4, v_maxRecDepth_1117_);
lean_ctor_set(v___x_1131_, 5, v_ref_1118_);
v___x_1132_ = lean_box(0);
v___x_1133_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1133_, 0, v_nextMacroScope_1124_);
lean_ctor_set(v___x_1133_, 1, v___x_1132_);
lean_ctor_set(v___x_1133_, 2, v___x_1132_);
v___x_1134_ = lean_apply_2(v_x_1104_, v___x_1131_, v___x_1133_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v_a_1135_; lean_object* v_a_1136_; lean_object* v_macroScope_1137_; lean_object* v_traceMsgs_1138_; lean_object* v_expandedMacroDecls_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v_a_1135_ = lean_ctor_get(v___x_1134_, 1);
lean_inc(v_a_1135_);
v_a_1136_ = lean_ctor_get(v___x_1134_, 0);
lean_inc(v_a_1136_);
lean_dec_ref(v___x_1134_);
v_macroScope_1137_ = lean_ctor_get(v_a_1135_, 0);
lean_inc(v_macroScope_1137_);
v_traceMsgs_1138_ = lean_ctor_get(v_a_1135_, 1);
lean_inc(v_traceMsgs_1138_);
v_expandedMacroDecls_1139_ = lean_ctor_get(v_a_1135_, 2);
lean_inc(v_expandedMacroDecls_1139_);
lean_dec(v_a_1135_);
v___x_1140_ = lean_box(0);
v___x_1141_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4___redArg(v_expandedMacroDecls_1139_, v___x_1140_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v___x_1142_; lean_object* v_env_1143_; lean_object* v_ngen_1144_; lean_object* v_auxDeclNGen_1145_; lean_object* v_traceState_1146_; lean_object* v_cache_1147_; lean_object* v_messages_1148_; lean_object* v_infoState_1149_; lean_object* v_snapshotTasks_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1176_; 
lean_dec_ref(v___x_1141_);
v___x_1142_ = lean_st_ref_take(v___y_1111_);
v_env_1143_ = lean_ctor_get(v___x_1142_, 0);
v_ngen_1144_ = lean_ctor_get(v___x_1142_, 2);
v_auxDeclNGen_1145_ = lean_ctor_get(v___x_1142_, 3);
v_traceState_1146_ = lean_ctor_get(v___x_1142_, 4);
v_cache_1147_ = lean_ctor_get(v___x_1142_, 5);
v_messages_1148_ = lean_ctor_get(v___x_1142_, 6);
v_infoState_1149_ = lean_ctor_get(v___x_1142_, 7);
v_snapshotTasks_1150_ = lean_ctor_get(v___x_1142_, 8);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1176_ == 0)
{
lean_object* v_unused_1177_; 
v_unused_1177_ = lean_ctor_get(v___x_1142_, 1);
lean_dec(v_unused_1177_);
v___x_1152_ = v___x_1142_;
v_isShared_1153_ = v_isSharedCheck_1176_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_snapshotTasks_1150_);
lean_inc(v_infoState_1149_);
lean_inc(v_messages_1148_);
lean_inc(v_cache_1147_);
lean_inc(v_traceState_1146_);
lean_inc(v_auxDeclNGen_1145_);
lean_inc(v_ngen_1144_);
lean_inc(v_env_1143_);
lean_dec(v___x_1142_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1176_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 1, v_macroScope_1137_);
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_env_1143_);
lean_ctor_set(v_reuseFailAlloc_1175_, 1, v_macroScope_1137_);
lean_ctor_set(v_reuseFailAlloc_1175_, 2, v_ngen_1144_);
lean_ctor_set(v_reuseFailAlloc_1175_, 3, v_auxDeclNGen_1145_);
lean_ctor_set(v_reuseFailAlloc_1175_, 4, v_traceState_1146_);
lean_ctor_set(v_reuseFailAlloc_1175_, 5, v_cache_1147_);
lean_ctor_set(v_reuseFailAlloc_1175_, 6, v_messages_1148_);
lean_ctor_set(v_reuseFailAlloc_1175_, 7, v_infoState_1149_);
lean_ctor_set(v_reuseFailAlloc_1175_, 8, v_snapshotTasks_1150_);
v___x_1155_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1156_ = lean_st_ref_set(v___y_1111_, v___x_1155_);
v___x_1157_ = l_List_reverse___redArg(v_traceMsgs_1138_);
v___x_1158_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5(v___x_1157_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
lean_dec_ref(v___y_1110_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1165_; 
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1165_ == 0)
{
lean_object* v_unused_1166_; 
v_unused_1166_ = lean_ctor_get(v___x_1158_, 0);
lean_dec(v_unused_1166_);
v___x_1160_ = v___x_1158_;
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
else
{
lean_dec(v___x_1158_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 0, v_a_1136_);
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1136_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
else
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1174_; 
lean_dec(v_a_1136_);
v_a_1167_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1169_ = v___x_1158_;
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1158_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1170_ == 0)
{
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_a_1167_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
}
}
else
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
lean_dec(v_traceMsgs_1138_);
lean_dec(v_macroScope_1137_);
lean_dec(v_a_1136_);
lean_dec_ref(v___y_1110_);
v_a_1178_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v___x_1141_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1141_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1178_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
else
{
lean_object* v_a_1186_; 
v_a_1186_ = lean_ctor_get(v___x_1134_, 0);
lean_inc(v_a_1186_);
lean_dec_ref(v___x_1134_);
if (lean_obj_tag(v_a_1186_) == 0)
{
lean_object* v_a_1187_; lean_object* v_a_1188_; lean_object* v___x_1189_; uint8_t v___x_1190_; 
v_a_1187_ = lean_ctor_get(v_a_1186_, 0);
lean_inc(v_a_1187_);
v_a_1188_ = lean_ctor_get(v_a_1186_, 1);
lean_inc_ref(v_a_1188_);
lean_dec_ref(v_a_1186_);
v___x_1189_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___closed__0));
v___x_1190_ = lean_string_dec_eq(v_a_1188_, v___x_1189_);
if (v___x_1190_ == 0)
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1191_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1191_, 0, v_a_1188_);
v___x_1192_ = l_Lean_MessageData_ofFormat(v___x_1191_);
v___x_1193_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1___redArg(v_a_1187_, v___x_1192_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
lean_dec_ref(v___y_1110_);
lean_dec(v_a_1187_);
return v___x_1193_;
}
else
{
lean_object* v___x_1194_; 
lean_dec_ref(v_a_1188_);
lean_dec_ref(v___y_1110_);
v___x_1194_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg(v_a_1187_);
return v___x_1194_;
}
}
else
{
lean_object* v___x_1195_; 
lean_dec_ref(v___y_1110_);
v___x_1195_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__7___redArg();
return v___x_1195_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___boxed(lean_object* v_x_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg(v_x_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
lean_dec(v___y_1203_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
lean_dec(v___y_1197_);
return v_res_1205_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheck___closed__1(void){
_start:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1207_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheck___closed__0));
v___x_1208_ = l_Lean_stringToMessageData(v___x_1207_);
return v___x_1208_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheck___closed__3(void){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheck___closed__2));
v___x_1211_ = l_Lean_stringToMessageData(v___x_1210_);
return v___x_1211_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheck___closed__5(void){
_start:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1213_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheck___closed__4));
v___x_1214_ = l_Lean_stringToMessageData(v___x_1213_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheck(lean_object* v_stx_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_){
_start:
{
lean_object* v___y_1228_; lean_object* v___y_1229_; lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___x_1273_; lean_object* v_env_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1273_ = lean_st_ref_get(v_a_1222_);
v_env_1274_ = lean_ctor_get(v___x_1273_, 0);
lean_inc_ref(v_env_1274_);
lean_dec(v___x_1273_);
v___x_1275_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
lean_inc(v_stx_1215_);
v___x_1276_ = l_Lean_Syntax_getKind(v_stx_1215_);
v___x_1277_ = l_Lean_KeyedDeclsAttribute_getValues___redArg(v___x_1275_, v_env_1274_, v___x_1276_);
lean_dec(v___x_1276_);
if (lean_obj_tag(v___x_1277_) == 1)
{
lean_object* v_head_1278_; lean_object* v_fileName_1279_; lean_object* v_fileMap_1280_; lean_object* v_options_1281_; lean_object* v_currRecDepth_1282_; lean_object* v_maxRecDepth_1283_; lean_object* v_ref_1284_; lean_object* v_currNamespace_1285_; lean_object* v_openDecls_1286_; lean_object* v_initHeartbeats_1287_; lean_object* v_maxHeartbeats_1288_; lean_object* v_quotContext_1289_; lean_object* v_currMacroScope_1290_; uint8_t v_diag_1291_; lean_object* v_cancelTk_x3f_1292_; uint8_t v_suppressElabErrors_1293_; lean_object* v_inheritedTraceOptions_1294_; lean_object* v_ref_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
v_head_1278_ = lean_ctor_get(v___x_1277_, 0);
lean_inc(v_head_1278_);
lean_dec_ref(v___x_1277_);
v_fileName_1279_ = lean_ctor_get(v_a_1221_, 0);
v_fileMap_1280_ = lean_ctor_get(v_a_1221_, 1);
v_options_1281_ = lean_ctor_get(v_a_1221_, 2);
v_currRecDepth_1282_ = lean_ctor_get(v_a_1221_, 3);
v_maxRecDepth_1283_ = lean_ctor_get(v_a_1221_, 4);
v_ref_1284_ = lean_ctor_get(v_a_1221_, 5);
v_currNamespace_1285_ = lean_ctor_get(v_a_1221_, 6);
v_openDecls_1286_ = lean_ctor_get(v_a_1221_, 7);
v_initHeartbeats_1287_ = lean_ctor_get(v_a_1221_, 8);
v_maxHeartbeats_1288_ = lean_ctor_get(v_a_1221_, 9);
v_quotContext_1289_ = lean_ctor_get(v_a_1221_, 10);
v_currMacroScope_1290_ = lean_ctor_get(v_a_1221_, 11);
v_diag_1291_ = lean_ctor_get_uint8(v_a_1221_, sizeof(void*)*14);
v_cancelTk_x3f_1292_ = lean_ctor_get(v_a_1221_, 12);
v_suppressElabErrors_1293_ = lean_ctor_get_uint8(v_a_1221_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1294_ = lean_ctor_get(v_a_1221_, 13);
v_ref_1295_ = l_Lean_replaceRef(v_stx_1215_, v_ref_1284_);
lean_inc_ref(v_inheritedTraceOptions_1294_);
lean_inc(v_cancelTk_x3f_1292_);
lean_inc(v_currMacroScope_1290_);
lean_inc(v_quotContext_1289_);
lean_inc(v_maxHeartbeats_1288_);
lean_inc(v_initHeartbeats_1287_);
lean_inc(v_openDecls_1286_);
lean_inc(v_currNamespace_1285_);
lean_inc(v_maxRecDepth_1283_);
lean_inc(v_currRecDepth_1282_);
lean_inc_ref(v_options_1281_);
lean_inc_ref(v_fileMap_1280_);
lean_inc_ref(v_fileName_1279_);
v___x_1296_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1296_, 0, v_fileName_1279_);
lean_ctor_set(v___x_1296_, 1, v_fileMap_1280_);
lean_ctor_set(v___x_1296_, 2, v_options_1281_);
lean_ctor_set(v___x_1296_, 3, v_currRecDepth_1282_);
lean_ctor_set(v___x_1296_, 4, v_maxRecDepth_1283_);
lean_ctor_set(v___x_1296_, 5, v_ref_1295_);
lean_ctor_set(v___x_1296_, 6, v_currNamespace_1285_);
lean_ctor_set(v___x_1296_, 7, v_openDecls_1286_);
lean_ctor_set(v___x_1296_, 8, v_initHeartbeats_1287_);
lean_ctor_set(v___x_1296_, 9, v_maxHeartbeats_1288_);
lean_ctor_set(v___x_1296_, 10, v_quotContext_1289_);
lean_ctor_set(v___x_1296_, 11, v_currMacroScope_1290_);
lean_ctor_set(v___x_1296_, 12, v_cancelTk_x3f_1292_);
lean_ctor_set(v___x_1296_, 13, v_inheritedTraceOptions_1294_);
lean_ctor_set_uint8(v___x_1296_, sizeof(void*)*14, v_diag_1291_);
lean_ctor_set_uint8(v___x_1296_, sizeof(void*)*14 + 1, v_suppressElabErrors_1293_);
lean_inc(v_a_1222_);
lean_inc(v_a_1220_);
lean_inc_ref(v_a_1219_);
lean_inc(v_a_1218_);
lean_inc_ref(v_a_1217_);
lean_inc(v_a_1216_);
lean_inc(v_stx_1215_);
v___x_1297_ = lean_apply_9(v_head_1278_, v_stx_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v___x_1296_, v_a_1222_, lean_box(0));
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1305_; 
lean_dec(v_stx_1215_);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1305_ == 0)
{
lean_object* v_unused_1306_; 
v_unused_1306_ = lean_ctor_get(v___x_1297_, 0);
lean_dec(v_unused_1306_);
v___x_1299_ = v___x_1297_;
v_isShared_1300_ = v_isSharedCheck_1305_;
goto v_resetjp_1298_;
}
else
{
lean_dec(v___x_1297_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1305_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1301_; lean_object* v___x_1303_; 
v___x_1301_ = lean_box(0);
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 0, v___x_1301_);
v___x_1303_ = v___x_1299_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v___x_1301_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
else
{
lean_object* v_a_1307_; lean_object* v___x_1308_; uint8_t v___y_1310_; uint8_t v___x_1313_; 
v_a_1307_ = lean_ctor_get(v___x_1297_, 0);
lean_inc(v_a_1307_);
v___x_1308_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1313_ = l_Lean_Exception_isInterrupt(v_a_1307_);
if (v___x_1313_ == 0)
{
uint8_t v___x_1314_; 
lean_inc(v_a_1307_);
v___x_1314_ = l_Lean_Exception_isRuntime(v_a_1307_);
v___y_1310_ = v___x_1314_;
goto v___jp_1309_;
}
else
{
v___y_1310_ = v___x_1313_;
goto v___jp_1309_;
}
v___jp_1309_:
{
if (v___y_1310_ == 0)
{
if (lean_obj_tag(v_a_1307_) == 0)
{
lean_dec_ref(v_a_1307_);
lean_dec(v_stx_1215_);
return v___x_1297_;
}
else
{
lean_object* v_id_1311_; uint8_t v___x_1312_; 
v_id_1311_ = lean_ctor_get(v_a_1307_, 0);
lean_inc(v_id_1311_);
lean_dec_ref(v_a_1307_);
v___x_1312_ = l_Lean_instBEqInternalExceptionId_beq(v___x_1308_, v_id_1311_);
lean_dec(v_id_1311_);
if (v___x_1312_ == 0)
{
lean_dec(v_stx_1215_);
return v___x_1297_;
}
else
{
lean_dec_ref(v___x_1297_);
v___y_1228_ = v_a_1216_;
v___y_1229_ = v_a_1217_;
v___y_1230_ = v_a_1218_;
v___y_1231_ = v_a_1219_;
v___y_1232_ = v_a_1220_;
v___y_1233_ = v_a_1221_;
v___y_1234_ = v_a_1222_;
goto v___jp_1227_;
}
}
}
else
{
lean_dec(v_a_1307_);
lean_dec(v_stx_1215_);
return v___x_1297_;
}
}
}
}
else
{
lean_dec(v___x_1277_);
v___y_1228_ = v_a_1216_;
v___y_1229_ = v_a_1217_;
v___y_1230_ = v_a_1218_;
v___y_1231_ = v_a_1219_;
v___y_1232_ = v_a_1220_;
v___y_1233_ = v_a_1221_;
v___y_1234_ = v_a_1222_;
goto v___jp_1227_;
}
v___jp_1224_:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1225_ = lean_box(0);
v___x_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
return v___x_1226_;
}
v___jp_1227_:
{
uint8_t v___x_1235_; 
lean_inc(v_stx_1215_);
v___x_1235_ = l_Lean_Syntax_isAnyAntiquot(v_stx_1215_);
if (v___x_1235_ == 0)
{
uint8_t v___x_1236_; 
lean_inc(v_stx_1215_);
v___x_1236_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent(v_stx_1215_);
if (v___x_1236_ == 0)
{
lean_dec(v_stx_1215_);
goto v___jp_1224_;
}
else
{
if (v___x_1235_ == 0)
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
lean_inc(v_stx_1215_);
v___x_1237_ = lean_alloc_closure((void*)(l_Lean_Macro_expandMacro_x3f___boxed), 3, 1);
lean_closure_set(v___x_1237_, 0, v_stx_1215_);
lean_inc_ref(v___y_1233_);
v___x_1238_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg(v___x_1237_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_a_1239_; 
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_a_1239_);
lean_dec_ref(v___x_1238_);
if (lean_obj_tag(v_a_1239_) == 1)
{
lean_object* v_val_1240_; lean_object* v___x_1241_; 
lean_dec(v_stx_1215_);
v_val_1240_ = lean_ctor_get(v_a_1239_, 0);
lean_inc(v_val_1240_);
lean_dec_ref(v_a_1239_);
v___x_1241_ = l_Lean_Elab_Term_Quotation_precheck(v_val_1240_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1249_; 
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1249_ == 0)
{
lean_object* v_unused_1250_; 
v_unused_1250_ = lean_ctor_get(v___x_1241_, 0);
lean_dec(v_unused_1250_);
v___x_1243_ = v___x_1241_;
v_isShared_1244_ = v_isSharedCheck_1249_;
goto v_resetjp_1242_;
}
else
{
lean_dec(v___x_1241_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1249_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1245_; lean_object* v___x_1247_; 
v___x_1245_ = lean_box(0);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 0, v___x_1245_);
v___x_1247_ = v___x_1243_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v___x_1245_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
else
{
return v___x_1241_;
}
}
else
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
lean_dec(v_a_1239_);
v___x_1251_ = lean_obj_once(&l_Lean_Elab_Term_Quotation_precheck___closed__1, &l_Lean_Elab_Term_Quotation_precheck___closed__1_once, _init_l_Lean_Elab_Term_Quotation_precheck___closed__1);
lean_inc(v_stx_1215_);
v___x_1252_ = l_Lean_Syntax_getKind(v_stx_1215_);
v___x_1253_ = l_Lean_MessageData_ofName(v___x_1252_);
v___x_1254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1251_);
lean_ctor_set(v___x_1254_, 1, v___x_1253_);
v___x_1255_ = lean_obj_once(&l_Lean_Elab_Term_Quotation_precheck___closed__3, &l_Lean_Elab_Term_Quotation_precheck___closed__3_once, _init_l_Lean_Elab_Term_Quotation_precheck___closed__3);
v___x_1256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1254_);
lean_ctor_set(v___x_1256_, 1, v___x_1255_);
lean_inc(v_stx_1215_);
v___x_1257_ = l_Lean_MessageData_ofSyntax(v_stx_1215_);
v___x_1258_ = l_Lean_indentD(v___x_1257_);
v___x_1259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1256_);
lean_ctor_set(v___x_1259_, 1, v___x_1258_);
v___x_1260_ = lean_obj_once(&l_Lean_Elab_Term_Quotation_precheck___closed__5, &l_Lean_Elab_Term_Quotation_precheck___closed__5_once, _init_l_Lean_Elab_Term_Quotation_precheck___closed__5);
v___x_1261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1259_);
lean_ctor_set(v___x_1261_, 1, v___x_1260_);
v___x_1262_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1___redArg(v_stx_1215_, v___x_1261_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
lean_dec(v_stx_1215_);
return v___x_1262_;
}
}
else
{
lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1270_; 
lean_dec(v_stx_1215_);
v_a_1263_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1265_ = v___x_1238_;
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_dec(v___x_1238_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1268_; 
if (v_isShared_1266_ == 0)
{
v___x_1268_ = v___x_1265_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_a_1263_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
}
else
{
lean_dec(v_stx_1215_);
goto v___jp_1224_;
}
}
}
else
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
lean_dec(v_stx_1215_);
v___x_1271_ = lean_box(0);
v___x_1272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1271_);
return v___x_1272_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheck___boxed(lean_object* v_stx_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_Lean_Elab_Term_Quotation_precheck(v_stx_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_);
lean_dec(v_a_1322_);
lean_dec_ref(v_a_1321_);
lean_dec(v_a_1320_);
lean_dec_ref(v_a_1319_);
lean_dec(v_a_1318_);
lean_dec_ref(v_a_1317_);
lean_dec(v_a_1316_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0(lean_object* v_cls_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v___x_1334_; 
v___x_1334_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg(v_cls_1325_, v___y_1331_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___boxed(lean_object* v_cls_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0(v_cls_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec(v___y_1336_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2(lean_object* v_00_u03b1_1345_, lean_object* v_x_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v___x_1349_; 
v___x_1349_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___redArg(v_x_1346_, v___y_1348_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1350_, lean_object* v_x_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2(v_00_u03b1_1350_, v_x_1351_, v___y_1352_, v___y_1353_);
lean_dec_ref(v___y_1352_);
lean_dec_ref(v_x_1351_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6(lean_object* v_00_u03b1_1355_, lean_object* v_ref_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
lean_object* v___x_1365_; 
v___x_1365_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg(v_ref_1356_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___boxed(lean_object* v_00_u03b1_1366_, lean_object* v_ref_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6(v_00_u03b1_1366_, v_ref_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
lean_dec(v___y_1374_);
lean_dec_ref(v___y_1373_);
lean_dec(v___y_1372_);
lean_dec_ref(v___y_1371_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
lean_dec(v___y_1368_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__7(lean_object* v_00_u03b1_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_){
_start:
{
lean_object* v___x_1386_; 
v___x_1386_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__7___redArg();
return v___x_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__7___boxed(lean_object* v_00_u03b1_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__7(v_00_u03b1_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
lean_dec(v___y_1392_);
lean_dec_ref(v___y_1391_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec(v___y_1388_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0(lean_object* v_00_u03b1_1397_, lean_object* v_x_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v___x_1407_; 
lean_inc_ref(v___y_1404_);
v___x_1407_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg(v_x_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___boxed(lean_object* v_00_u03b1_1408_, lean_object* v_x_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0(v_00_u03b1_1408_, v_x_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
lean_dec(v___y_1410_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1(lean_object* v_00_u03b1_1419_, lean_object* v_ref_1420_, lean_object* v_msg_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
lean_object* v___x_1430_; 
v___x_1430_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1___redArg(v_ref_1420_, v_msg_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1___boxed(lean_object* v_00_u03b1_1431_, lean_object* v_ref_1432_, lean_object* v_msg_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1(v_00_u03b1_1431_, v_ref_1432_, v_msg_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec(v___y_1438_);
lean_dec_ref(v___y_1437_);
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
lean_dec(v___y_1434_);
lean_dec(v_ref_1432_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1(lean_object* v_cls_1443_, lean_object* v_msg_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v___x_1453_; 
v___x_1453_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___redArg(v_cls_1443_, v_msg_1444_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___boxed(lean_object* v_cls_1454_, lean_object* v_msg_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v_res_1464_; 
v_res_1464_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1(v_cls_1454_, v_msg_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
lean_dec(v___y_1456_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4(lean_object* v_as_1465_, lean_object* v_as_x27_1466_, lean_object* v_b_1467_, lean_object* v_a_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
lean_object* v___x_1477_; 
v___x_1477_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4___redArg(v_as_x27_1466_, v_b_1467_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4___boxed(lean_object* v_as_1478_, lean_object* v_as_x27_1479_, lean_object* v_b_1480_, lean_object* v_a_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
lean_object* v_res_1490_; 
v_res_1490_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4(v_as_1478_, v_as_x27_1479_, v_b_1480_, v_a_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
lean_dec(v___y_1482_);
lean_dec(v_as_1478_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1_spec__9(lean_object* v_00_u03b1_1491_, lean_object* v_msg_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v___x_1501_; 
v___x_1501_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1_spec__9___redArg(v_msg_1492_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1_spec__9___boxed(lean_object* v_00_u03b1_1502_, lean_object* v_msg_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1_spec__9(v_00_u03b1_1502_, v_msg_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
lean_dec(v___y_1504_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__7(lean_object* v_00_u03b2_1513_, lean_object* v_m_1514_, lean_object* v_a_1515_){
_start:
{
lean_object* v___x_1516_; 
v___x_1516_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__7___redArg(v_m_1514_, v_a_1515_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__7___boxed(lean_object* v_00_u03b2_1517_, lean_object* v_m_1518_, lean_object* v_a_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__7(v_00_u03b2_1517_, v_m_1518_, v_a_1519_);
lean_dec(v_a_1519_);
lean_dec_ref(v_m_1518_);
return v_res_1520_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_1521_, lean_object* v_x_1522_, lean_object* v_x_1523_){
_start:
{
uint8_t v___x_1524_; 
v___x_1524_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9___redArg(v_x_1522_, v_x_1523_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03b2_1525_, lean_object* v_x_1526_, lean_object* v_x_1527_){
_start:
{
uint8_t v_res_1528_; lean_object* v_r_1529_; 
v_res_1528_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9(v_00_u03b2_1525_, v_x_1526_, v_x_1527_);
lean_dec_ref(v_x_1527_);
v_r_1529_ = lean_box(v_res_1528_);
return v_r_1529_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__7_spec__12(lean_object* v_00_u03b2_1530_, lean_object* v_a_1531_, lean_object* v_x_1532_){
_start:
{
lean_object* v___x_1533_; 
v___x_1533_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__7_spec__12___redArg(v_a_1531_, v_x_1532_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__7_spec__12___boxed(lean_object* v_00_u03b2_1534_, lean_object* v_a_1535_, lean_object* v_x_1536_){
_start:
{
lean_object* v_res_1537_; 
v_res_1537_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__7_spec__12(v_00_u03b2_1534_, v_a_1535_, v_x_1536_);
lean_dec(v_x_1536_);
lean_dec(v_a_1535_);
return v_res_1537_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9_spec__13(lean_object* v_00_u03b2_1538_, lean_object* v_x_1539_, size_t v_x_1540_, lean_object* v_x_1541_){
_start:
{
uint8_t v___x_1542_; 
v___x_1542_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9_spec__13___redArg(v_x_1539_, v_x_1540_, v_x_1541_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9_spec__13___boxed(lean_object* v_00_u03b2_1543_, lean_object* v_x_1544_, lean_object* v_x_1545_, lean_object* v_x_1546_){
_start:
{
size_t v_x_28904__boxed_1547_; uint8_t v_res_1548_; lean_object* v_r_1549_; 
v_x_28904__boxed_1547_ = lean_unbox_usize(v_x_1545_);
lean_dec(v_x_1545_);
v_res_1548_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9_spec__13(v_00_u03b2_1543_, v_x_1544_, v_x_28904__boxed_1547_, v_x_1546_);
lean_dec_ref(v_x_1546_);
v_r_1549_ = lean_box(v_res_1548_);
return v_r_1549_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9_spec__13_spec__16(lean_object* v_00_u03b2_1550_, lean_object* v_keys_1551_, lean_object* v_vals_1552_, lean_object* v_heq_1553_, lean_object* v_i_1554_, lean_object* v_k_1555_){
_start:
{
uint8_t v___x_1556_; 
v___x_1556_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9_spec__13_spec__16___redArg(v_keys_1551_, v_i_1554_, v_k_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9_spec__13_spec__16___boxed(lean_object* v_00_u03b2_1557_, lean_object* v_keys_1558_, lean_object* v_vals_1559_, lean_object* v_heq_1560_, lean_object* v_i_1561_, lean_object* v_k_1562_){
_start:
{
uint8_t v_res_1563_; lean_object* v_r_1564_; 
v_res_1563_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3_spec__5_spec__9_spec__13_spec__16(v_00_u03b2_1557_, v_keys_1558_, v_vals_1559_, v_heq_1560_, v_i_1561_, v_k_1562_);
lean_dec_ref(v_k_1562_);
lean_dec_ref(v_vals_1559_);
lean_dec_ref(v_keys_1558_);
v_r_1564_ = lean_box(v_res_1563_);
return v_r_1564_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Term_Quotation_runPrecheck_spec__0(lean_object* v_opts_1565_, lean_object* v_opt_1566_){
_start:
{
lean_object* v_name_1567_; lean_object* v_defValue_1568_; lean_object* v_map_1569_; lean_object* v___x_1570_; 
v_name_1567_ = lean_ctor_get(v_opt_1566_, 0);
v_defValue_1568_ = lean_ctor_get(v_opt_1566_, 1);
v_map_1569_ = lean_ctor_get(v_opts_1565_, 0);
v___x_1570_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1569_, v_name_1567_);
if (lean_obj_tag(v___x_1570_) == 0)
{
uint8_t v___x_1571_; 
v___x_1571_ = lean_unbox(v_defValue_1568_);
return v___x_1571_;
}
else
{
lean_object* v_val_1572_; 
v_val_1572_ = lean_ctor_get(v___x_1570_, 0);
lean_inc(v_val_1572_);
lean_dec_ref(v___x_1570_);
if (lean_obj_tag(v_val_1572_) == 1)
{
uint8_t v_v_1573_; 
v_v_1573_ = lean_ctor_get_uint8(v_val_1572_, 0);
lean_dec_ref(v_val_1572_);
return v_v_1573_;
}
else
{
uint8_t v___x_1574_; 
lean_dec(v_val_1572_);
v___x_1574_ = lean_unbox(v_defValue_1568_);
return v___x_1574_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Term_Quotation_runPrecheck_spec__0___boxed(lean_object* v_opts_1575_, lean_object* v_opt_1576_){
_start:
{
uint8_t v_res_1577_; lean_object* v_r_1578_; 
v_res_1577_ = l_Lean_Option_get___at___00Lean_Elab_Term_Quotation_runPrecheck_spec__0(v_opts_1575_, v_opt_1576_);
lean_dec_ref(v_opt_1576_);
lean_dec_ref(v_opts_1575_);
v_r_1578_ = lean_box(v_res_1577_);
return v_r_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_runPrecheck(lean_object* v_stx_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_){
_start:
{
uint8_t v___y_1588_; lean_object* v_options_1593_; lean_object* v___x_1594_; uint8_t v___x_1595_; 
v_options_1593_ = lean_ctor_get(v_a_1584_, 2);
v___x_1594_ = l_Lean_Elab_Term_Quotation_quotPrecheck;
v___x_1595_ = l_Lean_Option_get___at___00Lean_Elab_Term_Quotation_runPrecheck_spec__0(v_options_1593_, v___x_1594_);
if (v___x_1595_ == 0)
{
v___y_1588_ = v___x_1595_;
goto v___jp_1587_;
}
else
{
lean_object* v___x_1596_; uint8_t v___x_1597_; 
v___x_1596_ = l_Lean_Elab_Term_Quotation_hygiene;
v___x_1597_ = l_Lean_Option_get___at___00Lean_Elab_Term_Quotation_runPrecheck_spec__0(v_options_1593_, v___x_1596_);
v___y_1588_ = v___x_1597_;
goto v___jp_1587_;
}
v___jp_1587_:
{
if (v___y_1588_ == 0)
{
lean_object* v___x_1589_; lean_object* v___x_1590_; 
lean_dec(v_stx_1579_);
v___x_1589_ = lean_box(0);
v___x_1590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1589_);
return v___x_1590_;
}
else
{
lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1591_ = l_Lean_NameSet_empty;
v___x_1592_ = l_Lean_Elab_Term_Quotation_precheck(v_stx_1579_, v___x_1591_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_);
return v___x_1592_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_runPrecheck___boxed(lean_object* v_stx_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l_Lean_Elab_Term_Quotation_runPrecheck(v_stx_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_);
lean_dec(v_a_1604_);
lean_dec_ref(v_a_1603_);
lean_dec(v_a_1602_);
lean_dec_ref(v_a_1601_);
lean_dec(v_a_1600_);
lean_dec_ref(v_a_1599_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable_spec__0(lean_object* v_e_1610_, lean_object* v_init_1611_, lean_object* v_x_1612_){
_start:
{
if (lean_obj_tag(v_x_1612_) == 0)
{
lean_object* v_v_1613_; lean_object* v_l_1614_; lean_object* v_r_1615_; lean_object* v___x_1616_; 
v_v_1613_ = lean_ctor_get(v_x_1612_, 2);
v_l_1614_ = lean_ctor_get(v_x_1612_, 3);
v_r_1615_ = lean_ctor_get(v_x_1612_, 4);
v___x_1616_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable_spec__0(v_e_1610_, v_init_1611_, v_l_1614_);
if (lean_obj_tag(v___x_1616_) == 0)
{
return v___x_1616_;
}
else
{
lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1630_; 
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1630_ == 0)
{
lean_object* v_unused_1631_; 
v_unused_1631_ = lean_ctor_get(v___x_1616_, 0);
lean_dec(v_unused_1631_);
v___x_1618_ = v___x_1616_;
v_isShared_1619_ = v_isSharedCheck_1630_;
goto v_resetjp_1617_;
}
else
{
lean_dec(v___x_1616_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1630_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1620_; uint8_t v___x_1621_; 
v___x_1620_ = lean_box(0);
v___x_1621_ = lean_expr_eqv(v_e_1610_, v_v_1613_);
if (v___x_1621_ == 0)
{
lean_object* v___x_1622_; 
lean_del_object(v___x_1618_);
v___x_1622_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable_spec__0___closed__0));
v_init_1611_ = v___x_1622_;
v_x_1612_ = v_r_1615_;
goto _start;
}
else
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1628_; 
v___x_1624_ = lean_box(v___x_1621_);
v___x_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1624_);
v___x_1626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1625_);
lean_ctor_set(v___x_1626_, 1, v___x_1620_);
if (v_isShared_1619_ == 0)
{
lean_ctor_set_tag(v___x_1618_, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1626_);
v___x_1628_ = v___x_1618_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v___x_1626_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
}
}
else
{
lean_object* v___x_1632_; 
v___x_1632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1632_, 0, v_init_1611_);
return v___x_1632_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable_spec__0___boxed(lean_object* v_e_1633_, lean_object* v_init_1634_, lean_object* v_x_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable_spec__0(v_e_1633_, v_init_1634_, v_x_1635_);
lean_dec(v_x_1635_);
lean_dec_ref(v_e_1633_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable___redArg(lean_object* v_e_1637_, lean_object* v_a_1638_){
_start:
{
lean_object* v___y_1641_; lean_object* v_sectionFVars_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v_a_1657_; 
v_sectionFVars_1654_ = lean_ctor_get(v_a_1638_, 5);
v___x_1655_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable_spec__0___closed__0));
v___x_1656_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable_spec__0(v_e_1637_, v___x_1655_, v_sectionFVars_1654_);
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
lean_inc(v_a_1657_);
lean_dec_ref(v___x_1656_);
v___y_1641_ = v_a_1657_;
goto v___jp_1640_;
v___jp_1640_:
{
lean_object* v_fst_1642_; 
v_fst_1642_ = lean_ctor_get(v___y_1641_, 0);
lean_inc(v_fst_1642_);
lean_dec_ref(v___y_1641_);
if (lean_obj_tag(v_fst_1642_) == 0)
{
uint8_t v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1643_ = 0;
v___x_1644_ = lean_box(v___x_1643_);
v___x_1645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1644_);
return v___x_1645_;
}
else
{
lean_object* v_val_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1653_; 
v_val_1646_ = lean_ctor_get(v_fst_1642_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v_fst_1642_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1648_ = v_fst_1642_;
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_val_1646_);
lean_dec(v_fst_1642_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1651_; 
if (v_isShared_1649_ == 0)
{
lean_ctor_set_tag(v___x_1648_, 0);
v___x_1651_ = v___x_1648_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_val_1646_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable___redArg___boxed(lean_object* v_e_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable___redArg(v_e_1658_, v_a_1659_);
lean_dec_ref(v_a_1659_);
lean_dec_ref(v_e_1658_);
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable(lean_object* v_e_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_){
_start:
{
lean_object* v___x_1670_; 
v___x_1670_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable___redArg(v_e_1662_, v_a_1663_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable___boxed(lean_object* v_e_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable(v_e_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_);
lean_dec(v_a_1677_);
lean_dec_ref(v_a_1676_);
lean_dec(v_a_1675_);
lean_dec_ref(v_a_1674_);
lean_dec(v_a_1673_);
lean_dec_ref(v_a_1672_);
lean_dec_ref(v_e_1671_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg(lean_object* v_as_x27_1688_, lean_object* v_b_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_){
_start:
{
if (lean_obj_tag(v_as_x27_1688_) == 0)
{
lean_object* v___x_1693_; 
v___x_1693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1693_, 0, v_b_1689_);
return v___x_1693_;
}
else
{
lean_object* v_head_1694_; lean_object* v_tail_1695_; lean_object* v_fst_1696_; lean_object* v___x_1697_; 
lean_dec_ref(v_b_1689_);
v_head_1694_ = lean_ctor_get(v_as_x27_1688_, 0);
v_tail_1695_ = lean_ctor_get(v_as_x27_1688_, 1);
v_fst_1696_ = lean_ctor_get(v_head_1694_, 0);
v___x_1697_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___closed__0));
if (lean_obj_tag(v_fst_1696_) == 1)
{
lean_object* v___x_1698_; lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1714_; 
v___x_1698_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable___redArg(v_fst_1696_, v___y_1690_);
v_a_1699_ = lean_ctor_get(v___x_1698_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1701_ = v___x_1698_;
v_isShared_1702_ = v_isSharedCheck_1714_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___x_1698_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1714_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
uint8_t v___y_1704_; lean_object* v_options_1710_; lean_object* v___x_1711_; uint8_t v___x_1712_; 
v_options_1710_ = lean_ctor_get(v___y_1691_, 2);
v___x_1711_ = l_Lean_Elab_Term_Quotation_quotPrecheck_allowSectionVars;
v___x_1712_ = l_Lean_Option_get___at___00Lean_Elab_Term_Quotation_runPrecheck_spec__0(v_options_1710_, v___x_1711_);
if (v___x_1712_ == 0)
{
lean_dec(v_a_1699_);
v___y_1704_ = v___x_1712_;
goto v___jp_1703_;
}
else
{
uint8_t v___x_1713_; 
v___x_1713_ = lean_unbox(v_a_1699_);
lean_dec(v_a_1699_);
v___y_1704_ = v___x_1713_;
goto v___jp_1703_;
}
v___jp_1703_:
{
if (v___y_1704_ == 0)
{
lean_del_object(v___x_1701_);
v_as_x27_1688_ = v_tail_1695_;
v_b_1689_ = v___x_1697_;
goto _start;
}
else
{
lean_object* v___x_1706_; lean_object* v___x_1708_; 
v___x_1706_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___closed__2));
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 0, v___x_1706_);
v___x_1708_ = v___x_1701_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v___x_1706_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
}
else
{
v_as_x27_1688_ = v_tail_1695_;
v_b_1689_ = v___x_1697_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___boxed(lean_object* v_as_x27_1716_, lean_object* v_b_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg(v_as_x27_1716_, v_b_1717_, v___y_1718_, v___y_1719_);
lean_dec_ref(v___y_1719_);
lean_dec_ref(v___y_1718_);
lean_dec(v_as_x27_1716_);
return v_res_1721_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckIdent___closed__1(void){
_start:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1723_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckIdent___closed__0));
v___x_1724_ = l_Lean_stringToMessageData(v___x_1723_);
return v___x_1724_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckIdent___closed__3(void){
_start:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1726_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckIdent___closed__2));
v___x_1727_ = l_Lean_stringToMessageData(v___x_1726_);
return v___x_1727_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckIdent___closed__6(void){
_start:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1731_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckIdent___closed__5));
v___x_1732_ = l_Lean_MessageData_ofFormat(v___x_1731_);
return v___x_1732_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckIdent___closed__7(void){
_start:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1733_ = lean_obj_once(&l_Lean_Elab_Term_Quotation_precheckIdent___closed__6, &l_Lean_Elab_Term_Quotation_precheckIdent___closed__6_once, _init_l_Lean_Elab_Term_Quotation_precheckIdent___closed__6);
v___x_1734_ = l_Lean_MessageData_note(v___x_1733_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckIdent(lean_object* v_stx_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_){
_start:
{
if (lean_obj_tag(v_stx_1735_) == 3)
{
lean_object* v_val_1744_; lean_object* v_preresolved_1745_; lean_object* v_a_1747_; lean_object* v___y_1784_; uint8_t v___x_1794_; 
v_val_1744_ = lean_ctor_get(v_stx_1735_, 2);
lean_inc(v_val_1744_);
v_preresolved_1745_ = lean_ctor_get(v_stx_1735_, 3);
v___x_1794_ = l_List_isEmpty___redArg(v_preresolved_1745_);
if (v___x_1794_ == 0)
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
lean_dec(v_val_1744_);
lean_dec_ref(v_stx_1735_);
v___x_1795_ = lean_box(0);
v___x_1796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1795_);
return v___x_1796_;
}
else
{
lean_object* v___x_1797_; 
lean_inc(v_val_1744_);
lean_inc_ref(v_stx_1735_);
v___x_1797_ = l_Lean_Elab_realizeGlobalNameWithInfos(v_stx_1735_, v_val_1744_, v_a_1741_, v_a_1742_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1819_; 
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1800_ = v___x_1797_;
v_isShared_1801_ = v_isSharedCheck_1819_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1797_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1819_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
if (lean_obj_tag(v_a_1798_) == 1)
{
lean_object* v___x_1802_; lean_object* v___x_1804_; 
lean_dec_ref(v_a_1798_);
lean_dec(v_val_1744_);
lean_dec_ref(v_stx_1735_);
v___x_1802_ = lean_box(0);
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 0, v___x_1802_);
v___x_1804_ = v___x_1800_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___x_1802_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
else
{
uint8_t v___x_1806_; 
lean_dec(v_a_1798_);
v___x_1806_ = l_Lean_NameSet_contains(v_a_1736_, v_val_1744_);
if (v___x_1806_ == 0)
{
lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
lean_del_object(v___x_1800_);
v___x_1807_ = lean_box(0);
v___x_1808_ = lean_box(0);
lean_inc(v_val_1744_);
v___x_1809_ = l_Lean_Elab_Term_resolveName(v_stx_1735_, v_val_1744_, v___x_1807_, v___x_1807_, v___x_1808_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_);
if (lean_obj_tag(v___x_1809_) == 0)
{
v___y_1784_ = v___x_1809_;
goto v___jp_1783_;
}
else
{
lean_object* v_a_1810_; uint8_t v___y_1812_; uint8_t v___x_1813_; 
v_a_1810_ = lean_ctor_get(v___x_1809_, 0);
lean_inc(v_a_1810_);
v___x_1813_ = l_Lean_Exception_isInterrupt(v_a_1810_);
if (v___x_1813_ == 0)
{
uint8_t v___x_1814_; 
v___x_1814_ = l_Lean_Exception_isRuntime(v_a_1810_);
v___y_1812_ = v___x_1814_;
goto v___jp_1811_;
}
else
{
lean_dec(v_a_1810_);
v___y_1812_ = v___x_1813_;
goto v___jp_1811_;
}
v___jp_1811_:
{
if (v___y_1812_ == 0)
{
lean_dec_ref(v___x_1809_);
v_a_1747_ = v___x_1807_;
goto v___jp_1746_;
}
else
{
v___y_1784_ = v___x_1809_;
goto v___jp_1783_;
}
}
}
}
else
{
lean_object* v___x_1815_; lean_object* v___x_1817_; 
lean_dec(v_val_1744_);
lean_dec_ref(v_stx_1735_);
v___x_1815_ = lean_box(0);
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 0, v___x_1815_);
v___x_1817_ = v___x_1800_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v___x_1815_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
}
}
else
{
lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1827_; 
lean_dec(v_val_1744_);
lean_dec_ref(v_stx_1735_);
v_a_1820_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1822_ = v___x_1797_;
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_dec(v___x_1797_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1825_; 
if (v_isShared_1823_ == 0)
{
v___x_1825_ = v___x_1822_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_a_1820_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
}
v___jp_1746_:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1748_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___closed__0));
v___x_1749_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg(v_a_1747_, v___x_1748_, v_a_1737_, v_a_1741_);
lean_dec(v_a_1747_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v_a_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1774_; 
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1752_ = v___x_1749_;
v_isShared_1753_ = v_isSharedCheck_1774_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_dec(v___x_1749_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1774_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v_fst_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1772_; 
v_fst_1754_ = lean_ctor_get(v_a_1750_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v_a_1750_);
if (v_isSharedCheck_1772_ == 0)
{
lean_object* v_unused_1773_; 
v_unused_1773_ = lean_ctor_get(v_a_1750_, 1);
lean_dec(v_unused_1773_);
v___x_1756_ = v_a_1750_;
v_isShared_1757_ = v_isSharedCheck_1772_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_fst_1754_);
lean_dec(v_a_1750_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1772_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
if (lean_obj_tag(v_fst_1754_) == 0)
{
lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1761_; 
lean_del_object(v___x_1752_);
v___x_1758_ = lean_obj_once(&l_Lean_Elab_Term_Quotation_precheckIdent___closed__1, &l_Lean_Elab_Term_Quotation_precheckIdent___closed__1_once, _init_l_Lean_Elab_Term_Quotation_precheckIdent___closed__1);
v___x_1759_ = l_Lean_MessageData_ofName(v_val_1744_);
if (v_isShared_1757_ == 0)
{
lean_ctor_set_tag(v___x_1756_, 7);
lean_ctor_set(v___x_1756_, 1, v___x_1759_);
lean_ctor_set(v___x_1756_, 0, v___x_1758_);
v___x_1761_ = v___x_1756_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1758_);
lean_ctor_set(v_reuseFailAlloc_1767_, 1, v___x_1759_);
v___x_1761_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1762_ = lean_obj_once(&l_Lean_Elab_Term_Quotation_precheckIdent___closed__3, &l_Lean_Elab_Term_Quotation_precheckIdent___closed__3_once, _init_l_Lean_Elab_Term_Quotation_precheckIdent___closed__3);
v___x_1763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1761_);
lean_ctor_set(v___x_1763_, 1, v___x_1762_);
v___x_1764_ = lean_obj_once(&l_Lean_Elab_Term_Quotation_precheckIdent___closed__7, &l_Lean_Elab_Term_Quotation_precheckIdent___closed__7_once, _init_l_Lean_Elab_Term_Quotation_precheckIdent___closed__7);
v___x_1765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1763_);
lean_ctor_set(v___x_1765_, 1, v___x_1764_);
v___x_1766_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1_spec__9___redArg(v___x_1765_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_);
return v___x_1766_;
}
}
else
{
lean_object* v_val_1768_; lean_object* v___x_1770_; 
lean_del_object(v___x_1756_);
lean_dec(v_val_1744_);
v_val_1768_ = lean_ctor_get(v_fst_1754_, 0);
lean_inc(v_val_1768_);
lean_dec_ref(v_fst_1754_);
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 0, v_val_1768_);
v___x_1770_ = v___x_1752_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_val_1768_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
}
}
else
{
lean_object* v_a_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1782_; 
lean_dec(v_val_1744_);
v_a_1775_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1777_ = v___x_1749_;
v_isShared_1778_ = v_isSharedCheck_1782_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_a_1775_);
lean_dec(v___x_1749_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1782_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1780_; 
if (v_isShared_1778_ == 0)
{
v___x_1780_ = v___x_1777_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_a_1775_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
return v___x_1780_;
}
}
}
}
v___jp_1783_:
{
if (lean_obj_tag(v___y_1784_) == 0)
{
lean_object* v_a_1785_; 
v_a_1785_ = lean_ctor_get(v___y_1784_, 0);
lean_inc(v_a_1785_);
lean_dec_ref(v___y_1784_);
v_a_1747_ = v_a_1785_;
goto v___jp_1746_;
}
else
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
lean_dec(v_val_1744_);
v_a_1786_ = lean_ctor_get(v___y_1784_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___y_1784_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1788_ = v___y_1784_;
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___y_1784_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
if (v_isShared_1789_ == 0)
{
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_a_1786_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
}
}
else
{
lean_object* v___x_1828_; 
lean_dec(v_stx_1735_);
v___x_1828_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__7___redArg();
return v___x_1828_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___boxed(lean_object* v_stx_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l_Lean_Elab_Term_Quotation_precheckIdent(v_stx_1829_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_);
lean_dec(v_a_1836_);
lean_dec_ref(v_a_1835_);
lean_dec(v_a_1834_);
lean_dec_ref(v_a_1833_);
lean_dec(v_a_1832_);
lean_dec_ref(v_a_1831_);
lean_dec(v_a_1830_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0(lean_object* v_as_1839_, lean_object* v_as_x27_1840_, lean_object* v_b_1841_, lean_object* v_a_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
lean_object* v___x_1851_; 
v___x_1851_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg(v_as_x27_1840_, v_b_1841_, v___y_1844_, v___y_1848_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___boxed(lean_object* v_as_1852_, lean_object* v_as_x27_1853_, lean_object* v_b_1854_, lean_object* v_a_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0(v_as_1852_, v_as_x27_1853_, v_b_1854_, v_a_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec(v_as_x27_1853_);
lean_dec(v_as_1852_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1(){
_start:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1876_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
v___x_1877_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__1));
v___x_1878_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__3));
v___x_1879_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckIdent___boxed), 9, 0);
v___x_1880_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1876_, v___x_1877_, v___x_1878_, v___x_1879_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___boxed(lean_object* v_a_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1();
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0(lean_object* v_as_1896_, size_t v_sz_1897_, size_t v_i_1898_, lean_object* v_b_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_){
_start:
{
lean_object* v_a_1909_; uint8_t v___x_1913_; 
v___x_1913_ = lean_usize_dec_lt(v_i_1898_, v_sz_1897_);
if (v___x_1913_ == 0)
{
lean_object* v___x_1914_; 
v___x_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1914_, 0, v_b_1899_);
return v___x_1914_;
}
else
{
lean_object* v___x_1915_; lean_object* v_a_1916_; lean_object* v___x_1917_; uint8_t v___x_1918_; 
v___x_1915_ = lean_box(0);
v_a_1916_ = lean_array_uget_borrowed(v_as_1896_, v_i_1898_);
v___x_1917_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__2));
lean_inc(v_a_1916_);
v___x_1918_ = l_Lean_Syntax_isOfKind(v_a_1916_, v___x_1917_);
if (v___x_1918_ == 0)
{
lean_object* v___x_1919_; uint8_t v___x_1920_; 
v___x_1919_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__4));
lean_inc(v_a_1916_);
v___x_1920_ = l_Lean_Syntax_isOfKind(v_a_1916_, v___x_1919_);
if (v___x_1920_ == 0)
{
lean_object* v___x_1921_; 
lean_inc(v_a_1916_);
v___x_1921_ = l_Lean_Elab_Term_Quotation_precheck(v_a_1916_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_);
if (lean_obj_tag(v___x_1921_) == 0)
{
lean_dec_ref(v___x_1921_);
v_a_1909_ = v___x_1915_;
goto v___jp_1908_;
}
else
{
return v___x_1921_;
}
}
else
{
v_a_1909_ = v___x_1915_;
goto v___jp_1908_;
}
}
else
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1922_ = lean_unsigned_to_nat(3u);
v___x_1923_ = l_Lean_Syntax_getArg(v_a_1916_, v___x_1922_);
v___x_1924_ = l_Lean_Elab_Term_Quotation_precheck(v___x_1923_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_dec_ref(v___x_1924_);
v_a_1909_ = v___x_1915_;
goto v___jp_1908_;
}
else
{
return v___x_1924_;
}
}
}
v___jp_1908_:
{
size_t v___x_1910_; size_t v___x_1911_; 
v___x_1910_ = ((size_t)1ULL);
v___x_1911_ = lean_usize_add(v_i_1898_, v___x_1910_);
v_i_1898_ = v___x_1911_;
v_b_1899_ = v_a_1909_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___boxed(lean_object* v_as_1925_, lean_object* v_sz_1926_, lean_object* v_i_1927_, lean_object* v_b_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_){
_start:
{
size_t v_sz_boxed_1937_; size_t v_i_boxed_1938_; lean_object* v_res_1939_; 
v_sz_boxed_1937_ = lean_unbox_usize(v_sz_1926_);
lean_dec(v_sz_1926_);
v_i_boxed_1938_ = lean_unbox_usize(v_i_1927_);
lean_dec(v_i_1927_);
v_res_1939_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0(v_as_1925_, v_sz_boxed_1937_, v_i_boxed_1938_, v_b_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
lean_dec(v___y_1929_);
lean_dec_ref(v_as_1925_);
return v_res_1939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckApp(lean_object* v_x_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_){
_start:
{
lean_object* v___x_1955_; uint8_t v___x_1956_; 
v___x_1955_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckApp___closed__1));
lean_inc(v_x_1946_);
v___x_1956_ = l_Lean_Syntax_isOfKind(v_x_1946_, v___x_1955_);
if (v___x_1956_ == 0)
{
lean_object* v___x_1957_; 
lean_dec(v_x_1946_);
v___x_1957_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__7___redArg();
return v___x_1957_;
}
else
{
lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1958_ = lean_unsigned_to_nat(0u);
v___x_1959_ = l_Lean_Syntax_getArg(v_x_1946_, v___x_1958_);
v___x_1960_ = l_Lean_Elab_Term_Quotation_precheck(v___x_1959_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_);
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v_args_1963_; lean_object* v___x_1964_; size_t v_sz_1965_; size_t v___x_1966_; lean_object* v___x_1967_; 
lean_dec_ref(v___x_1960_);
v___x_1961_ = lean_unsigned_to_nat(1u);
v___x_1962_ = l_Lean_Syntax_getArg(v_x_1946_, v___x_1961_);
lean_dec(v_x_1946_);
v_args_1963_ = l_Lean_Syntax_getArgs(v___x_1962_);
lean_dec(v___x_1962_);
v___x_1964_ = lean_box(0);
v_sz_1965_ = lean_array_size(v_args_1963_);
v___x_1966_ = ((size_t)0ULL);
v___x_1967_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0(v_args_1963_, v_sz_1965_, v___x_1966_, v___x_1964_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_);
lean_dec_ref(v_args_1963_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1974_; 
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_1974_ == 0)
{
lean_object* v_unused_1975_; 
v_unused_1975_ = lean_ctor_get(v___x_1967_, 0);
lean_dec(v_unused_1975_);
v___x_1969_ = v___x_1967_;
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
else
{
lean_dec(v___x_1967_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1972_; 
if (v_isShared_1970_ == 0)
{
lean_ctor_set(v___x_1969_, 0, v___x_1964_);
v___x_1972_ = v___x_1969_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v___x_1964_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
else
{
return v___x_1967_;
}
}
else
{
lean_dec(v_x_1946_);
return v___x_1960_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckApp___boxed(lean_object* v_x_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = l_Lean_Elab_Term_Quotation_precheckApp(v_x_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_);
lean_dec(v_a_1983_);
lean_dec_ref(v_a_1982_);
lean_dec(v_a_1981_);
lean_dec_ref(v_a_1980_);
lean_dec(v_a_1979_);
lean_dec_ref(v_a_1978_);
lean_dec(v_a_1977_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1(){
_start:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1994_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
v___x_1995_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckApp___closed__1));
v___x_1996_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__1));
v___x_1997_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckApp___boxed), 9, 0);
v___x_1998_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1994_, v___x_1995_, v___x_1996_, v___x_1997_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___boxed(lean_object* v_a_1999_){
_start:
{
lean_object* v_res_2000_; 
v_res_2000_ = l_Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1();
return v_res_2000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckTypeAscription(lean_object* v_x_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_){
_start:
{
lean_object* v___x_2022_; uint8_t v___x_2023_; 
v___x_2022_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__1));
lean_inc(v_x_2013_);
v___x_2023_ = l_Lean_Syntax_isOfKind(v_x_2013_, v___x_2022_);
if (v___x_2023_ == 0)
{
lean_object* v___x_2024_; 
lean_dec(v_x_2013_);
v___x_2024_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__7___redArg();
return v___x_2024_;
}
else
{
lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; uint8_t v___x_2028_; 
v___x_2025_ = lean_unsigned_to_nat(0u);
v___x_2026_ = l_Lean_Syntax_getArg(v_x_2013_, v___x_2025_);
v___x_2027_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__3));
lean_inc(v___x_2026_);
v___x_2028_ = l_Lean_Syntax_isOfKind(v___x_2026_, v___x_2027_);
if (v___x_2028_ == 0)
{
lean_object* v___x_2029_; 
lean_dec(v___x_2026_);
lean_dec(v_x_2013_);
v___x_2029_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__7___redArg();
return v___x_2029_;
}
else
{
lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; uint8_t v___x_2033_; 
v___x_2030_ = lean_unsigned_to_nat(1u);
v___x_2031_ = l_Lean_Syntax_getArg(v___x_2026_, v___x_2030_);
lean_dec(v___x_2026_);
v___x_2032_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___closed__1));
lean_inc(v___x_2031_);
v___x_2033_ = l_Lean_Syntax_isOfKind(v___x_2031_, v___x_2032_);
if (v___x_2033_ == 0)
{
lean_object* v___x_2034_; 
lean_dec(v___x_2031_);
lean_dec(v_x_2013_);
v___x_2034_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__7___redArg();
return v___x_2034_;
}
else
{
lean_object* v___x_2035_; lean_object* v___x_2036_; uint8_t v___x_2037_; 
v___x_2035_ = l_Lean_Syntax_getArg(v___x_2031_, v___x_2025_);
lean_dec(v___x_2031_);
v___x_2036_ = lean_box(0);
v___x_2037_ = l_Lean_Syntax_matchesIdent(v___x_2035_, v___x_2036_);
lean_dec(v___x_2035_);
if (v___x_2037_ == 0)
{
lean_object* v___x_2038_; 
lean_dec(v_x_2013_);
v___x_2038_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__7___redArg();
return v___x_2038_;
}
else
{
lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; uint8_t v___x_2042_; 
v___x_2039_ = l_Lean_Syntax_getArg(v_x_2013_, v___x_2030_);
v___x_2040_ = lean_unsigned_to_nat(3u);
v___x_2041_ = l_Lean_Syntax_getArg(v_x_2013_, v___x_2040_);
lean_dec(v_x_2013_);
lean_inc(v___x_2041_);
v___x_2042_ = l_Lean_Syntax_matchesNull(v___x_2041_, v___x_2030_);
if (v___x_2042_ == 0)
{
uint8_t v___x_2043_; 
v___x_2043_ = l_Lean_Syntax_matchesNull(v___x_2041_, v___x_2025_);
if (v___x_2043_ == 0)
{
lean_object* v___x_2044_; 
lean_dec(v___x_2039_);
v___x_2044_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__7___redArg();
return v___x_2044_;
}
else
{
lean_object* v___x_2045_; 
v___x_2045_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2039_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_);
return v___x_2045_;
}
}
else
{
lean_object* v___x_2046_; 
v___x_2046_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2039_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v___x_2047_; lean_object* v___x_2048_; 
lean_dec_ref(v___x_2046_);
v___x_2047_ = l_Lean_Syntax_getArg(v___x_2041_, v___x_2025_);
lean_dec(v___x_2041_);
v___x_2048_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2047_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_);
return v___x_2048_;
}
else
{
lean_dec(v___x_2041_);
return v___x_2046_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckTypeAscription___boxed(lean_object* v_x_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_){
_start:
{
lean_object* v_res_2058_; 
v_res_2058_ = l_Lean_Elab_Term_Quotation_precheckTypeAscription(v_x_2049_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_);
lean_dec(v_a_2056_);
lean_dec_ref(v_a_2055_);
lean_dec(v_a_2054_);
lean_dec_ref(v_a_2053_);
lean_dec(v_a_2052_);
lean_dec_ref(v_a_2051_);
lean_dec(v_a_2050_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1(){
_start:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2067_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
v___x_2068_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__1));
v___x_2069_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__1));
v___x_2070_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckTypeAscription___boxed), 9, 0);
v___x_2071_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2067_, v___x_2068_, v___x_2069_, v___x_2070_);
return v___x_2071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___boxed(lean_object* v_a_2072_){
_start:
{
lean_object* v_res_2073_; 
v_res_2073_ = l_Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1();
return v_res_2073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckExplicit(lean_object* v_x_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_){
_start:
{
lean_object* v___x_2089_; uint8_t v___x_2090_; 
v___x_2089_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckExplicit___closed__1));
lean_inc(v_x_2080_);
v___x_2090_ = l_Lean_Syntax_isOfKind(v_x_2080_, v___x_2089_);
if (v___x_2090_ == 0)
{
lean_object* v___x_2091_; 
lean_dec(v_x_2080_);
v___x_2091_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__7___redArg();
return v___x_2091_;
}
else
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2092_ = lean_unsigned_to_nat(1u);
v___x_2093_ = l_Lean_Syntax_getArg(v_x_2080_, v___x_2092_);
lean_dec(v_x_2080_);
v___x_2094_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2093_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_);
return v___x_2094_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckExplicit___boxed(lean_object* v_x_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_){
_start:
{
lean_object* v_res_2104_; 
v_res_2104_ = l_Lean_Elab_Term_Quotation_precheckExplicit(v_x_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
lean_dec(v_a_2102_);
lean_dec_ref(v_a_2101_);
lean_dec(v_a_2100_);
lean_dec_ref(v_a_2099_);
lean_dec(v_a_2098_);
lean_dec_ref(v_a_2097_);
lean_dec(v_a_2096_);
return v_res_2104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1(){
_start:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2113_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
v___x_2114_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckExplicit___closed__1));
v___x_2115_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__1));
v___x_2116_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckExplicit___boxed), 9, 0);
v___x_2117_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2113_, v___x_2114_, v___x_2115_, v___x_2116_);
return v___x_2117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___boxed(lean_object* v_a_2118_){
_start:
{
lean_object* v_res_2119_; 
v_res_2119_ = l_Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1();
return v_res_2119_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2121_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1___closed__0));
v___x_2122_ = l_Lean_stringToMessageData(v___x_2121_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1(lean_object* v_as_2123_, size_t v_i_2124_, size_t v_stop_2125_, lean_object* v_b_2126_){
_start:
{
lean_object* v___y_2128_; uint8_t v___x_2132_; 
v___x_2132_ = lean_usize_dec_eq(v_i_2124_, v_stop_2125_);
if (v___x_2132_ == 0)
{
lean_object* v___x_2133_; lean_object* v_fst_2134_; 
v___x_2133_ = lean_array_uget(v_as_2123_, v_i_2124_);
v_fst_2134_ = lean_ctor_get(v___x_2133_, 0);
lean_inc(v_fst_2134_);
if (lean_obj_tag(v_fst_2134_) == 0)
{
lean_object* v_snd_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2148_; 
v_snd_2135_ = lean_ctor_get(v___x_2133_, 1);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2148_ == 0)
{
lean_object* v_unused_2149_; 
v_unused_2149_ = lean_ctor_get(v___x_2133_, 0);
lean_dec(v_unused_2149_);
v___x_2137_ = v___x_2133_;
v_isShared_2138_ = v_isSharedCheck_2148_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_snd_2135_);
lean_dec(v___x_2133_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2148_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v_a_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2143_; 
v_a_2139_ = lean_ctor_get(v_fst_2134_, 0);
lean_inc(v_a_2139_);
lean_dec_ref(v_fst_2134_);
v___x_2140_ = l_Lean_MessageData_ofSyntax(v_snd_2135_);
v___x_2141_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1___closed__1);
if (v_isShared_2138_ == 0)
{
lean_ctor_set_tag(v___x_2137_, 7);
lean_ctor_set(v___x_2137_, 1, v___x_2141_);
lean_ctor_set(v___x_2137_, 0, v___x_2140_);
v___x_2143_ = v___x_2137_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v___x_2140_);
lean_ctor_set(v_reuseFailAlloc_2147_, 1, v___x_2141_);
v___x_2143_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2144_ = l_Lean_Exception_toMessageData(v_a_2139_);
v___x_2145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2143_);
lean_ctor_set(v___x_2145_, 1, v___x_2144_);
v___x_2146_ = lean_array_push(v_b_2126_, v___x_2145_);
v___y_2128_ = v___x_2146_;
goto v___jp_2127_;
}
}
}
else
{
lean_dec(v_fst_2134_);
lean_dec(v___x_2133_);
v___y_2128_ = v_b_2126_;
goto v___jp_2127_;
}
}
else
{
return v_b_2126_;
}
v___jp_2127_:
{
size_t v___x_2129_; size_t v___x_2130_; 
v___x_2129_ = ((size_t)1ULL);
v___x_2130_ = lean_usize_add(v_i_2124_, v___x_2129_);
v_i_2124_ = v___x_2130_;
v_b_2126_ = v___y_2128_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1___boxed(lean_object* v_as_2150_, lean_object* v_i_2151_, lean_object* v_stop_2152_, lean_object* v_b_2153_){
_start:
{
size_t v_i_boxed_2154_; size_t v_stop_boxed_2155_; lean_object* v_res_2156_; 
v_i_boxed_2154_ = lean_unbox_usize(v_i_2151_);
lean_dec(v_i_2151_);
v_stop_boxed_2155_ = lean_unbox_usize(v_stop_2152_);
lean_dec(v_stop_2152_);
v_res_2156_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1(v_as_2150_, v_i_boxed_2154_, v_stop_boxed_2155_, v_b_2153_);
lean_dec_ref(v_as_2150_);
return v_res_2156_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1(lean_object* v_as_2157_, lean_object* v_start_2158_, lean_object* v_stop_2159_){
_start:
{
lean_object* v___x_2160_; uint8_t v___x_2161_; 
v___x_2160_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___redArg___closed__2));
v___x_2161_ = lean_nat_dec_lt(v_start_2158_, v_stop_2159_);
if (v___x_2161_ == 0)
{
return v___x_2160_;
}
else
{
lean_object* v___x_2162_; uint8_t v___x_2163_; 
v___x_2162_ = lean_array_get_size(v_as_2157_);
v___x_2163_ = lean_nat_dec_le(v_stop_2159_, v___x_2162_);
if (v___x_2163_ == 0)
{
uint8_t v___x_2164_; 
v___x_2164_ = lean_nat_dec_lt(v_start_2158_, v___x_2162_);
if (v___x_2164_ == 0)
{
return v___x_2160_;
}
else
{
size_t v___x_2165_; size_t v___x_2166_; lean_object* v___x_2167_; 
v___x_2165_ = lean_usize_of_nat(v_start_2158_);
v___x_2166_ = lean_usize_of_nat(v___x_2162_);
v___x_2167_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1(v_as_2157_, v___x_2165_, v___x_2166_, v___x_2160_);
return v___x_2167_;
}
}
else
{
size_t v___x_2168_; size_t v___x_2169_; lean_object* v___x_2170_; 
v___x_2168_ = lean_usize_of_nat(v_start_2158_);
v___x_2169_ = lean_usize_of_nat(v_stop_2159_);
v___x_2170_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1(v_as_2157_, v___x_2168_, v___x_2169_, v___x_2160_);
return v___x_2170_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1___boxed(lean_object* v_as_2171_, lean_object* v_start_2172_, lean_object* v_stop_2173_){
_start:
{
lean_object* v_res_2174_; 
v_res_2174_ = l_Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1(v_as_2171_, v_start_2172_, v_stop_2173_);
lean_dec(v_stop_2173_);
lean_dec(v_start_2172_);
lean_dec_ref(v_as_2171_);
return v_res_2174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__0(size_t v_sz_2175_, size_t v_i_2176_, lean_object* v_bs_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_){
_start:
{
uint8_t v___x_2186_; 
v___x_2186_ = lean_usize_dec_lt(v_i_2176_, v_sz_2175_);
if (v___x_2186_ == 0)
{
lean_object* v___x_2187_; 
v___x_2187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2187_, 0, v_bs_2177_);
return v___x_2187_;
}
else
{
lean_object* v_v_2188_; lean_object* v___x_2189_; lean_object* v_bs_x27_2190_; lean_object* v_a_2192_; lean_object* v___x_2197_; 
v_v_2188_ = lean_array_uget(v_bs_2177_, v_i_2176_);
v___x_2189_ = lean_unsigned_to_nat(0u);
v_bs_x27_2190_ = lean_array_uset(v_bs_2177_, v_i_2176_, v___x_2189_);
v___x_2197_ = l_Lean_Elab_Term_Quotation_precheck(v_v_2188_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_);
if (lean_obj_tag(v___x_2197_) == 0)
{
lean_object* v_a_2198_; lean_object* v___x_2199_; 
v_a_2198_ = lean_ctor_get(v___x_2197_, 0);
lean_inc(v_a_2198_);
lean_dec_ref(v___x_2197_);
v___x_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2199_, 0, v_a_2198_);
v_a_2192_ = v___x_2199_;
goto v___jp_2191_;
}
else
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2212_; 
v_a_2200_ = lean_ctor_get(v___x_2197_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2202_ = v___x_2197_;
v_isShared_2203_ = v_isSharedCheck_2212_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2197_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2212_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
uint8_t v___y_2205_; uint8_t v___x_2210_; 
v___x_2210_ = l_Lean_Exception_isInterrupt(v_a_2200_);
if (v___x_2210_ == 0)
{
uint8_t v___x_2211_; 
lean_inc(v_a_2200_);
v___x_2211_ = l_Lean_Exception_isRuntime(v_a_2200_);
v___y_2205_ = v___x_2211_;
goto v___jp_2204_;
}
else
{
v___y_2205_ = v___x_2210_;
goto v___jp_2204_;
}
v___jp_2204_:
{
if (v___y_2205_ == 0)
{
lean_object* v___x_2206_; 
lean_del_object(v___x_2202_);
v___x_2206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2206_, 0, v_a_2200_);
v_a_2192_ = v___x_2206_;
goto v___jp_2191_;
}
else
{
lean_object* v___x_2208_; 
lean_dec_ref(v_bs_x27_2190_);
if (v_isShared_2203_ == 0)
{
v___x_2208_ = v___x_2202_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_a_2200_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
}
}
}
v___jp_2191_:
{
size_t v___x_2193_; size_t v___x_2194_; lean_object* v___x_2195_; 
v___x_2193_ = ((size_t)1ULL);
v___x_2194_ = lean_usize_add(v_i_2176_, v___x_2193_);
v___x_2195_ = lean_array_uset(v_bs_x27_2190_, v_i_2176_, v_a_2192_);
v_i_2176_ = v___x_2194_;
v_bs_2177_ = v___x_2195_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__0___boxed(lean_object* v_sz_2213_, lean_object* v_i_2214_, lean_object* v_bs_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_){
_start:
{
size_t v_sz_boxed_2224_; size_t v_i_boxed_2225_; lean_object* v_res_2226_; 
v_sz_boxed_2224_ = lean_unbox_usize(v_sz_2213_);
lean_dec(v_sz_2213_);
v_i_boxed_2225_ = lean_unbox_usize(v_i_2214_);
lean_dec(v_i_2214_);
v_res_2226_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__0(v_sz_boxed_2224_, v_i_boxed_2225_, v_bs_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_);
lean_dec(v___y_2222_);
lean_dec_ref(v___y_2221_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec(v___y_2216_);
return v_res_2226_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckChoice___closed__1(void){
_start:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2228_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckChoice___closed__0));
v___x_2229_ = l_Lean_stringToMessageData(v___x_2228_);
return v___x_2229_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckChoice___closed__3(void){
_start:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2231_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckChoice___closed__2));
v___x_2232_ = l_Lean_stringToMessageData(v___x_2231_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckChoice(lean_object* v_stx_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_){
_start:
{
lean_object* v___x_2242_; size_t v_sz_2243_; size_t v___x_2244_; lean_object* v___x_2245_; 
v___x_2242_ = l_Lean_Syntax_getArgs(v_stx_2233_);
v_sz_2243_ = lean_array_size(v___x_2242_);
v___x_2244_ = ((size_t)0ULL);
lean_inc_ref(v___x_2242_);
v___x_2245_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__0(v_sz_2243_, v___x_2244_, v___x_2242_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_);
if (lean_obj_tag(v___x_2245_) == 0)
{
lean_object* v_a_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2267_; 
v_a_2246_ = lean_ctor_get(v___x_2245_, 0);
v_isSharedCheck_2267_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2248_ = v___x_2245_;
v_isShared_2249_ = v_isSharedCheck_2267_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_a_2246_);
lean_dec(v___x_2245_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2267_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; uint8_t v___x_2255_; 
v___x_2250_ = l_Array_zip___redArg(v_a_2246_, v___x_2242_);
lean_dec_ref(v___x_2242_);
lean_dec(v_a_2246_);
v___x_2251_ = lean_unsigned_to_nat(0u);
v___x_2252_ = lean_array_get_size(v___x_2250_);
v___x_2253_ = l_Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1(v___x_2250_, v___x_2251_, v___x_2252_);
lean_dec_ref(v___x_2250_);
v___x_2254_ = lean_array_get_size(v___x_2253_);
v___x_2255_ = lean_nat_dec_eq(v___x_2254_, v___x_2251_);
if (v___x_2255_ == 0)
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
lean_del_object(v___x_2248_);
v___x_2256_ = lean_obj_once(&l_Lean_Elab_Term_Quotation_precheckChoice___closed__1, &l_Lean_Elab_Term_Quotation_precheckChoice___closed__1_once, _init_l_Lean_Elab_Term_Quotation_precheckChoice___closed__1);
v___x_2257_ = lean_array_to_list(v___x_2253_);
v___x_2258_ = lean_obj_once(&l_Lean_Elab_Term_Quotation_precheckChoice___closed__3, &l_Lean_Elab_Term_Quotation_precheckChoice___closed__3_once, _init_l_Lean_Elab_Term_Quotation_precheckChoice___closed__3);
v___x_2259_ = l_Lean_MessageData_joinSep(v___x_2257_, v___x_2258_);
v___x_2260_ = l_Lean_indentD(v___x_2259_);
v___x_2261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2256_);
lean_ctor_set(v___x_2261_, 1, v___x_2260_);
v___x_2262_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1___redArg(v_stx_2233_, v___x_2261_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_);
return v___x_2262_;
}
else
{
lean_object* v___x_2263_; lean_object* v___x_2265_; 
lean_dec_ref(v___x_2253_);
v___x_2263_ = lean_box(0);
if (v_isShared_2249_ == 0)
{
lean_ctor_set(v___x_2248_, 0, v___x_2263_);
v___x_2265_ = v___x_2248_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v___x_2263_);
v___x_2265_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
return v___x_2265_;
}
}
}
}
else
{
lean_object* v_a_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2275_; 
lean_dec_ref(v___x_2242_);
v_a_2268_ = lean_ctor_get(v___x_2245_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2270_ = v___x_2245_;
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_a_2268_);
lean_dec(v___x_2245_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2273_; 
if (v_isShared_2271_ == 0)
{
v___x_2273_ = v___x_2270_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_a_2268_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckChoice___boxed(lean_object* v_stx_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_){
_start:
{
lean_object* v_res_2285_; 
v_res_2285_ = l_Lean_Elab_Term_Quotation_precheckChoice(v_stx_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
lean_dec(v_a_2283_);
lean_dec_ref(v_a_2282_);
lean_dec(v_a_2281_);
lean_dec_ref(v_a_2280_);
lean_dec(v_a_2279_);
lean_dec_ref(v_a_2278_);
lean_dec(v_a_2277_);
lean_dec(v_stx_2276_);
return v_res_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1(){
_start:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2297_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
v___x_2298_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__1));
v___x_2299_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__3));
v___x_2300_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckChoice___boxed), 9, 0);
v___x_2301_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2297_, v___x_2298_, v___x_2299_, v___x_2300_);
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___boxed(lean_object* v_a_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l_Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1();
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___lam__0(lean_object* v_singleQuot_2304_, lean_object* v_x_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
lean_object* v___x_2313_; 
v___x_2313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2313_, 0, v_singleQuot_2304_);
return v___x_2313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___lam__0___boxed(lean_object* v_singleQuot_2314_, lean_object* v_x_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_){
_start:
{
lean_object* v_res_2323_; 
v_res_2323_ = l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___lam__0(v_singleQuot_2314_, v_x_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
lean_dec(v_x_2315_);
return v_res_2323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot(lean_object* v_stx_2324_, lean_object* v_expectedType_x3f_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_){
_start:
{
lean_object* v___x_2333_; lean_object* v_singleQuot_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2333_ = lean_unsigned_to_nat(1u);
v_singleQuot_2334_ = l_Lean_Syntax_getArg(v_stx_2324_, v___x_2333_);
lean_inc(v_singleQuot_2334_);
v___x_2335_ = l_Lean_Syntax_getQuotContent(v_singleQuot_2334_);
v___x_2336_ = l_Lean_Elab_Term_Quotation_runPrecheck(v___x_2335_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v___f_2337_; lean_object* v___x_2338_; 
lean_dec_ref(v___x_2336_);
v___f_2337_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___lam__0___boxed), 9, 1);
lean_closure_set(v___f_2337_, 0, v_singleQuot_2334_);
v___x_2338_ = l_Lean_Elab_Term_adaptExpander(v___f_2337_, v_stx_2324_, v_expectedType_x3f_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_);
return v___x_2338_;
}
else
{
lean_object* v_a_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2346_; 
lean_dec(v_singleQuot_2334_);
lean_dec(v_expectedType_x3f_2325_);
lean_dec(v_stx_2324_);
v_a_2339_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2346_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2341_ = v___x_2336_;
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_a_2339_);
lean_dec(v___x_2336_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v___x_2344_; 
if (v_isShared_2342_ == 0)
{
v___x_2344_ = v___x_2341_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_a_2339_);
v___x_2344_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
return v___x_2344_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___boxed(lean_object* v_stx_2347_, lean_object* v_expectedType_x3f_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_){
_start:
{
lean_object* v_res_2356_; 
v_res_2356_ = l_Lean_Elab_Term_Quotation_elabPrecheckedQuot(v_stx_2347_, v_expectedType_x3f_2348_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_);
lean_dec(v_a_2354_);
lean_dec_ref(v_a_2353_);
lean_dec(v_a_2352_);
lean_dec_ref(v_a_2351_);
lean_dec(v_a_2350_);
lean_dec_ref(v_a_2349_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1(){
_start:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2371_ = l_Lean_Elab_Term_termElabAttribute;
v___x_2372_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__1));
v___x_2373_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3));
v___x_2374_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___boxed), 9, 0);
v___x_2375_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2371_, v___x_2372_, v___x_2373_, v___x_2374_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___boxed(lean_object* v_a_2376_){
_start:
{
lean_object* v_res_2377_; 
v_res_2377_ = l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1();
return v_res_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3(){
_start:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2404_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3));
v___x_2405_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__6));
v___x_2406_ = l_Lean_addBuiltinDeclarationRanges(v___x_2404_, v___x_2405_);
return v___x_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___boxed(lean_object* v_a_2407_){
_start:
{
lean_object* v_res_2408_; 
v_res_2408_ = l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3();
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinrel(lean_object* v_x_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_){
_start:
{
lean_object* v___x_2424_; uint8_t v___x_2425_; 
v___x_2424_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckBinrel___closed__1));
lean_inc(v_x_2415_);
v___x_2425_ = l_Lean_Syntax_isOfKind(v_x_2415_, v___x_2424_);
if (v___x_2425_ == 0)
{
lean_object* v___x_2426_; 
lean_dec(v_x_2415_);
v___x_2426_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__7___redArg();
return v___x_2426_;
}
else
{
lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2427_ = lean_unsigned_to_nat(1u);
v___x_2428_ = l_Lean_Syntax_getArg(v_x_2415_, v___x_2427_);
v___x_2429_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2428_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_);
if (lean_obj_tag(v___x_2429_) == 0)
{
lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; 
lean_dec_ref(v___x_2429_);
v___x_2430_ = lean_unsigned_to_nat(2u);
v___x_2431_ = l_Lean_Syntax_getArg(v_x_2415_, v___x_2430_);
v___x_2432_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2431_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_);
if (lean_obj_tag(v___x_2432_) == 0)
{
lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; 
lean_dec_ref(v___x_2432_);
v___x_2433_ = lean_unsigned_to_nat(3u);
v___x_2434_ = l_Lean_Syntax_getArg(v_x_2415_, v___x_2433_);
lean_dec(v_x_2415_);
v___x_2435_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2434_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_);
return v___x_2435_;
}
else
{
lean_dec(v_x_2415_);
return v___x_2432_;
}
}
else
{
lean_dec(v_x_2415_);
return v___x_2429_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinrel___boxed(lean_object* v_x_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_){
_start:
{
lean_object* v_res_2445_; 
v_res_2445_ = l_Lean_Elab_Term_Quotation_precheckBinrel(v_x_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_);
lean_dec(v_a_2443_);
lean_dec_ref(v_a_2442_);
lean_dec(v_a_2441_);
lean_dec_ref(v_a_2440_);
lean_dec(v_a_2439_);
lean_dec_ref(v_a_2438_);
lean_dec(v_a_2437_);
return v_res_2445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1(){
_start:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2454_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
v___x_2455_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckBinrel___closed__1));
v___x_2456_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__1));
v___x_2457_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckBinrel___boxed), 9, 0);
v___x_2458_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2454_, v___x_2455_, v___x_2456_, v___x_2457_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___boxed(lean_object* v_a_2459_){
_start:
{
lean_object* v_res_2460_; 
v_res_2460_ = l_Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1();
return v_res_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinrelNoProp(lean_object* v_x_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_){
_start:
{
lean_object* v___x_2476_; uint8_t v___x_2477_; 
v___x_2476_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__1));
lean_inc(v_x_2467_);
v___x_2477_ = l_Lean_Syntax_isOfKind(v_x_2467_, v___x_2476_);
if (v___x_2477_ == 0)
{
lean_object* v___x_2478_; 
lean_dec(v_x_2467_);
v___x_2478_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__7___redArg();
return v___x_2478_;
}
else
{
lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
v___x_2479_ = lean_unsigned_to_nat(1u);
v___x_2480_ = l_Lean_Syntax_getArg(v_x_2467_, v___x_2479_);
v___x_2481_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2480_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_);
if (lean_obj_tag(v___x_2481_) == 0)
{
lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; 
lean_dec_ref(v___x_2481_);
v___x_2482_ = lean_unsigned_to_nat(2u);
v___x_2483_ = l_Lean_Syntax_getArg(v_x_2467_, v___x_2482_);
v___x_2484_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2483_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_);
if (lean_obj_tag(v___x_2484_) == 0)
{
lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; 
lean_dec_ref(v___x_2484_);
v___x_2485_ = lean_unsigned_to_nat(3u);
v___x_2486_ = l_Lean_Syntax_getArg(v_x_2467_, v___x_2485_);
lean_dec(v_x_2467_);
v___x_2487_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2486_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_);
return v___x_2487_;
}
else
{
lean_dec(v_x_2467_);
return v___x_2484_;
}
}
else
{
lean_dec(v_x_2467_);
return v___x_2481_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___boxed(lean_object* v_x_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_){
_start:
{
lean_object* v_res_2497_; 
v_res_2497_ = l_Lean_Elab_Term_Quotation_precheckBinrelNoProp(v_x_2488_, v_a_2489_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_);
lean_dec(v_a_2495_);
lean_dec_ref(v_a_2494_);
lean_dec(v_a_2493_);
lean_dec_ref(v_a_2492_);
lean_dec(v_a_2491_);
lean_dec_ref(v_a_2490_);
lean_dec(v_a_2489_);
return v_res_2497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1(){
_start:
{
lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; 
v___x_2506_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
v___x_2507_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__1));
v___x_2508_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__1));
v___x_2509_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___boxed), 9, 0);
v___x_2510_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2506_, v___x_2507_, v___x_2508_, v___x_2509_);
return v___x_2510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___boxed(lean_object* v_a_2511_){
_start:
{
lean_object* v_res_2512_; 
v_res_2512_ = l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1();
return v_res_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinop(lean_object* v_x_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_){
_start:
{
lean_object* v___x_2528_; uint8_t v___x_2529_; 
v___x_2528_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckBinop___closed__1));
lean_inc(v_x_2519_);
v___x_2529_ = l_Lean_Syntax_isOfKind(v_x_2519_, v___x_2528_);
if (v___x_2529_ == 0)
{
lean_object* v___x_2530_; 
lean_dec(v_x_2519_);
v___x_2530_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__7___redArg();
return v___x_2530_;
}
else
{
lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2531_ = lean_unsigned_to_nat(1u);
v___x_2532_ = l_Lean_Syntax_getArg(v_x_2519_, v___x_2531_);
v___x_2533_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2532_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_);
if (lean_obj_tag(v___x_2533_) == 0)
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
lean_dec_ref(v___x_2533_);
v___x_2534_ = lean_unsigned_to_nat(2u);
v___x_2535_ = l_Lean_Syntax_getArg(v_x_2519_, v___x_2534_);
v___x_2536_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2535_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
lean_dec_ref(v___x_2536_);
v___x_2537_ = lean_unsigned_to_nat(3u);
v___x_2538_ = l_Lean_Syntax_getArg(v_x_2519_, v___x_2537_);
lean_dec(v_x_2519_);
v___x_2539_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2538_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_);
return v___x_2539_;
}
else
{
lean_dec(v_x_2519_);
return v___x_2536_;
}
}
else
{
lean_dec(v_x_2519_);
return v___x_2533_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinop___boxed(lean_object* v_x_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_){
_start:
{
lean_object* v_res_2549_; 
v_res_2549_ = l_Lean_Elab_Term_Quotation_precheckBinop(v_x_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_);
lean_dec(v_a_2547_);
lean_dec_ref(v_a_2546_);
lean_dec(v_a_2545_);
lean_dec_ref(v_a_2544_);
lean_dec(v_a_2543_);
lean_dec_ref(v_a_2542_);
lean_dec(v_a_2541_);
return v_res_2549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1(){
_start:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; 
v___x_2558_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
v___x_2559_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckBinop___closed__1));
v___x_2560_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__1));
v___x_2561_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckBinop___boxed), 9, 0);
v___x_2562_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2558_, v___x_2559_, v___x_2560_, v___x_2561_);
return v___x_2562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___boxed(lean_object* v_a_2563_){
_start:
{
lean_object* v_res_2564_; 
v_res_2564_ = l_Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1();
return v_res_2564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinopLazy(lean_object* v_x_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_){
_start:
{
lean_object* v___x_2580_; uint8_t v___x_2581_; 
v___x_2580_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__1));
lean_inc(v_x_2571_);
v___x_2581_ = l_Lean_Syntax_isOfKind(v_x_2571_, v___x_2580_);
if (v___x_2581_ == 0)
{
lean_object* v___x_2582_; 
lean_dec(v_x_2571_);
v___x_2582_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__7___redArg();
return v___x_2582_;
}
else
{
lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2583_ = lean_unsigned_to_nat(1u);
v___x_2584_ = l_Lean_Syntax_getArg(v_x_2571_, v___x_2583_);
v___x_2585_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2584_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_);
if (lean_obj_tag(v___x_2585_) == 0)
{
lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
lean_dec_ref(v___x_2585_);
v___x_2586_ = lean_unsigned_to_nat(2u);
v___x_2587_ = l_Lean_Syntax_getArg(v_x_2571_, v___x_2586_);
v___x_2588_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2587_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
lean_dec_ref(v___x_2588_);
v___x_2589_ = lean_unsigned_to_nat(3u);
v___x_2590_ = l_Lean_Syntax_getArg(v_x_2571_, v___x_2589_);
lean_dec(v_x_2571_);
v___x_2591_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2590_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_);
return v___x_2591_;
}
else
{
lean_dec(v_x_2571_);
return v___x_2588_;
}
}
else
{
lean_dec(v_x_2571_);
return v___x_2585_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinopLazy___boxed(lean_object* v_x_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_){
_start:
{
lean_object* v_res_2601_; 
v_res_2601_ = l_Lean_Elab_Term_Quotation_precheckBinopLazy(v_x_2592_, v_a_2593_, v_a_2594_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_, v_a_2599_);
lean_dec(v_a_2599_);
lean_dec_ref(v_a_2598_);
lean_dec(v_a_2597_);
lean_dec_ref(v_a_2596_);
lean_dec(v_a_2595_);
lean_dec_ref(v_a_2594_);
lean_dec(v_a_2593_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1(){
_start:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2610_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
v___x_2611_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__1));
v___x_2612_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__1));
v___x_2613_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckBinopLazy___boxed), 9, 0);
v___x_2614_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2610_, v___x_2611_, v___x_2612_, v___x_2613_);
return v___x_2614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___boxed(lean_object* v_a_2615_){
_start:
{
lean_object* v_res_2616_; 
v_res_2616_ = l_Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1();
return v_res_2616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckLeftact(lean_object* v_x_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_){
_start:
{
lean_object* v___x_2632_; uint8_t v___x_2633_; 
v___x_2632_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckLeftact___closed__1));
lean_inc(v_x_2623_);
v___x_2633_ = l_Lean_Syntax_isOfKind(v_x_2623_, v___x_2632_);
if (v___x_2633_ == 0)
{
lean_object* v___x_2634_; 
lean_dec(v_x_2623_);
v___x_2634_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__7___redArg();
return v___x_2634_;
}
else
{
lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___x_2635_ = lean_unsigned_to_nat(1u);
v___x_2636_ = l_Lean_Syntax_getArg(v_x_2623_, v___x_2635_);
v___x_2637_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2636_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_);
if (lean_obj_tag(v___x_2637_) == 0)
{
lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; 
lean_dec_ref(v___x_2637_);
v___x_2638_ = lean_unsigned_to_nat(2u);
v___x_2639_ = l_Lean_Syntax_getArg(v_x_2623_, v___x_2638_);
v___x_2640_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2639_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_);
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
lean_dec_ref(v___x_2640_);
v___x_2641_ = lean_unsigned_to_nat(3u);
v___x_2642_ = l_Lean_Syntax_getArg(v_x_2623_, v___x_2641_);
lean_dec(v_x_2623_);
v___x_2643_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2642_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_);
return v___x_2643_;
}
else
{
lean_dec(v_x_2623_);
return v___x_2640_;
}
}
else
{
lean_dec(v_x_2623_);
return v___x_2637_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckLeftact___boxed(lean_object* v_x_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_){
_start:
{
lean_object* v_res_2653_; 
v_res_2653_ = l_Lean_Elab_Term_Quotation_precheckLeftact(v_x_2644_, v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
lean_dec(v_a_2651_);
lean_dec_ref(v_a_2650_);
lean_dec(v_a_2649_);
lean_dec_ref(v_a_2648_);
lean_dec(v_a_2647_);
lean_dec_ref(v_a_2646_);
lean_dec(v_a_2645_);
return v_res_2653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1(){
_start:
{
lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; 
v___x_2662_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
v___x_2663_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckLeftact___closed__1));
v___x_2664_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__1));
v___x_2665_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckLeftact___boxed), 9, 0);
v___x_2666_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2662_, v___x_2663_, v___x_2664_, v___x_2665_);
return v___x_2666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___boxed(lean_object* v_a_2667_){
_start:
{
lean_object* v_res_2668_; 
v_res_2668_ = l_Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1();
return v_res_2668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckRightact(lean_object* v_x_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_){
_start:
{
lean_object* v___x_2684_; uint8_t v___x_2685_; 
v___x_2684_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckRightact___closed__1));
lean_inc(v_x_2675_);
v___x_2685_ = l_Lean_Syntax_isOfKind(v_x_2675_, v___x_2684_);
if (v___x_2685_ == 0)
{
lean_object* v___x_2686_; 
lean_dec(v_x_2675_);
v___x_2686_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__7___redArg();
return v___x_2686_;
}
else
{
lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; 
v___x_2687_ = lean_unsigned_to_nat(1u);
v___x_2688_ = l_Lean_Syntax_getArg(v_x_2675_, v___x_2687_);
v___x_2689_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2688_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_);
if (lean_obj_tag(v___x_2689_) == 0)
{
lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
lean_dec_ref(v___x_2689_);
v___x_2690_ = lean_unsigned_to_nat(2u);
v___x_2691_ = l_Lean_Syntax_getArg(v_x_2675_, v___x_2690_);
v___x_2692_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2691_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_);
if (lean_obj_tag(v___x_2692_) == 0)
{
lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; 
lean_dec_ref(v___x_2692_);
v___x_2693_ = lean_unsigned_to_nat(3u);
v___x_2694_ = l_Lean_Syntax_getArg(v_x_2675_, v___x_2693_);
lean_dec(v_x_2675_);
v___x_2695_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2694_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_);
return v___x_2695_;
}
else
{
lean_dec(v_x_2675_);
return v___x_2692_;
}
}
else
{
lean_dec(v_x_2675_);
return v___x_2689_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckRightact___boxed(lean_object* v_x_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_){
_start:
{
lean_object* v_res_2705_; 
v_res_2705_ = l_Lean_Elab_Term_Quotation_precheckRightact(v_x_2696_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_);
lean_dec(v_a_2703_);
lean_dec_ref(v_a_2702_);
lean_dec(v_a_2701_);
lean_dec_ref(v_a_2700_);
lean_dec(v_a_2699_);
lean_dec_ref(v_a_2698_);
lean_dec(v_a_2697_);
return v_res_2705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1(){
_start:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2714_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
v___x_2715_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckRightact___closed__1));
v___x_2716_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__1));
v___x_2717_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckRightact___boxed), 9, 0);
v___x_2718_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2714_, v___x_2715_, v___x_2716_, v___x_2717_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___boxed(lean_object* v_a_2719_){
_start:
{
lean_object* v_res_2720_; 
v_res_2720_ = l_Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1();
return v_res_2720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckUnop(lean_object* v_x_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_){
_start:
{
lean_object* v___x_2736_; uint8_t v___x_2737_; 
v___x_2736_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckUnop___closed__1));
lean_inc(v_x_2727_);
v___x_2737_ = l_Lean_Syntax_isOfKind(v_x_2727_, v___x_2736_);
if (v___x_2737_ == 0)
{
lean_object* v___x_2738_; 
lean_dec(v_x_2727_);
v___x_2738_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__7___redArg();
return v___x_2738_;
}
else
{
lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; 
v___x_2739_ = lean_unsigned_to_nat(1u);
v___x_2740_ = l_Lean_Syntax_getArg(v_x_2727_, v___x_2739_);
v___x_2741_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2740_, v_a_2728_, v_a_2729_, v_a_2730_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_);
if (lean_obj_tag(v___x_2741_) == 0)
{
lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; 
lean_dec_ref(v___x_2741_);
v___x_2742_ = lean_unsigned_to_nat(2u);
v___x_2743_ = l_Lean_Syntax_getArg(v_x_2727_, v___x_2742_);
lean_dec(v_x_2727_);
v___x_2744_ = l_Lean_Elab_Term_Quotation_precheck(v___x_2743_, v_a_2728_, v_a_2729_, v_a_2730_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_);
return v___x_2744_;
}
else
{
lean_dec(v_x_2727_);
return v___x_2741_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckUnop___boxed(lean_object* v_x_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_){
_start:
{
lean_object* v_res_2754_; 
v_res_2754_ = l_Lean_Elab_Term_Quotation_precheckUnop(v_x_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_);
lean_dec(v_a_2752_);
lean_dec_ref(v_a_2751_);
lean_dec(v_a_2750_);
lean_dec_ref(v_a_2749_);
lean_dec(v_a_2748_);
lean_dec_ref(v_a_2747_);
lean_dec(v_a_2746_);
return v_res_2754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1(){
_start:
{
lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; 
v___x_2763_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
v___x_2764_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckUnop___closed__1));
v___x_2765_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__1));
v___x_2766_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckUnop___boxed), 9, 0);
v___x_2767_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2763_, v___x_2764_, v___x_2765_, v___x_2766_);
return v___x_2767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___boxed(lean_object* v_a_2768_){
_start:
{
lean_object* v_res_2769_; 
v_res_2769_ = l_Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1();
return v_res_2769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckHygieneInfo___redArg(){
_start:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; 
v___x_2771_ = lean_box(0);
v___x_2772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2772_, 0, v___x_2771_);
return v___x_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckHygieneInfo___redArg___boxed(lean_object* v_a_2773_){
_start:
{
lean_object* v_res_2774_; 
v_res_2774_ = l_Lean_Elab_Term_Quotation_precheckHygieneInfo___redArg();
return v_res_2774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckHygieneInfo(lean_object* v_x_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_){
_start:
{
lean_object* v___x_2784_; 
v___x_2784_ = l_Lean_Elab_Term_Quotation_precheckHygieneInfo___redArg();
return v___x_2784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckHygieneInfo___boxed(lean_object* v_x_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_){
_start:
{
lean_object* v_res_2794_; 
v_res_2794_ = l_Lean_Elab_Term_Quotation_precheckHygieneInfo(v_x_2785_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_, v_a_2792_);
lean_dec(v_a_2792_);
lean_dec_ref(v_a_2791_);
lean_dec(v_a_2790_);
lean_dec_ref(v_a_2789_);
lean_dec(v_a_2788_);
lean_dec_ref(v_a_2787_);
lean_dec(v_a_2786_);
lean_dec(v_x_2785_);
return v_res_2794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1(){
_start:
{
lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2808_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
v___x_2809_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__0));
v___x_2810_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__2));
v___x_2811_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckHygieneInfo___boxed), 9, 0);
v___x_2812_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2808_, v___x_2809_, v___x_2810_, v___x_2811_);
return v___x_2812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___boxed(lean_object* v_a_2813_){
_start:
{
lean_object* v_res_2814_; 
v_res_2814_ = l_Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1();
return v_res_2814_;
}
}
lean_object* runtime_initialize_Lean_Elab_Quotation_Util(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Quotation_Precheck(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Quotation_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Term_Quotation_quotPrecheck = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Term_Quotation_quotPrecheck);
lean_dec_ref(res);
res = l_Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Term_Quotation_quotPrecheck_allowSectionVars = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Term_Quotation_quotPrecheck_allowSectionVars);
lean_dec_ref(res);
res = l_Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Term_Quotation_precheckAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckAttribute);
lean_dec_ref(res);
res = l_Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1();
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
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Quotation_Precheck(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Quotation_Util(builtin);
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
