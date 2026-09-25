// Lean compiler output
// Module: Lean.Linter.Deprecated
// Imports: public import Lean.Meta.Basic import Lean.Linter.Init import Lean.Elab.InfoTree.Main import Lean.ExtraModUses import Lean.Meta.Hint import Init.Data.List.MapIdx import Init.Omega
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
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_Name_componentsRev(lean_object*);
lean_object* l_Lean_Name_appendCore(lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
extern lean_object* l_Lean_ResolveName_backward_privateInPublic_warn;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_MacroScopesView_review(lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_extractMacroScopes(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MacroScopesView_isSuffixOf(lean_object*, lean_object*);
lean_object* l_Lean_privateToUserName_x3f(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerParametricAttributeExt___redArg(lean_object*, uint8_t, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_MessageData_hint_x27(lean_object*);
lean_object* l_Lean_Syntax_ofRange(lean_object*, uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_hint(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_ConstantInfo_numLevelParams(lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_ConstantInfo_instantiateTypeLevelParams(lean_object*, lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Std_HashMap_instInhabited___redArg();
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___redArg();
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
extern lean_object* l_Lean_Linter_linterSetsExt;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
extern lean_object* l_Lean_rootNamespace;
lean_object* l_Lean_getRevAliases(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Name_getPrefix(lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_registerParametricAttributeForExt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_ParametricAttribute_setParam___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___redArg(lean_object*, lean_object*);
lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isProtected(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_List_get___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "deprecated"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(227, 99, 57, 49, 46, 156, 253, 187)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "if true, generate deprecation warnings"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(53, 243, 121, 207, 53, 172, 203, 87)}};
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(248, 165, 85, 201, 27, 48, 185, 203)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_linter_deprecated;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "deprecatedTarget"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(227, 99, 57, 49, 46, 156, 253, 187)}};
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(204, 166, 165, 234, 53, 174, 145, 27)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 97, .m_capacity = 97, .m_length = 96, .m_data = "if true, warn when a `@[deprecated]` attribute points at a declaration that is itself deprecated"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(53, 243, 121, 207, 53, 172, 203, 87)}};
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(248, 165, 85, 201, 27, 48, 185, 203)}};
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(147, 187, 162, 70, 72, 196, 181, 236)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_linter_deprecated_deprecatedTarget;
static const lean_ctor_object l_Lean_Linter_instInhabitedDeprecationEntry_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Linter_instInhabitedDeprecationEntry_default___closed__0 = (const lean_object*)&l_Lean_Linter_instInhabitedDeprecationEntry_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_instInhabitedDeprecationEntry_default = (const lean_object*)&l_Lean_Linter_instInhabitedDeprecationEntry_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_instInhabitedDeprecationEntry = (const lean_object*)&l_Lean_Linter_instInhabitedDeprecationEntry_default___closed__0_value;
static const lean_string_object l_List_mapIdx_go___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_deprecated"};
static const lean_object* l_List_mapIdx_go___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq_spec__0___closed__0 = (const lean_object*)&l_List_mapIdx_go___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq_spec__0___closed__0_value;
static const lean_ctor_object l_List_mapIdx_go___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_mapIdx_go___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(123, 51, 129, 56, 173, 194, 28, 188)}};
static const lean_object* l_List_mapIdx_go___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq_spec__0___closed__1 = (const lean_object*)&l_List_mapIdx_go___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq___closed__0 = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__6___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Try this: +typeChanged"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44_spec__47(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44_spec__47___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Private declaration `"};
static const lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__0 = (const lean_object*)&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__0_value;
static lean_once_cell_t l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__1;
static const lean_string_object l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 167, .m_capacity = 167, .m_length = 166, .m_data = "` accessed publicly; this is allowed only because the `backward.privateInPublic` option is enabled. \n\nDisable `backward.privateInPublic.warn` to silence this warning."};
static const lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__2 = (const lean_object*)&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__2_value;
static lean_once_cell_t l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__3;
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__31(lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__31___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__17___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__17___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22___lam__0___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__0 = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__0_value;
static const lean_closure_object l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22___lam__0___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48___closed__0_value)} };
static const lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__1 = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22___closed__0 = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__24(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12___closed__0 = (const lean_object*)&l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5___lam__0___boxed, .m_arity = 7, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5___closed__0 = (const lean_object*)&l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__0;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__1;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__2;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__3_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__4 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__4_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__7_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__8;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__9;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__10 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__10_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__11;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__12 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__12_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__13;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__14_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__15;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__16_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__18_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__19_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2___closed__0;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__0_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 134, .m_capacity = 134, .m_length = 133, .m_data = "`[deprecated]` attribute should specify the date or library version at which the deprecation was introduced, using `(since := \"...\")`"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__0_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__0_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__1_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__0_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__1_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__1_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__2_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__2_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__3_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 83, .m_capacity = 83, .m_length = 82, .m_data = "`[deprecated]` attribute should specify either a new name or a deprecation message"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__3_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__3_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__4_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__3_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__4_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__4_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__5_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__5_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "The updated constant has a different type:"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "\ninstead of"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__10_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 372, .m_capacity = 372, .m_length = 371, .m_data = "\n\nThis suggests that addressing the deprecation might be more involved than simply replacing the old name with the new name. This is often expected, but sometimes it indicates that the deprecation is in favor of the wrong declaration, or that there is a mistake in one of the statements.\n\nIf the type difference is intentional, use `+typeChanged` to silence this warning."};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__10_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__10_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__11_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__11_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__12_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Add `+typeChanged` to silence this warning."};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__12_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__12_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__13_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__12_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__13_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__13_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__14_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__14_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__15_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__15_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Invalid `[deprecated]` attribute syntax"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__18_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Add `+typeChanged`:"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__18_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__18_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__19_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__18_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__19_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__19_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__20_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__20_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__21_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " +typeChanged"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__21_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__21_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__22_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__21_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__22_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__22_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__23_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "+typeChanged"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__23_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__23_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__24_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__23_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__24_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__24_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__25_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__25_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__27_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 88, .m_capacity = 88, .m_length = 87, .m_data = "The `+typeChanged` marker is not needed because the updated constant has the same type."};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__27_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__27_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__28_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__27_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__28_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__28_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
static const lean_array_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__36_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Deprecate in favor of `"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__36_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__36_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__37_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__37_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__38_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "` instead:"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__38_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__38_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__39_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__39_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__40_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "This warning can be disabled with `set_option "};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__40_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__40_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " false`"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = "` is itself deprecated, but without an explicit replacement; `"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__47_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__47_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__48_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "` is being deprecated in favor of a deprecated declaration"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__48_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__48_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__49_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__49_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__50_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "` is itself deprecated in favor of `"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__50_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__50_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__51_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__51_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__52_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "`; consider deprecating `"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__52_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__52_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__53_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__53_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__54_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "` in favor of `"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__54_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__54_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__55_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__55_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__56_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` instead"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__56_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__56_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__57_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__57_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__58_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Invalid `[deprecated]` attribute: `"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__58_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__58_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__59_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__59_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__60_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "` cannot be deprecated in favor of itself"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__60_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__60_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__61_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__61_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "deprecatedAttr"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(85, 246, 23, 143, 159, 138, 155, 162)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(78, 182, 79, 155, 204, 118, 39, 140)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "mark declaration as deprecated"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__17(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__17___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_deprecatedAttr;
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Linter_isDeprecated(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_isDeprecated___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_MessageData_isDeprecationWarning___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_isDeprecationWarning___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_MessageData_isDeprecationWarning___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageData_isDeprecationWarning___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MessageData_isDeprecationWarning___closed__0 = (const lean_object*)&l_Lean_MessageData_isDeprecationWarning___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_MessageData_isDeprecationWarning(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_isDeprecationWarning___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getDeprecatedNewName(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___00List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Replace the deprecated name:"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__0 = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__0_value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_checkDeprecated___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "` has been deprecated"};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__0 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__0_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__1;
static const lean_string_object l_Lean_Linter_checkDeprecated___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ": Use `"};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__2 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__2_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__3;
static const lean_string_object l_Lean_Linter_checkDeprecated___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "` is protected. References to this constant must include "};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__4 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__4_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__5;
static const lean_string_object l_Lean_Linter_checkDeprecated___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "its prefix `"};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__6 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__6_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__7;
static const lean_string_object l_Lean_Linter_checkDeprecated___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "` even when inside its namespace."};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__8 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__8_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__9;
static const lean_string_object l_Lean_Linter_checkDeprecated___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 86, .m_capacity = 86, .m_length = 85, .m_data = "The updated constant is in a different namespace. Dot notation may need to be changed"};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__10 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__10_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__11;
static const lean_string_object l_Lean_Linter_checkDeprecated___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__12 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__12_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__13;
static const lean_ctor_object l_Lean_Linter_checkDeprecated___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44___closed__0_value)}};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__14 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__14_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__15;
static const lean_string_object l_Lean_Linter_checkDeprecated___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "at least the last component `"};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__16 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__16_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__17;
static const lean_string_object l_Lean_Linter_checkDeprecated___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "` of "};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__18 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__18_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__19;
static const lean_string_object l_Lean_Linter_checkDeprecated___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = " (e.g., from `x."};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__20 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__20_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__21;
static const lean_string_object l_Lean_Linter_checkDeprecated___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "` to `"};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__22 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__22_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__23;
static const lean_string_object l_Lean_Linter_checkDeprecated___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " x`)"};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__24 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__24_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__25;
static const lean_string_object l_Lean_Linter_checkDeprecated___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__26 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__26_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__27;
LEAN_EXPORT lean_object* l_Lean_Linter_checkDeprecated(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_checkDeprecated___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_53_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_));
v___x_54_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_));
v___x_55_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_));
v___x_56_ = l_Lean_Option_register___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__spec__0(v___x_53_, v___x_54_, v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4____boxed(lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_();
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_77_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4_));
v___x_78_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4_));
v___x_79_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4_));
v___x_80_ = l_Lean_Option_register___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__spec__0(v___x_77_, v___x_78_, v___x_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4____boxed(lean_object* v_a_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4_();
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq_spec__0(lean_object* v_a_90_, lean_object* v_a_91_){
_start:
{
if (lean_obj_tag(v_a_90_) == 0)
{
lean_object* v___x_92_; 
v___x_92_ = lean_array_to_list(v_a_91_);
return v___x_92_;
}
else
{
lean_object* v_tail_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v_tail_93_ = lean_ctor_get(v_a_90_, 1);
v___x_94_ = lean_array_get_size(v_a_91_);
v___x_95_ = ((lean_object*)(l_List_mapIdx_go___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq_spec__0___closed__1));
v___x_96_ = l_Lean_Name_num___override(v___x_95_, v___x_94_);
v___x_97_ = l_Lean_mkLevelParam(v___x_96_);
v___x_98_ = lean_array_push(v_a_91_, v___x_97_);
v_a_90_ = v_tail_93_;
v_a_91_ = v___x_98_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq_spec__0___boxed(lean_object* v_a_100_, lean_object* v_a_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_List_mapIdx_go___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq_spec__0(v_a_100_, v_a_101_);
lean_dec(v_a_100_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq(lean_object* v_decl_u2081_105_, lean_object* v_decl_u2082_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_){
_start:
{
lean_object* v___y_113_; lean_object* v___x_130_; lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_130_ = l_Lean_ConstantInfo_numLevelParams(v_decl_u2081_105_);
v___x_131_ = l_Lean_ConstantInfo_numLevelParams(v_decl_u2082_106_);
v___x_132_ = lean_nat_dec_eq(v___x_130_, v___x_131_);
lean_dec(v___x_131_);
lean_dec(v___x_130_);
if (v___x_132_ == 0)
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = lean_box(v___x_132_);
v___x_134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
return v___x_134_;
}
else
{
lean_object* v___x_135_; uint8_t v_transparency_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v_levels_139_; lean_object* v_type_u2081_140_; lean_object* v_type_u2082_141_; uint8_t v___x_142_; uint8_t v___x_143_; 
v___x_135_ = l_Lean_Meta_Context_config(v_a_107_);
v_transparency_136_ = lean_ctor_get_uint8(v___x_135_, 9);
lean_dec_ref(v___x_135_);
v___x_137_ = l_Lean_ConstantInfo_levelParams(v_decl_u2081_105_);
v___x_138_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq___closed__0));
v_levels_139_ = l_List_mapIdx_go___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq_spec__0(v___x_137_, v___x_138_);
lean_dec(v___x_137_);
lean_inc(v_levels_139_);
v_type_u2081_140_ = l_Lean_ConstantInfo_instantiateTypeLevelParams(v_decl_u2081_105_, v_levels_139_);
v_type_u2082_141_ = l_Lean_ConstantInfo_instantiateTypeLevelParams(v_decl_u2082_106_, v_levels_139_);
v___x_142_ = 2;
v___x_143_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_136_, v___x_142_);
if (v___x_143_ == 0)
{
lean_object* v_keyedConfig_144_; uint8_t v_trackZetaDelta_145_; lean_object* v_zetaDeltaSet_146_; lean_object* v_lctx_147_; lean_object* v_localInstances_148_; lean_object* v_defEqCtx_x3f_149_; lean_object* v_synthPendingDepth_150_; lean_object* v_customCanUnfoldPredicate_x3f_151_; uint8_t v_univApprox_152_; uint8_t v_inTypeClassResolution_153_; uint8_t v_cacheInferType_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v_keyedConfig_144_ = lean_ctor_get(v_a_107_, 0);
v_trackZetaDelta_145_ = lean_ctor_get_uint8(v_a_107_, sizeof(void*)*7);
v_zetaDeltaSet_146_ = lean_ctor_get(v_a_107_, 1);
v_lctx_147_ = lean_ctor_get(v_a_107_, 2);
v_localInstances_148_ = lean_ctor_get(v_a_107_, 3);
v_defEqCtx_x3f_149_ = lean_ctor_get(v_a_107_, 4);
v_synthPendingDepth_150_ = lean_ctor_get(v_a_107_, 5);
v_customCanUnfoldPredicate_x3f_151_ = lean_ctor_get(v_a_107_, 6);
v_univApprox_152_ = lean_ctor_get_uint8(v_a_107_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_153_ = lean_ctor_get_uint8(v_a_107_, sizeof(void*)*7 + 2);
v_cacheInferType_154_ = lean_ctor_get_uint8(v_a_107_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_144_);
v___x_155_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_142_, v_keyedConfig_144_);
lean_inc(v_customCanUnfoldPredicate_x3f_151_);
lean_inc(v_synthPendingDepth_150_);
lean_inc(v_defEqCtx_x3f_149_);
lean_inc_ref(v_localInstances_148_);
lean_inc_ref(v_lctx_147_);
lean_inc(v_zetaDeltaSet_146_);
v___x_156_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_156_, 0, v___x_155_);
lean_ctor_set(v___x_156_, 1, v_zetaDeltaSet_146_);
lean_ctor_set(v___x_156_, 2, v_lctx_147_);
lean_ctor_set(v___x_156_, 3, v_localInstances_148_);
lean_ctor_set(v___x_156_, 4, v_defEqCtx_x3f_149_);
lean_ctor_set(v___x_156_, 5, v_synthPendingDepth_150_);
lean_ctor_set(v___x_156_, 6, v_customCanUnfoldPredicate_x3f_151_);
lean_ctor_set_uint8(v___x_156_, sizeof(void*)*7, v_trackZetaDelta_145_);
lean_ctor_set_uint8(v___x_156_, sizeof(void*)*7 + 1, v_univApprox_152_);
lean_ctor_set_uint8(v___x_156_, sizeof(void*)*7 + 2, v_inTypeClassResolution_153_);
lean_ctor_set_uint8(v___x_156_, sizeof(void*)*7 + 3, v_cacheInferType_154_);
v___x_157_ = l_Lean_Meta_isExprDefEqGuarded(v_type_u2081_140_, v_type_u2082_141_, v___x_156_, v_a_108_, v_a_109_, v_a_110_);
lean_dec_ref_known(v___x_156_, 7);
v___y_113_ = v___x_157_;
goto v___jp_112_;
}
else
{
lean_object* v___x_158_; 
v___x_158_ = l_Lean_Meta_isExprDefEqGuarded(v_type_u2081_140_, v_type_u2082_141_, v_a_107_, v_a_108_, v_a_109_, v_a_110_);
v___y_113_ = v___x_158_;
goto v___jp_112_;
}
}
v___jp_112_:
{
if (lean_obj_tag(v___y_113_) == 0)
{
lean_object* v_a_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_121_; 
v_a_114_ = lean_ctor_get(v___y_113_, 0);
v_isSharedCheck_121_ = !lean_is_exclusive(v___y_113_);
if (v_isSharedCheck_121_ == 0)
{
v___x_116_ = v___y_113_;
v_isShared_117_ = v_isSharedCheck_121_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_a_114_);
lean_dec(v___y_113_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_121_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___x_119_; 
if (v_isShared_117_ == 0)
{
v___x_119_ = v___x_116_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v_a_114_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
return v___x_119_;
}
}
}
else
{
lean_object* v_a_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_129_; 
v_a_122_ = lean_ctor_get(v___y_113_, 0);
v_isSharedCheck_129_ = !lean_is_exclusive(v___y_113_);
if (v_isSharedCheck_129_ == 0)
{
v___x_124_ = v___y_113_;
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_a_122_);
lean_dec(v___y_113_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_127_; 
if (v_isShared_125_ == 0)
{
v___x_127_ = v___x_124_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_a_122_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq___boxed(lean_object* v_decl_u2081_159_, lean_object* v_decl_u2082_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq(v_decl_u2081_159_, v_decl_u2082_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_);
lean_dec(v_a_164_);
lean_dec_ref(v_a_163_);
lean_dec(v_a_162_);
lean_dec_ref(v_a_161_);
lean_dec_ref(v_decl_u2082_160_);
lean_dec_ref(v_decl_u2081_159_);
return v_res_166_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__4(lean_object* v_opts_167_, lean_object* v_opt_168_){
_start:
{
lean_object* v_name_169_; lean_object* v_defValue_170_; lean_object* v_map_171_; lean_object* v___x_172_; 
v_name_169_ = lean_ctor_get(v_opt_168_, 0);
v_defValue_170_ = lean_ctor_get(v_opt_168_, 1);
v_map_171_ = lean_ctor_get(v_opts_167_, 0);
v___x_172_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_171_, v_name_169_);
if (lean_obj_tag(v___x_172_) == 0)
{
uint8_t v___x_173_; 
v___x_173_ = lean_unbox(v_defValue_170_);
return v___x_173_;
}
else
{
lean_object* v_val_174_; 
v_val_174_ = lean_ctor_get(v___x_172_, 0);
lean_inc(v_val_174_);
lean_dec_ref_known(v___x_172_, 1);
if (lean_obj_tag(v_val_174_) == 1)
{
uint8_t v_v_175_; 
v_v_175_ = lean_ctor_get_uint8(v_val_174_, 0);
lean_dec_ref_known(v_val_174_, 0);
return v_v_175_;
}
else
{
uint8_t v___x_176_; 
lean_dec(v_val_174_);
v___x_176_ = lean_unbox(v_defValue_170_);
return v___x_176_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__4___boxed(lean_object* v_opts_177_, lean_object* v_opt_178_){
_start:
{
uint8_t v_res_179_; lean_object* v_r_180_; 
v_res_179_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__4(v_opts_177_, v_opt_178_);
lean_dec_ref(v_opt_178_);
lean_dec_ref(v_opts_177_);
v_r_180_ = lean_box(v_res_179_);
return v_r_180_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__6(lean_object* v_x_181_, lean_object* v_x_182_){
_start:
{
if (lean_obj_tag(v_x_181_) == 0)
{
if (lean_obj_tag(v_x_182_) == 0)
{
uint8_t v___x_183_; 
v___x_183_ = 1;
return v___x_183_;
}
else
{
uint8_t v___x_184_; 
v___x_184_ = 0;
return v___x_184_;
}
}
else
{
if (lean_obj_tag(v_x_182_) == 0)
{
uint8_t v___x_185_; 
v___x_185_ = 0;
return v___x_185_;
}
else
{
lean_object* v_val_186_; lean_object* v_val_187_; uint8_t v___x_188_; 
v_val_186_ = lean_ctor_get(v_x_181_, 0);
v_val_187_ = lean_ctor_get(v_x_182_, 0);
v___x_188_ = lean_name_eq(v_val_186_, v_val_187_);
return v___x_188_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__6___boxed(lean_object* v_x_189_, lean_object* v_x_190_){
_start:
{
uint8_t v_res_191_; lean_object* v_r_192_; 
v_res_191_ = l_Option_instBEq_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__6(v_x_189_, v_x_190_);
lean_dec(v_x_190_);
lean_dec(v_x_189_);
v_r_192_ = lean_box(v_res_191_);
return v_r_192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(lean_object* v_x_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2____boxed(lean_object* v_x_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(v_x_196_);
lean_dec_ref(v_x_196_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(lean_object* v_x_198_, lean_object* v_x_199_, lean_object* v_x_200_, lean_object* v___y_201_){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = lean_box(0);
v___x_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2____boxed(lean_object* v_x_205_, lean_object* v_x_206_, lean_object* v_x_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(v_x_205_, v_x_206_, v_x_207_, v___y_208_);
lean_dec(v___y_208_);
lean_dec_ref(v_x_207_);
lean_dec_ref(v_x_206_);
lean_dec(v_x_205_);
return v_res_210_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(uint8_t v___x_211_, lean_object* v_env_212_, lean_object* v_n_213_, lean_object* v_x_214_){
_start:
{
uint8_t v___x_215_; 
v___x_215_ = l_Lean_Environment_contains(v_env_212_, v_n_213_, v___x_211_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2____boxed(lean_object* v___x_216_, lean_object* v_env_217_, lean_object* v_n_218_, lean_object* v_x_219_){
_start:
{
uint8_t v___x_43314__boxed_220_; uint8_t v_res_221_; lean_object* v_r_222_; 
v___x_43314__boxed_220_ = lean_unbox(v___x_216_);
v_res_221_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(v___x_43314__boxed_220_, v_env_217_, v_n_218_, v_x_219_);
lean_dec_ref(v_x_219_);
v_r_222_ = lean_box(v_res_221_);
return v_r_222_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__27(lean_object* v_a_223_, lean_object* v_a_224_){
_start:
{
if (lean_obj_tag(v_a_223_) == 0)
{
lean_object* v___x_225_; 
v___x_225_ = l_List_reverse___redArg(v_a_224_);
return v___x_225_;
}
else
{
lean_object* v_head_226_; lean_object* v_tail_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_238_; 
v_head_226_ = lean_ctor_get(v_a_223_, 0);
v_tail_227_ = lean_ctor_get(v_a_223_, 1);
v_isSharedCheck_238_ = !lean_is_exclusive(v_a_223_);
if (v_isSharedCheck_238_ == 0)
{
v___x_229_ = v_a_223_;
v_isShared_230_ = v_isSharedCheck_238_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_tail_227_);
lean_inc(v_head_226_);
lean_dec(v_a_223_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_238_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v_snd_231_; uint8_t v___x_232_; 
v_snd_231_ = lean_ctor_get(v_head_226_, 1);
v___x_232_ = l_List_isEmpty___redArg(v_snd_231_);
if (v___x_232_ == 0)
{
lean_del_object(v___x_229_);
lean_dec(v_head_226_);
v_a_223_ = v_tail_227_;
goto _start;
}
else
{
lean_object* v___x_235_; 
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 1, v_a_224_);
v___x_235_ = v___x_229_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_head_226_);
lean_ctor_set(v_reuseFailAlloc_237_, 1, v_a_224_);
v___x_235_ = v_reuseFailAlloc_237_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
v_a_223_ = v_tail_227_;
v_a_224_ = v___x_235_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44_spec__47(lean_object* v_msgData_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
lean_object* v___x_245_; lean_object* v_env_246_; lean_object* v___x_247_; lean_object* v_toCold_248_; lean_object* v_mctx_249_; lean_object* v_lctx_250_; lean_object* v_options_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_245_ = lean_st_ref_get(v___y_243_);
v_env_246_ = lean_ctor_get(v___x_245_, 0);
lean_inc_ref(v_env_246_);
lean_dec(v___x_245_);
v___x_247_ = lean_st_ref_get(v___y_241_);
v_toCold_248_ = lean_ctor_get(v___y_242_, 0);
v_mctx_249_ = lean_ctor_get(v___x_247_, 0);
lean_inc_ref(v_mctx_249_);
lean_dec(v___x_247_);
v_lctx_250_ = lean_ctor_get(v___y_240_, 2);
v_options_251_ = lean_ctor_get(v_toCold_248_, 2);
lean_inc_ref(v_options_251_);
lean_inc_ref(v_lctx_250_);
v___x_252_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_252_, 0, v_env_246_);
lean_ctor_set(v___x_252_, 1, v_mctx_249_);
lean_ctor_set(v___x_252_, 2, v_lctx_250_);
lean_ctor_set(v___x_252_, 3, v_options_251_);
v___x_253_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
lean_ctor_set(v___x_253_, 1, v_msgData_239_);
v___x_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44_spec__47___boxed(lean_object* v_msgData_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44_spec__47(v_msgData_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
return v_res_261_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0(uint8_t v_suppressElabErrors_270_, uint8_t v___y_271_, lean_object* v_x_272_){
_start:
{
if (lean_obj_tag(v_x_272_) == 1)
{
lean_object* v_pre_273_; 
v_pre_273_ = lean_ctor_get(v_x_272_, 0);
switch(lean_obj_tag(v_pre_273_))
{
case 1:
{
lean_object* v_pre_274_; 
v_pre_274_ = lean_ctor_get(v_pre_273_, 0);
switch(lean_obj_tag(v_pre_274_))
{
case 0:
{
lean_object* v_str_275_; lean_object* v_str_276_; lean_object* v___x_277_; uint8_t v___x_278_; 
v_str_275_ = lean_ctor_get(v_x_272_, 1);
v_str_276_ = lean_ctor_get(v_pre_273_, 1);
v___x_277_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__0));
v___x_278_ = lean_string_dec_eq(v_str_276_, v___x_277_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; uint8_t v___x_280_; 
v___x_279_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__1));
v___x_280_ = lean_string_dec_eq(v_str_276_, v___x_279_);
if (v___x_280_ == 0)
{
return v___x_280_;
}
else
{
lean_object* v___x_281_; uint8_t v___x_282_; 
v___x_281_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__2));
v___x_282_ = lean_string_dec_eq(v_str_275_, v___x_281_);
if (v___x_282_ == 0)
{
return v___x_282_;
}
else
{
return v_suppressElabErrors_270_;
}
}
}
else
{
lean_object* v___x_283_; uint8_t v___x_284_; 
v___x_283_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__3));
v___x_284_ = lean_string_dec_eq(v_str_275_, v___x_283_);
if (v___x_284_ == 0)
{
return v___x_284_;
}
else
{
return v_suppressElabErrors_270_;
}
}
}
case 1:
{
lean_object* v_pre_285_; 
v_pre_285_ = lean_ctor_get(v_pre_274_, 0);
if (lean_obj_tag(v_pre_285_) == 0)
{
lean_object* v_str_286_; lean_object* v_str_287_; lean_object* v_str_288_; lean_object* v___x_289_; uint8_t v___x_290_; 
v_str_286_ = lean_ctor_get(v_x_272_, 1);
v_str_287_ = lean_ctor_get(v_pre_273_, 1);
v_str_288_ = lean_ctor_get(v_pre_274_, 1);
v___x_289_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__4));
v___x_290_ = lean_string_dec_eq(v_str_288_, v___x_289_);
if (v___x_290_ == 0)
{
return v___x_290_;
}
else
{
lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_291_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__5));
v___x_292_ = lean_string_dec_eq(v_str_287_, v___x_291_);
if (v___x_292_ == 0)
{
return v___x_292_;
}
else
{
lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_293_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__6));
v___x_294_ = lean_string_dec_eq(v_str_286_, v___x_293_);
if (v___x_294_ == 0)
{
return v___x_294_;
}
else
{
return v_suppressElabErrors_270_;
}
}
}
}
else
{
return v___y_271_;
}
}
default: 
{
return v___y_271_;
}
}
}
case 0:
{
lean_object* v_str_295_; lean_object* v___x_296_; uint8_t v___x_297_; 
v_str_295_ = lean_ctor_get(v_x_272_, 1);
v___x_296_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__7));
v___x_297_ = lean_string_dec_eq(v_str_295_, v___x_296_);
if (v___x_297_ == 0)
{
return v___x_297_;
}
else
{
return v_suppressElabErrors_270_;
}
}
default: 
{
return v___y_271_;
}
}
}
else
{
return v___y_271_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___boxed(lean_object* v_suppressElabErrors_298_, lean_object* v___y_299_, lean_object* v_x_300_){
_start:
{
uint8_t v_suppressElabErrors_boxed_301_; uint8_t v___y_43396__boxed_302_; uint8_t v_res_303_; lean_object* v_r_304_; 
v_suppressElabErrors_boxed_301_ = lean_unbox(v_suppressElabErrors_298_);
v___y_43396__boxed_302_ = lean_unbox(v___y_299_);
v_res_303_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0(v_suppressElabErrors_boxed_301_, v___y_43396__boxed_302_, v_x_300_);
lean_dec(v_x_300_);
v_r_304_ = lean_box(v_res_303_);
return v_r_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44(lean_object* v_ref_306_, lean_object* v_msgData_307_, uint8_t v_severity_308_, uint8_t v_isSilent_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v___y_316_; lean_object* v___y_317_; lean_object* v___y_318_; lean_object* v___y_319_; uint8_t v___y_320_; uint8_t v___y_321_; lean_object* v___y_322_; lean_object* v_toCold_323_; lean_object* v___y_324_; lean_object* v___y_353_; lean_object* v___y_354_; uint8_t v___y_355_; lean_object* v___y_356_; uint8_t v___y_357_; uint8_t v___y_358_; lean_object* v___y_359_; lean_object* v___y_360_; uint8_t v___y_380_; lean_object* v___y_381_; lean_object* v___y_382_; uint8_t v___y_383_; uint8_t v___y_384_; lean_object* v___y_385_; lean_object* v___y_386_; uint8_t v___y_390_; uint8_t v___y_391_; uint8_t v___y_392_; uint8_t v___x_403_; uint8_t v___y_405_; uint8_t v___y_406_; uint8_t v___y_407_; uint8_t v___y_409_; uint8_t v___x_417_; 
v___x_403_ = 2;
v___x_417_ = l_Lean_instBEqMessageSeverity_beq(v_severity_308_, v___x_403_);
if (v___x_417_ == 0)
{
v___y_409_ = v___x_417_;
goto v___jp_408_;
}
else
{
uint8_t v___x_418_; 
lean_inc_ref(v_msgData_307_);
v___x_418_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_307_);
v___y_409_ = v___x_418_;
goto v___jp_408_;
}
v___jp_315_:
{
lean_object* v_currNamespace_325_; lean_object* v_openDecls_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v_env_331_; lean_object* v_nextMacroScope_332_; lean_object* v_ngen_333_; lean_object* v_auxDeclNGen_334_; lean_object* v_traceState_335_; lean_object* v_cache_336_; lean_object* v_recordedDeps_337_; lean_object* v_messages_338_; lean_object* v_infoState_339_; lean_object* v_snapshotTasks_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_351_; 
v_currNamespace_325_ = lean_ctor_get(v_toCold_323_, 4);
v_openDecls_326_ = lean_ctor_get(v_toCold_323_, 5);
lean_inc(v_openDecls_326_);
lean_inc(v_currNamespace_325_);
v___x_327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_327_, 0, v_currNamespace_325_);
lean_ctor_set(v___x_327_, 1, v_openDecls_326_);
v___x_328_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
lean_ctor_set(v___x_328_, 1, v___y_316_);
lean_inc_ref(v___y_319_);
lean_inc_ref(v___y_317_);
v___x_329_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_329_, 0, v___y_317_);
lean_ctor_set(v___x_329_, 1, v___y_322_);
lean_ctor_set(v___x_329_, 2, v___y_318_);
lean_ctor_set(v___x_329_, 3, v___y_319_);
lean_ctor_set(v___x_329_, 4, v___x_328_);
lean_ctor_set_uint8(v___x_329_, sizeof(void*)*5, v___y_321_);
lean_ctor_set_uint8(v___x_329_, sizeof(void*)*5 + 1, v___y_320_);
lean_ctor_set_uint8(v___x_329_, sizeof(void*)*5 + 2, v_isSilent_309_);
v___x_330_ = lean_st_ref_take(v___y_324_);
v_env_331_ = lean_ctor_get(v___x_330_, 0);
v_nextMacroScope_332_ = lean_ctor_get(v___x_330_, 1);
v_ngen_333_ = lean_ctor_get(v___x_330_, 2);
v_auxDeclNGen_334_ = lean_ctor_get(v___x_330_, 3);
v_traceState_335_ = lean_ctor_get(v___x_330_, 4);
v_cache_336_ = lean_ctor_get(v___x_330_, 5);
v_recordedDeps_337_ = lean_ctor_get(v___x_330_, 6);
v_messages_338_ = lean_ctor_get(v___x_330_, 7);
v_infoState_339_ = lean_ctor_get(v___x_330_, 8);
v_snapshotTasks_340_ = lean_ctor_get(v___x_330_, 9);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_351_ == 0)
{
v___x_342_ = v___x_330_;
v_isShared_343_ = v_isSharedCheck_351_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_snapshotTasks_340_);
lean_inc(v_infoState_339_);
lean_inc(v_messages_338_);
lean_inc(v_recordedDeps_337_);
lean_inc(v_cache_336_);
lean_inc(v_traceState_335_);
lean_inc(v_auxDeclNGen_334_);
lean_inc(v_ngen_333_);
lean_inc(v_nextMacroScope_332_);
lean_inc(v_env_331_);
lean_dec(v___x_330_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_351_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_347_; 
v___x_344_ = lean_box(0);
v___x_345_ = l_Lean_MessageLog_add(v___x_329_, v_messages_338_);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 7, v___x_345_);
v___x_347_ = v___x_342_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_env_331_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v_nextMacroScope_332_);
lean_ctor_set(v_reuseFailAlloc_350_, 2, v_ngen_333_);
lean_ctor_set(v_reuseFailAlloc_350_, 3, v_auxDeclNGen_334_);
lean_ctor_set(v_reuseFailAlloc_350_, 4, v_traceState_335_);
lean_ctor_set(v_reuseFailAlloc_350_, 5, v_cache_336_);
lean_ctor_set(v_reuseFailAlloc_350_, 6, v_recordedDeps_337_);
lean_ctor_set(v_reuseFailAlloc_350_, 7, v___x_345_);
lean_ctor_set(v_reuseFailAlloc_350_, 8, v_infoState_339_);
lean_ctor_set(v_reuseFailAlloc_350_, 9, v_snapshotTasks_340_);
v___x_347_ = v_reuseFailAlloc_350_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_st_ref_put(v___y_324_, v___x_347_);
v___x_349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_349_, 0, v___x_344_);
return v___x_349_;
}
}
}
v___jp_352_:
{
lean_object* v_fileName_361_; lean_object* v_fileMap_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v_a_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_378_; 
v_fileName_361_ = lean_ctor_get(v___y_356_, 0);
v_fileMap_362_ = lean_ctor_get(v___y_356_, 1);
v___x_363_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_307_);
v___x_364_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44_spec__47(v___x_363_, v___y_310_, v___y_311_, v___y_312_, v___y_313_);
v_a_365_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_378_ == 0)
{
v___x_367_ = v___x_364_;
v_isShared_368_ = v_isSharedCheck_378_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_dec(v___x_364_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_378_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
lean_inc_ref_n(v_fileMap_362_, 2);
v___x_369_ = l_Lean_FileMap_toPosition(v_fileMap_362_, v___y_359_);
lean_dec(v___y_359_);
v___x_370_ = l_Lean_FileMap_toPosition(v_fileMap_362_, v___y_360_);
lean_dec(v___y_360_);
v___x_371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
v___x_372_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44___closed__0));
if (v___y_355_ == 0)
{
lean_del_object(v___x_367_);
lean_dec_ref(v___y_354_);
v___y_316_ = v_a_365_;
v___y_317_ = v_fileName_361_;
v___y_318_ = v___x_371_;
v___y_319_ = v___x_372_;
v___y_320_ = v___y_358_;
v___y_321_ = v___y_357_;
v___y_322_ = v___x_369_;
v_toCold_323_ = v___y_353_;
v___y_324_ = v___y_313_;
goto v___jp_315_;
}
else
{
uint8_t v___x_373_; 
lean_inc(v_a_365_);
v___x_373_ = l_Lean_MessageData_hasTag(v___y_354_, v_a_365_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; lean_object* v___x_376_; 
lean_dec_ref_known(v___x_371_, 1);
lean_dec_ref(v___x_369_);
lean_dec(v_a_365_);
v___x_374_ = lean_box(0);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 0, v___x_374_);
v___x_376_ = v___x_367_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v___x_374_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
else
{
lean_del_object(v___x_367_);
v___y_316_ = v_a_365_;
v___y_317_ = v_fileName_361_;
v___y_318_ = v___x_371_;
v___y_319_ = v___x_372_;
v___y_320_ = v___y_358_;
v___y_321_ = v___y_357_;
v___y_322_ = v___x_369_;
v_toCold_323_ = v___y_353_;
v___y_324_ = v___y_313_;
goto v___jp_315_;
}
}
}
}
v___jp_379_:
{
lean_object* v___x_387_; 
v___x_387_ = l_Lean_Syntax_getTailPos_x3f(v___y_385_, v___y_384_);
lean_dec(v___y_385_);
if (lean_obj_tag(v___x_387_) == 0)
{
lean_inc(v___y_386_);
v___y_353_ = v___y_381_;
v___y_354_ = v___y_382_;
v___y_355_ = v___y_380_;
v___y_356_ = v___y_381_;
v___y_357_ = v___y_384_;
v___y_358_ = v___y_383_;
v___y_359_ = v___y_386_;
v___y_360_ = v___y_386_;
goto v___jp_352_;
}
else
{
lean_object* v_val_388_; 
v_val_388_ = lean_ctor_get(v___x_387_, 0);
lean_inc(v_val_388_);
lean_dec_ref_known(v___x_387_, 1);
v___y_353_ = v___y_381_;
v___y_354_ = v___y_382_;
v___y_355_ = v___y_380_;
v___y_356_ = v___y_381_;
v___y_357_ = v___y_384_;
v___y_358_ = v___y_383_;
v___y_359_ = v___y_386_;
v___y_360_ = v_val_388_;
goto v___jp_352_;
}
}
v___jp_389_:
{
lean_object* v_toCold_393_; lean_object* v_ref_394_; uint8_t v_suppressElabErrors_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___f_398_; lean_object* v_ref_399_; lean_object* v___x_400_; 
v_toCold_393_ = lean_ctor_get(v___y_312_, 0);
v_ref_394_ = lean_ctor_get(v___y_312_, 2);
v_suppressElabErrors_395_ = lean_ctor_get_uint8(v___y_312_, sizeof(void*)*3 + 2);
v___x_396_ = lean_box(v_suppressElabErrors_395_);
v___x_397_ = lean_box(v___y_390_);
v___f_398_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___boxed), 3, 2);
lean_closure_set(v___f_398_, 0, v___x_396_);
lean_closure_set(v___f_398_, 1, v___x_397_);
v_ref_399_ = l_Lean_replaceRef(v_ref_306_, v_ref_394_);
v___x_400_ = l_Lean_Syntax_getPos_x3f(v_ref_399_, v___y_391_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v___x_401_; 
v___x_401_ = lean_unsigned_to_nat(0u);
v___y_380_ = v_suppressElabErrors_395_;
v___y_381_ = v_toCold_393_;
v___y_382_ = v___f_398_;
v___y_383_ = v___y_392_;
v___y_384_ = v___y_391_;
v___y_385_ = v_ref_399_;
v___y_386_ = v___x_401_;
goto v___jp_379_;
}
else
{
lean_object* v_val_402_; 
v_val_402_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_val_402_);
lean_dec_ref_known(v___x_400_, 1);
v___y_380_ = v_suppressElabErrors_395_;
v___y_381_ = v_toCold_393_;
v___y_382_ = v___f_398_;
v___y_383_ = v___y_392_;
v___y_384_ = v___y_391_;
v___y_385_ = v_ref_399_;
v___y_386_ = v_val_402_;
goto v___jp_379_;
}
}
v___jp_404_:
{
if (v___y_407_ == 0)
{
v___y_390_ = v___y_405_;
v___y_391_ = v___y_406_;
v___y_392_ = v_severity_308_;
goto v___jp_389_;
}
else
{
v___y_390_ = v___y_405_;
v___y_391_ = v___y_406_;
v___y_392_ = v___x_403_;
goto v___jp_389_;
}
}
v___jp_408_:
{
if (v___y_409_ == 0)
{
uint8_t v___x_410_; uint8_t v___x_411_; 
v___x_410_ = 1;
v___x_411_ = l_Lean_instBEqMessageSeverity_beq(v_severity_308_, v___x_410_);
if (v___x_411_ == 0)
{
v___y_405_ = v___y_409_;
v___y_406_ = v___y_409_;
v___y_407_ = v___x_411_;
goto v___jp_404_;
}
else
{
lean_object* v___x_412_; lean_object* v___x_413_; uint8_t v___x_414_; 
v___x_412_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_312_);
v___x_413_ = l_Lean_warningAsError;
v___x_414_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__4(v___x_412_, v___x_413_);
lean_dec_ref(v___x_412_);
v___y_405_ = v___y_409_;
v___y_406_ = v___y_409_;
v___y_407_ = v___x_414_;
goto v___jp_404_;
}
}
else
{
lean_object* v___x_415_; lean_object* v___x_416_; 
lean_dec_ref(v_msgData_307_);
v___x_415_ = lean_box(0);
v___x_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
return v___x_416_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44___boxed(lean_object* v_ref_419_, lean_object* v_msgData_420_, lean_object* v_severity_421_, lean_object* v_isSilent_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
uint8_t v_severity_boxed_428_; uint8_t v_isSilent_boxed_429_; lean_object* v_res_430_; 
v_severity_boxed_428_ = lean_unbox(v_severity_421_);
v_isSilent_boxed_429_ = lean_unbox(v_isSilent_422_);
v_res_430_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44(v_ref_419_, v_msgData_420_, v_severity_boxed_428_, v_isSilent_boxed_429_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
lean_dec(v_ref_419_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42(lean_object* v_msgData_431_, uint8_t v_severity_432_, uint8_t v_isSilent_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
lean_object* v_ref_439_; lean_object* v___x_440_; 
v_ref_439_ = lean_ctor_get(v___y_436_, 2);
v___x_440_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44(v_ref_439_, v_msgData_431_, v_severity_432_, v_isSilent_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42___boxed(lean_object* v_msgData_441_, lean_object* v_severity_442_, lean_object* v_isSilent_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
uint8_t v_severity_boxed_449_; uint8_t v_isSilent_boxed_450_; lean_object* v_res_451_; 
v_severity_boxed_449_ = lean_unbox(v_severity_442_);
v_isSilent_boxed_450_ = lean_unbox(v_isSilent_443_);
v_res_451_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42(v_msgData_441_, v_severity_boxed_449_, v_isSilent_boxed_450_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38(lean_object* v_msgData_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
uint8_t v___x_458_; uint8_t v___x_459_; lean_object* v___x_460_; 
v___x_458_ = 1;
v___x_459_ = 0;
v___x_460_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42(v_msgData_452_, v___x_458_, v___x_459_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38___boxed(lean_object* v_msgData_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38(v_msgData_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
lean_dec(v___y_463_);
lean_dec_ref(v___y_462_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37___redArg(lean_object* v_opt_468_, lean_object* v___y_469_){
_start:
{
lean_object* v___x_471_; uint8_t v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_471_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_469_);
v___x_472_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__4(v___x_471_, v_opt_468_);
lean_dec_ref(v___x_471_);
v___x_473_ = lean_box(v___x_472_);
v___x_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37___redArg___boxed(lean_object* v_opt_475_, lean_object* v___y_476_, lean_object* v___y_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37___redArg(v_opt_475_, v___y_476_);
lean_dec_ref(v___y_476_);
lean_dec_ref(v_opt_475_);
return v_res_478_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__1(void){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__0));
v___x_481_ = l_Lean_stringToMessageData(v___x_480_);
return v___x_481_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__3(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__2));
v___x_484_ = l_Lean_stringToMessageData(v___x_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32(lean_object* v_id_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v___x_491_; lean_object* v_env_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_514_; 
v___x_491_ = lean_st_ref_get(v___y_489_);
v_env_492_ = lean_ctor_get(v___x_491_, 0);
lean_inc_ref(v_env_492_);
lean_dec(v___x_491_);
v___x_493_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_494_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37___redArg(v___x_493_, v___y_488_);
v_a_495_ = lean_ctor_get(v___x_494_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_514_ == 0)
{
v___x_497_ = v___x_494_;
v_isShared_498_ = v_isSharedCheck_514_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v___x_494_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_514_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
uint8_t v_isExporting_504_; 
v_isExporting_504_ = lean_ctor_get_uint8(v_env_492_, sizeof(void*)*8);
lean_dec_ref(v_env_492_);
if (v_isExporting_504_ == 0)
{
lean_dec(v_a_495_);
lean_dec(v_id_485_);
goto v___jp_499_;
}
else
{
uint8_t v___x_505_; 
v___x_505_ = l_Lean_isPrivateName(v_id_485_);
if (v___x_505_ == 0)
{
lean_dec(v_a_495_);
lean_dec(v_id_485_);
goto v___jp_499_;
}
else
{
uint8_t v___x_506_; 
v___x_506_ = lean_unbox(v_a_495_);
lean_dec(v_a_495_);
if (v___x_506_ == 0)
{
lean_dec(v_id_485_);
goto v___jp_499_;
}
else
{
lean_object* v___x_507_; uint8_t v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
lean_del_object(v___x_497_);
v___x_507_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__1);
v___x_508_ = 0;
v___x_509_ = l_Lean_MessageData_ofConstName(v_id_485_, v___x_508_);
v___x_510_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_510_, 0, v___x_507_);
lean_ctor_set(v___x_510_, 1, v___x_509_);
v___x_511_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__3);
v___x_512_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_512_, 0, v___x_510_);
lean_ctor_set(v___x_512_, 1, v___x_511_);
v___x_513_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38(v___x_512_, v___y_486_, v___y_487_, v___y_488_, v___y_489_);
return v___x_513_;
}
}
}
v___jp_499_:
{
lean_object* v___x_500_; lean_object* v___x_502_; 
v___x_500_ = lean_box(0);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 0, v___x_500_);
v___x_502_ = v___x_497_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v___x_500_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___boxed(lean_object* v_id_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32(v_id_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__31(lean_object* v_x_522_){
_start:
{
if (lean_obj_tag(v_x_522_) == 0)
{
lean_object* v___x_523_; 
v___x_523_ = lean_box(0);
return v___x_523_;
}
else
{
lean_object* v_head_524_; lean_object* v_tail_525_; lean_object* v_fst_526_; uint8_t v___x_527_; 
v_head_524_ = lean_ctor_get(v_x_522_, 0);
v_tail_525_ = lean_ctor_get(v_x_522_, 1);
v_fst_526_ = lean_ctor_get(v_head_524_, 0);
v___x_527_ = l_Lean_isPrivateName(v_fst_526_);
if (v___x_527_ == 0)
{
v_x_522_ = v_tail_525_;
goto _start;
}
else
{
lean_object* v___x_529_; 
lean_inc(v_head_524_);
v___x_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_529_, 0, v_head_524_);
return v___x_529_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__31___boxed(lean_object* v_x_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__31(v_x_530_);
lean_dec(v_x_530_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26(lean_object* v_id_532_, uint8_t v_enableLog_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_){
_start:
{
lean_object* v___x_539_; lean_object* v_toCold_540_; lean_object* v_env_541_; lean_object* v_currNamespace_542_; lean_object* v_openDecls_543_; lean_object* v___x_544_; lean_object* v_res_545_; lean_object* v___x_546_; 
v___x_539_ = lean_st_ref_get(v___y_537_);
v_toCold_540_ = lean_ctor_get(v___y_536_, 0);
v_env_541_ = lean_ctor_get(v___x_539_, 0);
lean_inc_ref(v_env_541_);
lean_dec(v___x_539_);
v_currNamespace_542_ = lean_ctor_get(v_toCold_540_, 4);
v_openDecls_543_ = lean_ctor_get(v_toCold_540_, 5);
v___x_544_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_536_);
lean_inc(v_openDecls_543_);
lean_inc(v_currNamespace_542_);
v_res_545_ = l_Lean_ResolveName_resolveGlobalName(v_env_541_, v___x_544_, v_currNamespace_542_, v_openDecls_543_, v_id_532_);
lean_dec_ref(v___x_544_);
v___x_546_ = lean_st_ref_get(v___y_537_);
if (v_enableLog_533_ == 0)
{
lean_object* v___x_547_; 
lean_dec(v___x_546_);
v___x_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_547_, 0, v_res_545_);
return v___x_547_;
}
else
{
lean_object* v_env_548_; uint8_t v_isExporting_549_; 
v_env_548_ = lean_ctor_get(v___x_546_, 0);
lean_inc_ref(v_env_548_);
lean_dec(v___x_546_);
v_isExporting_549_ = lean_ctor_get_uint8(v_env_548_, sizeof(void*)*8);
lean_dec_ref(v_env_548_);
if (v_isExporting_549_ == 0)
{
lean_object* v___x_550_; 
v___x_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_550_, 0, v_res_545_);
return v___x_550_;
}
else
{
lean_object* v___x_551_; 
v___x_551_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__31(v_res_545_);
if (lean_obj_tag(v___x_551_) == 1)
{
lean_object* v_val_552_; lean_object* v_fst_553_; lean_object* v___x_554_; 
v_val_552_ = lean_ctor_get(v___x_551_, 0);
lean_inc(v_val_552_);
lean_dec_ref_known(v___x_551_, 1);
v_fst_553_ = lean_ctor_get(v_val_552_, 0);
lean_inc(v_fst_553_);
lean_dec(v_val_552_);
v___x_554_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32(v_fst_553_, v___y_534_, v___y_535_, v___y_536_, v___y_537_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_561_; 
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_561_ == 0)
{
lean_object* v_unused_562_; 
v_unused_562_ = lean_ctor_get(v___x_554_, 0);
lean_dec(v_unused_562_);
v___x_556_ = v___x_554_;
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
else
{
lean_dec(v___x_554_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_559_; 
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 0, v_res_545_);
v___x_559_ = v___x_556_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_res_545_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
else
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_570_; 
lean_dec(v_res_545_);
v_a_563_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_570_ == 0)
{
v___x_565_ = v___x_554_;
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_554_);
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
v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_a_563_);
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
else
{
lean_object* v___x_571_; 
lean_dec(v___x_551_);
v___x_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_571_, 0, v_res_545_);
return v___x_571_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26___boxed(lean_object* v_id_572_, lean_object* v_enableLog_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
uint8_t v_enableLog_boxed_579_; lean_object* v_res_580_; 
v_enableLog_boxed_579_ = lean_unbox(v_enableLog_573_);
v_res_580_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26(v_id_572_, v_enableLog_boxed_579_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20(lean_object* v_view_581_, lean_object* v_findLocalDecl_x3f_582_, lean_object* v_n_583_, lean_object* v_projs_584_, uint8_t v_globalDeclFound_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
lean_object* v___y_592_; lean_object* v___y_593_; uint8_t v_globalDeclFoundNext_594_; lean_object* v___y_595_; lean_object* v___y_596_; lean_object* v___y_597_; lean_object* v___y_598_; lean_object* v_imported_601_; lean_object* v_ctx_602_; lean_object* v_scopes_603_; lean_object* v_givenNameView_604_; uint8_t v___y_606_; 
v_imported_601_ = lean_ctor_get(v_view_581_, 1);
v_ctx_602_ = lean_ctor_get(v_view_581_, 2);
v_scopes_603_ = lean_ctor_get(v_view_581_, 3);
lean_inc(v_scopes_603_);
lean_inc(v_ctx_602_);
lean_inc(v_imported_601_);
lean_inc(v_n_583_);
v_givenNameView_604_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_givenNameView_604_, 0, v_n_583_);
lean_ctor_set(v_givenNameView_604_, 1, v_imported_601_);
lean_ctor_set(v_givenNameView_604_, 2, v_ctx_602_);
lean_ctor_set(v_givenNameView_604_, 3, v_scopes_603_);
if (v_globalDeclFound_585_ == 0)
{
v___y_606_ = v_globalDeclFound_585_;
goto v___jp_605_;
}
else
{
uint8_t v___x_641_; 
v___x_641_ = l_List_isEmpty___redArg(v_projs_584_);
if (v___x_641_ == 0)
{
v___y_606_ = v_globalDeclFound_585_;
goto v___jp_605_;
}
else
{
uint8_t v___x_642_; 
v___x_642_ = 0;
v___y_606_ = v___x_642_;
goto v___jp_605_;
}
}
v___jp_591_:
{
lean_object* v___x_599_; 
v___x_599_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_599_, 0, v___y_592_);
lean_ctor_set(v___x_599_, 1, v_projs_584_);
v_n_583_ = v___y_593_;
v_projs_584_ = v___x_599_;
v_globalDeclFound_585_ = v_globalDeclFoundNext_594_;
v___y_586_ = v___y_595_;
v___y_587_ = v___y_596_;
v___y_588_ = v___y_597_;
v___y_589_ = v___y_598_;
goto _start;
}
v___jp_605_:
{
lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_607_ = lean_box(v___y_606_);
lean_inc_ref(v_findLocalDecl_x3f_582_);
lean_inc_ref(v_givenNameView_604_);
v___x_608_ = lean_apply_2(v_findLocalDecl_x3f_582_, v_givenNameView_604_, v___x_607_);
if (lean_obj_tag(v___x_608_) == 0)
{
if (lean_obj_tag(v_n_583_) == 1)
{
if (v_globalDeclFound_585_ == 0)
{
lean_object* v_pre_609_; lean_object* v_str_610_; uint8_t v_globalDeclFoundNext_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v_pre_609_ = lean_ctor_get(v_n_583_, 0);
lean_inc(v_pre_609_);
v_str_610_ = lean_ctor_get(v_n_583_, 1);
lean_inc_ref(v_str_610_);
lean_dec_ref_known(v_n_583_, 2);
v_globalDeclFoundNext_611_ = 1;
v___x_612_ = l_Lean_MacroScopesView_review(v_givenNameView_604_);
v___x_613_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26(v___x_612_, v_globalDeclFound_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
if (lean_obj_tag(v___x_613_) == 0)
{
lean_object* v_a_614_; lean_object* v___x_615_; lean_object* v_r_616_; uint8_t v___x_617_; 
v_a_614_ = lean_ctor_get(v___x_613_, 0);
lean_inc(v_a_614_);
lean_dec_ref_known(v___x_613_, 1);
v___x_615_ = lean_box(0);
v_r_616_ = l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__27(v_a_614_, v___x_615_);
v___x_617_ = l_List_isEmpty___redArg(v_r_616_);
lean_dec(v_r_616_);
if (v___x_617_ == 0)
{
v___y_592_ = v_str_610_;
v___y_593_ = v_pre_609_;
v_globalDeclFoundNext_594_ = v_globalDeclFoundNext_611_;
v___y_595_ = v___y_586_;
v___y_596_ = v___y_587_;
v___y_597_ = v___y_588_;
v___y_598_ = v___y_589_;
goto v___jp_591_;
}
else
{
v___y_592_ = v_str_610_;
v___y_593_ = v_pre_609_;
v_globalDeclFoundNext_594_ = v_globalDeclFound_585_;
v___y_595_ = v___y_586_;
v___y_596_ = v___y_587_;
v___y_597_ = v___y_588_;
v___y_598_ = v___y_589_;
goto v___jp_591_;
}
}
else
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_625_; 
lean_dec_ref(v_str_610_);
lean_dec(v_pre_609_);
lean_dec(v_projs_584_);
lean_dec_ref(v_findLocalDecl_x3f_582_);
v_a_618_ = lean_ctor_get(v___x_613_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_613_);
if (v_isSharedCheck_625_ == 0)
{
v___x_620_ = v___x_613_;
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_613_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_623_; 
if (v_isShared_621_ == 0)
{
v___x_623_ = v___x_620_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_618_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
else
{
lean_object* v_pre_626_; lean_object* v_str_627_; 
lean_dec_ref_known(v_givenNameView_604_, 4);
v_pre_626_ = lean_ctor_get(v_n_583_, 0);
lean_inc(v_pre_626_);
v_str_627_ = lean_ctor_get(v_n_583_, 1);
lean_inc_ref(v_str_627_);
lean_dec_ref_known(v_n_583_, 2);
v___y_592_ = v_str_627_;
v___y_593_ = v_pre_626_;
v_globalDeclFoundNext_594_ = v_globalDeclFound_585_;
v___y_595_ = v___y_586_;
v___y_596_ = v___y_587_;
v___y_597_ = v___y_588_;
v___y_598_ = v___y_589_;
goto v___jp_591_;
}
}
else
{
lean_object* v___x_628_; lean_object* v___x_629_; 
lean_dec_ref_known(v_givenNameView_604_, 4);
lean_dec(v_projs_584_);
lean_dec(v_n_583_);
lean_dec_ref(v_findLocalDecl_x3f_582_);
v___x_628_ = lean_box(0);
v___x_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
return v___x_629_;
}
}
else
{
lean_object* v_val_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_640_; 
lean_dec_ref_known(v_givenNameView_604_, 4);
lean_dec(v_n_583_);
lean_dec_ref(v_findLocalDecl_x3f_582_);
v_val_630_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_640_ == 0)
{
v___x_632_ = v___x_608_;
v_isShared_633_ = v_isSharedCheck_640_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_val_630_);
lean_dec(v___x_608_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_640_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_637_; 
v___x_634_ = l_Lean_LocalDecl_toExpr(v_val_630_);
v___x_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
lean_ctor_set(v___x_635_, 1, v_projs_584_);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 0, v___x_635_);
v___x_637_ = v___x_632_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v___x_635_);
v___x_637_ = v_reuseFailAlloc_639_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
lean_object* v___x_638_; 
v___x_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
return v___x_638_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20___boxed(lean_object* v_view_643_, lean_object* v_findLocalDecl_x3f_644_, lean_object* v_n_645_, lean_object* v_projs_646_, lean_object* v_globalDeclFound_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
uint8_t v_globalDeclFound_boxed_653_; lean_object* v_res_654_; 
v_globalDeclFound_boxed_653_ = lean_unbox(v_globalDeclFound_647_);
v_res_654_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20(v_view_643_, v_findLocalDecl_x3f_644_, v_n_645_, v_projs_646_, v_globalDeclFound_boxed_653_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec_ref(v_view_643_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__17___redArg(lean_object* v_t_655_, lean_object* v_k_656_){
_start:
{
if (lean_obj_tag(v_t_655_) == 0)
{
lean_object* v_k_657_; lean_object* v_v_658_; lean_object* v_l_659_; lean_object* v_r_660_; uint8_t v___x_661_; 
v_k_657_ = lean_ctor_get(v_t_655_, 1);
v_v_658_ = lean_ctor_get(v_t_655_, 2);
v_l_659_ = lean_ctor_get(v_t_655_, 3);
v_r_660_ = lean_ctor_get(v_t_655_, 4);
v___x_661_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_656_, v_k_657_);
switch(v___x_661_)
{
case 0:
{
v_t_655_ = v_l_659_;
goto _start;
}
case 1:
{
lean_object* v___x_663_; 
lean_inc(v_v_658_);
v___x_663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_663_, 0, v_v_658_);
return v___x_663_;
}
default: 
{
v_t_655_ = v_r_660_;
goto _start;
}
}
}
else
{
lean_object* v___x_665_; 
v___x_665_ = lean_box(0);
return v___x_665_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__17___redArg___boxed(lean_object* v_t_666_, lean_object* v_k_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__17___redArg(v_t_666_, v_k_667_);
lean_dec(v_k_667_);
lean_dec(v_t_666_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg___lam__0(lean_object* v_localDecl_669_, lean_object* v_givenName_670_){
_start:
{
lean_object* v___x_671_; uint8_t v___x_672_; 
v___x_671_ = l_Lean_LocalDecl_userName(v_localDecl_669_);
v___x_672_ = lean_name_eq(v___x_671_, v_givenName_670_);
lean_dec(v___x_671_);
if (v___x_672_ == 0)
{
lean_object* v___x_673_; 
lean_dec_ref(v_localDecl_669_);
v___x_673_ = lean_box(0);
return v___x_673_;
}
else
{
lean_object* v___x_674_; 
v___x_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_674_, 0, v_localDecl_669_);
return v___x_674_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg___lam__0___boxed(lean_object* v_localDecl_675_, lean_object* v_givenName_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg___lam__0(v_localDecl_675_, v_givenName_676_);
lean_dec(v_givenName_676_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg(lean_object* v_givenName_678_, uint8_t v_skipAuxDecl_679_, lean_object* v_auxDeclToFullName_680_, lean_object* v___x_681_, lean_object* v_givenNameView_682_, lean_object* v_as_683_, lean_object* v_i_684_){
_start:
{
lean_object* v_zero_685_; uint8_t v_isZero_686_; 
v_zero_685_ = lean_unsigned_to_nat(0u);
v_isZero_686_ = lean_nat_dec_eq(v_i_684_, v_zero_685_);
if (v_isZero_686_ == 1)
{
lean_object* v___x_687_; 
lean_dec(v_i_684_);
lean_dec_ref(v_givenNameView_682_);
lean_dec(v___x_681_);
v___x_687_ = lean_box(0);
return v___x_687_;
}
else
{
lean_object* v_one_688_; lean_object* v_n_689_; lean_object* v___y_691_; lean_object* v___x_693_; 
v_one_688_ = lean_unsigned_to_nat(1u);
v_n_689_ = lean_nat_sub(v_i_684_, v_one_688_);
lean_dec(v_i_684_);
v___x_693_ = lean_array_fget_borrowed(v_as_683_, v_n_689_);
if (lean_obj_tag(v___x_693_) == 0)
{
v___y_691_ = v___x_693_;
goto v___jp_690_;
}
else
{
lean_object* v_val_694_; uint8_t v___x_695_; 
v_val_694_ = lean_ctor_get(v___x_693_, 0);
v___x_695_ = l_Lean_LocalDecl_isAuxDecl(v_val_694_);
if (v___x_695_ == 0)
{
lean_object* v___x_696_; 
lean_inc(v_val_694_);
v___x_696_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg___lam__0(v_val_694_, v_givenName_678_);
v___y_691_ = v___x_696_;
goto v___jp_690_;
}
else
{
if (v_skipAuxDecl_679_ == 0)
{
if (v___x_695_ == 0)
{
v_i_684_ = v_n_689_;
goto _start;
}
else
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = l_Lean_LocalDecl_fvarId(v_val_694_);
v___x_699_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__17___redArg(v_auxDeclToFullName_680_, v___x_698_);
lean_dec(v___x_698_);
if (lean_obj_tag(v___x_699_) == 1)
{
lean_object* v_val_700_; lean_object* v_fullDeclView_701_; lean_object* v___y_703_; lean_object* v_name_724_; lean_object* v___x_725_; 
v_val_700_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_val_700_);
lean_dec_ref_known(v___x_699_, 1);
v_fullDeclView_701_ = l_Lean_extractMacroScopes(v_val_700_);
v_name_724_ = lean_ctor_get(v_fullDeclView_701_, 0);
lean_inc_n(v_name_724_, 2);
v___x_725_ = l_Lean_privateToUserName_x3f(v_name_724_);
if (lean_obj_tag(v___x_725_) == 0)
{
v___y_703_ = v_name_724_;
goto v___jp_702_;
}
else
{
lean_object* v_val_726_; 
lean_dec(v_name_724_);
v_val_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_val_726_);
lean_dec_ref_known(v___x_725_, 1);
v___y_703_ = v_val_726_;
goto v___jp_702_;
}
v___jp_702_:
{
lean_object* v_imported_704_; lean_object* v_ctx_705_; lean_object* v_scopes_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_722_; 
v_imported_704_ = lean_ctor_get(v_fullDeclView_701_, 1);
v_ctx_705_ = lean_ctor_get(v_fullDeclView_701_, 2);
v_scopes_706_ = lean_ctor_get(v_fullDeclView_701_, 3);
v_isSharedCheck_722_ = !lean_is_exclusive(v_fullDeclView_701_);
if (v_isSharedCheck_722_ == 0)
{
lean_object* v_unused_723_; 
v_unused_723_ = lean_ctor_get(v_fullDeclView_701_, 0);
lean_dec(v_unused_723_);
v___x_708_ = v_fullDeclView_701_;
v_isShared_709_ = v_isSharedCheck_722_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_scopes_706_);
lean_inc(v_ctx_705_);
lean_inc(v_imported_704_);
lean_dec(v_fullDeclView_701_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_722_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v_fullDeclView_711_; 
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 0, v___y_703_);
v_fullDeclView_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___y_703_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_imported_704_);
lean_ctor_set(v_reuseFailAlloc_721_, 2, v_ctx_705_);
lean_ctor_set(v_reuseFailAlloc_721_, 3, v_scopes_706_);
v_fullDeclView_711_ = v_reuseFailAlloc_721_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
lean_object* v_fullDeclName_712_; uint8_t v___x_713_; 
lean_inc_ref(v_fullDeclView_711_);
v_fullDeclName_712_ = l_Lean_MacroScopesView_review(v_fullDeclView_711_);
v___x_713_ = l_Lean_Name_isPrefixOf(v___x_681_, v_fullDeclName_712_);
if (v___x_713_ == 0)
{
lean_object* v___x_714_; 
lean_dec_ref(v_fullDeclView_711_);
lean_inc(v___x_681_);
lean_inc_ref(v_givenNameView_682_);
lean_inc(v_val_694_);
v___x_714_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_val_694_, v_givenNameView_682_, v_fullDeclName_712_, v___x_681_);
lean_dec(v_fullDeclName_712_);
v___y_691_ = v___x_714_;
goto v___jp_690_;
}
else
{
lean_object* v___x_715_; lean_object* v_localDeclNameView_716_; uint8_t v___x_717_; 
lean_dec(v_fullDeclName_712_);
v___x_715_ = l_Lean_LocalDecl_userName(v_val_694_);
v_localDeclNameView_716_ = l_Lean_extractMacroScopes(v___x_715_);
v___x_717_ = l_Lean_MacroScopesView_isSuffixOf(v_localDeclNameView_716_, v_givenNameView_682_);
lean_dec_ref(v_localDeclNameView_716_);
if (v___x_717_ == 0)
{
lean_dec_ref(v_fullDeclView_711_);
v_i_684_ = v_n_689_;
goto _start;
}
else
{
uint8_t v___x_719_; 
v___x_719_ = l_Lean_MacroScopesView_isSuffixOf(v_givenNameView_682_, v_fullDeclView_711_);
lean_dec_ref(v_fullDeclView_711_);
if (v___x_719_ == 0)
{
v_i_684_ = v_n_689_;
goto _start;
}
else
{
lean_inc_ref(v___x_693_);
v___y_691_ = v___x_693_;
goto v___jp_690_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_727_; 
lean_dec(v___x_699_);
lean_inc(v_val_694_);
v___x_727_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg___lam__0(v_val_694_, v_givenName_678_);
v___y_691_ = v___x_727_;
goto v___jp_690_;
}
}
}
else
{
v_i_684_ = v_n_689_;
goto _start;
}
}
}
v___jp_690_:
{
if (lean_obj_tag(v___y_691_) == 0)
{
v_i_684_ = v_n_689_;
goto _start;
}
else
{
lean_dec(v_n_689_);
lean_dec_ref(v_givenNameView_682_);
lean_dec(v___x_681_);
return v___y_691_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg___boxed(lean_object* v_givenName_729_, lean_object* v_skipAuxDecl_730_, lean_object* v_auxDeclToFullName_731_, lean_object* v___x_732_, lean_object* v_givenNameView_733_, lean_object* v_as_734_, lean_object* v_i_735_){
_start:
{
uint8_t v_skipAuxDecl_boxed_736_; lean_object* v_res_737_; 
v_skipAuxDecl_boxed_736_ = lean_unbox(v_skipAuxDecl_730_);
v_res_737_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg(v_givenName_729_, v_skipAuxDecl_boxed_736_, v_auxDeclToFullName_731_, v___x_732_, v_givenNameView_733_, v_as_734_, v_i_735_);
lean_dec_ref(v_as_734_);
lean_dec(v_auxDeclToFullName_731_);
lean_dec(v_givenName_729_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24___redArg(lean_object* v_givenName_738_, uint8_t v_skipAuxDecl_739_, lean_object* v_auxDeclToFullName_740_, lean_object* v___x_741_, lean_object* v_givenNameView_742_, lean_object* v_as_743_, lean_object* v_i_744_){
_start:
{
lean_object* v_zero_745_; uint8_t v_isZero_746_; 
v_zero_745_ = lean_unsigned_to_nat(0u);
v_isZero_746_ = lean_nat_dec_eq(v_i_744_, v_zero_745_);
if (v_isZero_746_ == 1)
{
lean_object* v___x_747_; 
lean_dec(v_i_744_);
lean_dec_ref(v_givenNameView_742_);
lean_dec(v___x_741_);
v___x_747_ = lean_box(0);
return v___x_747_;
}
else
{
lean_object* v_one_748_; lean_object* v_n_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v_one_748_ = lean_unsigned_to_nat(1u);
v_n_749_ = lean_nat_sub(v_i_744_, v_one_748_);
lean_dec(v_i_744_);
v___x_750_ = lean_array_fget_borrowed(v_as_743_, v_n_749_);
lean_inc_ref(v_givenNameView_742_);
lean_inc(v___x_741_);
v___x_751_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21(v_givenName_738_, v_skipAuxDecl_739_, v_auxDeclToFullName_740_, v___x_741_, v_givenNameView_742_, v___x_750_);
if (lean_obj_tag(v___x_751_) == 0)
{
v_i_744_ = v_n_749_;
goto _start;
}
else
{
lean_dec(v_n_749_);
lean_dec_ref(v_givenNameView_742_);
lean_dec(v___x_741_);
return v___x_751_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21(lean_object* v_givenName_753_, uint8_t v_skipAuxDecl_754_, lean_object* v_auxDeclToFullName_755_, lean_object* v___x_756_, lean_object* v_givenNameView_757_, lean_object* v_x_758_){
_start:
{
if (lean_obj_tag(v_x_758_) == 0)
{
lean_object* v_cs_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v_cs_759_ = lean_ctor_get(v_x_758_, 0);
v___x_760_ = lean_array_get_size(v_cs_759_);
v___x_761_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24___redArg(v_givenName_753_, v_skipAuxDecl_754_, v_auxDeclToFullName_755_, v___x_756_, v_givenNameView_757_, v_cs_759_, v___x_760_);
return v___x_761_;
}
else
{
lean_object* v_vs_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v_vs_762_ = lean_ctor_get(v_x_758_, 0);
v___x_763_ = lean_array_get_size(v_vs_762_);
v___x_764_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg(v_givenName_753_, v_skipAuxDecl_754_, v_auxDeclToFullName_755_, v___x_756_, v_givenNameView_757_, v_vs_762_, v___x_763_);
return v___x_764_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21___boxed(lean_object* v_givenName_765_, lean_object* v_skipAuxDecl_766_, lean_object* v_auxDeclToFullName_767_, lean_object* v___x_768_, lean_object* v_givenNameView_769_, lean_object* v_x_770_){
_start:
{
uint8_t v_skipAuxDecl_boxed_771_; lean_object* v_res_772_; 
v_skipAuxDecl_boxed_771_ = lean_unbox(v_skipAuxDecl_766_);
v_res_772_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21(v_givenName_765_, v_skipAuxDecl_boxed_771_, v_auxDeclToFullName_767_, v___x_768_, v_givenNameView_769_, v_x_770_);
lean_dec_ref(v_x_770_);
lean_dec(v_auxDeclToFullName_767_);
lean_dec(v_givenName_765_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24___redArg___boxed(lean_object* v_givenName_773_, lean_object* v_skipAuxDecl_774_, lean_object* v_auxDeclToFullName_775_, lean_object* v___x_776_, lean_object* v_givenNameView_777_, lean_object* v_as_778_, lean_object* v_i_779_){
_start:
{
uint8_t v_skipAuxDecl_boxed_780_; lean_object* v_res_781_; 
v_skipAuxDecl_boxed_780_ = lean_unbox(v_skipAuxDecl_774_);
v_res_781_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24___redArg(v_givenName_773_, v_skipAuxDecl_boxed_780_, v_auxDeclToFullName_775_, v___x_776_, v_givenNameView_777_, v_as_778_, v_i_779_);
lean_dec_ref(v_as_778_);
lean_dec(v_auxDeclToFullName_775_);
lean_dec(v_givenName_773_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18(lean_object* v_givenName_782_, uint8_t v_skipAuxDecl_783_, lean_object* v_auxDeclToFullName_784_, lean_object* v___x_785_, lean_object* v_givenNameView_786_, lean_object* v_t_787_){
_start:
{
lean_object* v_root_788_; lean_object* v_tail_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v_root_788_ = lean_ctor_get(v_t_787_, 0);
v_tail_789_ = lean_ctor_get(v_t_787_, 1);
v___x_790_ = lean_array_get_size(v_tail_789_);
lean_inc_ref(v_givenNameView_786_);
lean_inc(v___x_785_);
v___x_791_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg(v_givenName_782_, v_skipAuxDecl_783_, v_auxDeclToFullName_784_, v___x_785_, v_givenNameView_786_, v_tail_789_, v___x_790_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v___x_792_; 
v___x_792_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21(v_givenName_782_, v_skipAuxDecl_783_, v_auxDeclToFullName_784_, v___x_785_, v_givenNameView_786_, v_root_788_);
return v___x_792_;
}
else
{
lean_dec_ref(v_givenNameView_786_);
lean_dec(v___x_785_);
return v___x_791_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18___boxed(lean_object* v_givenName_793_, lean_object* v_skipAuxDecl_794_, lean_object* v_auxDeclToFullName_795_, lean_object* v___x_796_, lean_object* v_givenNameView_797_, lean_object* v_t_798_){
_start:
{
uint8_t v_skipAuxDecl_boxed_799_; lean_object* v_res_800_; 
v_skipAuxDecl_boxed_799_ = lean_unbox(v_skipAuxDecl_794_);
v_res_800_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18(v_givenName_793_, v_skipAuxDecl_boxed_799_, v_auxDeclToFullName_795_, v___x_796_, v_givenNameView_797_, v_t_798_);
lean_dec_ref(v_t_798_);
lean_dec(v_auxDeclToFullName_795_);
lean_dec(v_givenName_793_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___redArg(lean_object* v_localDecl_x3f_801_, lean_object* v_givenName_802_, lean_object* v_as_803_, lean_object* v_i_804_){
_start:
{
lean_object* v_zero_805_; uint8_t v_isZero_806_; 
v_zero_805_ = lean_unsigned_to_nat(0u);
v_isZero_806_ = lean_nat_dec_eq(v_i_804_, v_zero_805_);
if (v_isZero_806_ == 1)
{
lean_object* v___x_807_; 
lean_dec(v_i_804_);
v___x_807_ = lean_box(0);
return v___x_807_;
}
else
{
lean_object* v_one_808_; lean_object* v_n_809_; lean_object* v___y_811_; lean_object* v___x_813_; 
v_one_808_ = lean_unsigned_to_nat(1u);
v_n_809_ = lean_nat_sub(v_i_804_, v_one_808_);
lean_dec(v_i_804_);
v___x_813_ = lean_array_fget_borrowed(v_as_803_, v_n_809_);
if (lean_obj_tag(v___x_813_) == 0)
{
v___y_811_ = v___x_813_;
goto v___jp_810_;
}
else
{
lean_object* v_val_814_; uint8_t v___x_815_; 
v_val_814_ = lean_ctor_get(v___x_813_, 0);
v___x_815_ = l_Lean_LocalDecl_isAuxDecl(v_val_814_);
if (v___x_815_ == 0)
{
v___y_811_ = v_localDecl_x3f_801_;
goto v___jp_810_;
}
else
{
lean_object* v___x_816_; uint8_t v___x_817_; 
v___x_816_ = l_Lean_LocalDecl_userName(v_val_814_);
v___x_817_ = lean_name_eq(v___x_816_, v_givenName_802_);
lean_dec(v___x_816_);
if (v___x_817_ == 0)
{
v_i_804_ = v_n_809_;
goto _start;
}
else
{
v___y_811_ = v___x_813_;
goto v___jp_810_;
}
}
}
v___jp_810_:
{
if (lean_obj_tag(v___y_811_) == 0)
{
v_i_804_ = v_n_809_;
goto _start;
}
else
{
lean_dec(v_n_809_);
lean_inc_ref(v___y_811_);
return v___y_811_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___redArg___boxed(lean_object* v_localDecl_x3f_819_, lean_object* v_givenName_820_, lean_object* v_as_821_, lean_object* v_i_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___redArg(v_localDecl_x3f_819_, v_givenName_820_, v_as_821_, v_i_822_);
lean_dec_ref(v_as_821_);
lean_dec(v_givenName_820_);
lean_dec(v_localDecl_x3f_819_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28___redArg(lean_object* v_localDecl_x3f_824_, lean_object* v_givenName_825_, lean_object* v_as_826_, lean_object* v_i_827_){
_start:
{
lean_object* v_zero_828_; uint8_t v_isZero_829_; 
v_zero_828_ = lean_unsigned_to_nat(0u);
v_isZero_829_ = lean_nat_dec_eq(v_i_827_, v_zero_828_);
if (v_isZero_829_ == 1)
{
lean_object* v___x_830_; 
lean_dec(v_i_827_);
v___x_830_ = lean_box(0);
return v___x_830_;
}
else
{
lean_object* v_one_831_; lean_object* v_n_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v_one_831_ = lean_unsigned_to_nat(1u);
v_n_832_ = lean_nat_sub(v_i_827_, v_one_831_);
lean_dec(v_i_827_);
v___x_833_ = lean_array_fget_borrowed(v_as_826_, v_n_832_);
v___x_834_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24(v_localDecl_x3f_824_, v_givenName_825_, v___x_833_);
if (lean_obj_tag(v___x_834_) == 0)
{
v_i_827_ = v_n_832_;
goto _start;
}
else
{
lean_dec(v_n_832_);
return v___x_834_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24(lean_object* v_localDecl_x3f_836_, lean_object* v_givenName_837_, lean_object* v_x_838_){
_start:
{
if (lean_obj_tag(v_x_838_) == 0)
{
lean_object* v_cs_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v_cs_839_ = lean_ctor_get(v_x_838_, 0);
v___x_840_ = lean_array_get_size(v_cs_839_);
v___x_841_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28___redArg(v_localDecl_x3f_836_, v_givenName_837_, v_cs_839_, v___x_840_);
return v___x_841_;
}
else
{
lean_object* v_vs_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v_vs_842_ = lean_ctor_get(v_x_838_, 0);
v___x_843_ = lean_array_get_size(v_vs_842_);
v___x_844_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___redArg(v_localDecl_x3f_836_, v_givenName_837_, v_vs_842_, v___x_843_);
return v___x_844_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24___boxed(lean_object* v_localDecl_x3f_845_, lean_object* v_givenName_846_, lean_object* v_x_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24(v_localDecl_x3f_845_, v_givenName_846_, v_x_847_);
lean_dec_ref(v_x_847_);
lean_dec(v_givenName_846_);
lean_dec(v_localDecl_x3f_845_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28___redArg___boxed(lean_object* v_localDecl_x3f_849_, lean_object* v_givenName_850_, lean_object* v_as_851_, lean_object* v_i_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28___redArg(v_localDecl_x3f_849_, v_givenName_850_, v_as_851_, v_i_852_);
lean_dec_ref(v_as_851_);
lean_dec(v_givenName_850_);
lean_dec(v_localDecl_x3f_849_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19(lean_object* v_localDecl_x3f_854_, lean_object* v_givenName_855_, lean_object* v_t_856_){
_start:
{
lean_object* v_root_857_; lean_object* v_tail_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v_root_857_ = lean_ctor_get(v_t_856_, 0);
v_tail_858_ = lean_ctor_get(v_t_856_, 1);
v___x_859_ = lean_array_get_size(v_tail_858_);
v___x_860_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___redArg(v_localDecl_x3f_854_, v_givenName_855_, v_tail_858_, v___x_859_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v___x_861_; 
v___x_861_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24(v_localDecl_x3f_854_, v_givenName_855_, v_root_857_);
return v___x_861_;
}
else
{
return v___x_860_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19___boxed(lean_object* v_localDecl_x3f_862_, lean_object* v_givenName_863_, lean_object* v_t_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19(v_localDecl_x3f_862_, v_givenName_863_, v_t_864_);
lean_dec_ref(v_t_864_);
lean_dec(v_givenName_863_);
lean_dec(v_localDecl_x3f_862_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11___lam__0(lean_object* v_auxDeclToFullName_866_, lean_object* v_currNamespace_867_, lean_object* v_decls_868_, lean_object* v_givenNameView_869_, uint8_t v_skipAuxDecl_870_){
_start:
{
lean_object* v_givenName_871_; lean_object* v_localDecl_x3f_872_; 
lean_inc_ref(v_givenNameView_869_);
v_givenName_871_ = l_Lean_MacroScopesView_review(v_givenNameView_869_);
v_localDecl_x3f_872_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18(v_givenName_871_, v_skipAuxDecl_870_, v_auxDeclToFullName_866_, v_currNamespace_867_, v_givenNameView_869_, v_decls_868_);
if (lean_obj_tag(v_localDecl_x3f_872_) == 0)
{
if (v_skipAuxDecl_870_ == 0)
{
lean_object* v___x_873_; 
v___x_873_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19(v_localDecl_x3f_872_, v_givenName_871_, v_decls_868_);
lean_dec(v_givenName_871_);
return v___x_873_;
}
else
{
lean_dec(v_givenName_871_);
return v_localDecl_x3f_872_;
}
}
else
{
lean_dec(v_givenName_871_);
return v_localDecl_x3f_872_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11___lam__0___boxed(lean_object* v_auxDeclToFullName_874_, lean_object* v_currNamespace_875_, lean_object* v_decls_876_, lean_object* v_givenNameView_877_, lean_object* v_skipAuxDecl_878_){
_start:
{
uint8_t v_skipAuxDecl_boxed_879_; lean_object* v_res_880_; 
v_skipAuxDecl_boxed_879_ = lean_unbox(v_skipAuxDecl_878_);
v_res_880_ = l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11___lam__0(v_auxDeclToFullName_874_, v_currNamespace_875_, v_decls_876_, v_givenNameView_877_, v_skipAuxDecl_boxed_879_);
lean_dec_ref(v_decls_876_);
lean_dec(v_auxDeclToFullName_874_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11(lean_object* v_n_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
lean_object* v_lctx_887_; lean_object* v_toCold_888_; lean_object* v_decls_889_; lean_object* v_auxDeclToFullName_890_; lean_object* v_currNamespace_891_; lean_object* v_view_892_; lean_object* v_name_893_; lean_object* v_findLocalDecl_x3f_894_; lean_object* v___x_895_; uint8_t v___x_896_; lean_object* v___x_897_; 
v_lctx_887_ = lean_ctor_get(v___y_882_, 2);
v_toCold_888_ = lean_ctor_get(v___y_884_, 0);
v_decls_889_ = lean_ctor_get(v_lctx_887_, 1);
v_auxDeclToFullName_890_ = lean_ctor_get(v_lctx_887_, 2);
v_currNamespace_891_ = lean_ctor_get(v_toCold_888_, 4);
v_view_892_ = l_Lean_extractMacroScopes(v_n_881_);
v_name_893_ = lean_ctor_get(v_view_892_, 0);
lean_inc(v_name_893_);
lean_inc_ref(v_decls_889_);
lean_inc(v_currNamespace_891_);
lean_inc(v_auxDeclToFullName_890_);
v_findLocalDecl_x3f_894_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11___lam__0___boxed), 5, 3);
lean_closure_set(v_findLocalDecl_x3f_894_, 0, v_auxDeclToFullName_890_);
lean_closure_set(v_findLocalDecl_x3f_894_, 1, v_currNamespace_891_);
lean_closure_set(v_findLocalDecl_x3f_894_, 2, v_decls_889_);
v___x_895_ = lean_box(0);
v___x_896_ = 0;
v___x_897_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20(v_view_892_, v_findLocalDecl_x3f_894_, v_name_893_, v___x_895_, v___x_896_, v___y_882_, v___y_883_, v___y_884_, v___y_885_);
lean_dec_ref(v_view_892_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11___boxed(lean_object* v_n_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11(v_n_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5___lam__0(uint8_t v___x_905_, lean_object* v_n_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11(v_n_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_926_; 
v_a_913_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_926_ == 0)
{
v___x_915_ = v___x_912_;
v_isShared_916_ = v_isSharedCheck_926_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v___x_912_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_926_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
if (lean_obj_tag(v_a_913_) == 0)
{
uint8_t v___x_917_; lean_object* v___x_918_; lean_object* v___x_920_; 
v___x_917_ = 1;
v___x_918_ = lean_box(v___x_917_);
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 0, v___x_918_);
v___x_920_ = v___x_915_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_918_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
else
{
lean_object* v___x_922_; lean_object* v___x_924_; 
lean_dec_ref_known(v_a_913_, 1);
v___x_922_ = lean_box(v___x_905_);
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 0, v___x_922_);
v___x_924_ = v___x_915_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_922_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
else
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_934_; 
v_a_927_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_934_ == 0)
{
v___x_929_ = v___x_912_;
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_912_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_932_; 
if (v_isShared_930_ == 0)
{
v___x_932_ = v___x_929_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_a_927_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5___lam__0___boxed(lean_object* v___x_935_, lean_object* v_n_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
uint8_t v___x_44191__boxed_942_; lean_object* v_res_943_; 
v___x_44191__boxed_942_ = lean_unbox(v___x_935_);
v_res_943_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5___lam__0(v___x_44191__boxed_942_, v_n_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22___lam__0(lean_object* v___x_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_950_, 0, v___x_944_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22___lam__0___boxed(lean_object* v___x_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22___lam__0(v___x_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43___redArg(lean_object* v_opt_958_, lean_object* v___y_959_){
_start:
{
lean_object* v___x_961_; uint8_t v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_961_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_959_);
v___x_962_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__4(v___x_961_, v_opt_958_);
lean_dec_ref(v___x_961_);
v___x_963_ = lean_box(v___x_962_);
v___x_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
v___x_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_965_, 0, v___x_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43___redArg___boxed(lean_object* v_opt_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43___redArg(v_opt_966_, v___y_967_);
lean_dec_ref(v___y_967_);
lean_dec_ref(v_opt_966_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48(lean_object* v_ref_972_, lean_object* v_msgData_973_, uint8_t v_severity_974_, uint8_t v_isSilent_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v_a_982_; uint8_t v___y_986_; lean_object* v___y_987_; lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___y_991_; uint8_t v___y_992_; lean_object* v_toCold_993_; lean_object* v___y_994_; lean_object* v___y_1022_; lean_object* v___y_1023_; uint8_t v___y_1024_; lean_object* v___y_1025_; uint8_t v___y_1026_; lean_object* v___y_1027_; uint8_t v___y_1028_; lean_object* v___y_1029_; lean_object* v___y_1048_; uint8_t v___y_1049_; lean_object* v___y_1050_; uint8_t v___y_1051_; lean_object* v___y_1052_; uint8_t v___y_1053_; lean_object* v___y_1054_; uint8_t v___y_1058_; uint8_t v___y_1059_; uint8_t v___y_1060_; uint8_t v___x_1071_; uint8_t v___y_1073_; uint8_t v___y_1074_; uint8_t v___y_1075_; uint8_t v___y_1077_; uint8_t v___x_1085_; 
v___x_1071_ = 2;
v___x_1085_ = l_Lean_instBEqMessageSeverity_beq(v_severity_974_, v___x_1071_);
if (v___x_1085_ == 0)
{
v___y_1077_ = v___x_1085_;
goto v___jp_1076_;
}
else
{
uint8_t v___x_1086_; 
lean_inc_ref(v_msgData_973_);
v___x_1086_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_973_);
v___y_1077_ = v___x_1086_;
goto v___jp_1076_;
}
v___jp_981_:
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_983_, 0, v_a_982_);
v___x_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
return v___x_984_;
}
v___jp_985_:
{
lean_object* v_currNamespace_995_; lean_object* v_openDecls_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v_env_1001_; lean_object* v_nextMacroScope_1002_; lean_object* v_ngen_1003_; lean_object* v_auxDeclNGen_1004_; lean_object* v_traceState_1005_; lean_object* v_cache_1006_; lean_object* v_recordedDeps_1007_; lean_object* v_messages_1008_; lean_object* v_infoState_1009_; lean_object* v_snapshotTasks_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1020_; 
v_currNamespace_995_ = lean_ctor_get(v_toCold_993_, 4);
v_openDecls_996_ = lean_ctor_get(v_toCold_993_, 5);
lean_inc(v_openDecls_996_);
lean_inc(v_currNamespace_995_);
v___x_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_997_, 0, v_currNamespace_995_);
lean_ctor_set(v___x_997_, 1, v_openDecls_996_);
v___x_998_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
lean_ctor_set(v___x_998_, 1, v___y_990_);
lean_inc_ref(v___y_989_);
lean_inc_ref(v___y_991_);
v___x_999_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_999_, 0, v___y_991_);
lean_ctor_set(v___x_999_, 1, v___y_987_);
lean_ctor_set(v___x_999_, 2, v___y_988_);
lean_ctor_set(v___x_999_, 3, v___y_989_);
lean_ctor_set(v___x_999_, 4, v___x_998_);
lean_ctor_set_uint8(v___x_999_, sizeof(void*)*5, v___y_986_);
lean_ctor_set_uint8(v___x_999_, sizeof(void*)*5 + 1, v___y_992_);
lean_ctor_set_uint8(v___x_999_, sizeof(void*)*5 + 2, v_isSilent_975_);
v___x_1000_ = lean_st_ref_take(v___y_994_);
v_env_1001_ = lean_ctor_get(v___x_1000_, 0);
v_nextMacroScope_1002_ = lean_ctor_get(v___x_1000_, 1);
v_ngen_1003_ = lean_ctor_get(v___x_1000_, 2);
v_auxDeclNGen_1004_ = lean_ctor_get(v___x_1000_, 3);
v_traceState_1005_ = lean_ctor_get(v___x_1000_, 4);
v_cache_1006_ = lean_ctor_get(v___x_1000_, 5);
v_recordedDeps_1007_ = lean_ctor_get(v___x_1000_, 6);
v_messages_1008_ = lean_ctor_get(v___x_1000_, 7);
v_infoState_1009_ = lean_ctor_get(v___x_1000_, 8);
v_snapshotTasks_1010_ = lean_ctor_get(v___x_1000_, 9);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1012_ = v___x_1000_;
v_isShared_1013_ = v_isSharedCheck_1020_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_snapshotTasks_1010_);
lean_inc(v_infoState_1009_);
lean_inc(v_messages_1008_);
lean_inc(v_recordedDeps_1007_);
lean_inc(v_cache_1006_);
lean_inc(v_traceState_1005_);
lean_inc(v_auxDeclNGen_1004_);
lean_inc(v_ngen_1003_);
lean_inc(v_nextMacroScope_1002_);
lean_inc(v_env_1001_);
lean_dec(v___x_1000_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1020_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1017_; 
v___x_1014_ = lean_box(0);
v___x_1015_ = l_Lean_MessageLog_add(v___x_999_, v_messages_1008_);
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 7, v___x_1015_);
v___x_1017_ = v___x_1012_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_env_1001_);
lean_ctor_set(v_reuseFailAlloc_1019_, 1, v_nextMacroScope_1002_);
lean_ctor_set(v_reuseFailAlloc_1019_, 2, v_ngen_1003_);
lean_ctor_set(v_reuseFailAlloc_1019_, 3, v_auxDeclNGen_1004_);
lean_ctor_set(v_reuseFailAlloc_1019_, 4, v_traceState_1005_);
lean_ctor_set(v_reuseFailAlloc_1019_, 5, v_cache_1006_);
lean_ctor_set(v_reuseFailAlloc_1019_, 6, v_recordedDeps_1007_);
lean_ctor_set(v_reuseFailAlloc_1019_, 7, v___x_1015_);
lean_ctor_set(v_reuseFailAlloc_1019_, 8, v_infoState_1009_);
lean_ctor_set(v_reuseFailAlloc_1019_, 9, v_snapshotTasks_1010_);
v___x_1017_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
lean_object* v___x_1018_; 
v___x_1018_ = lean_st_ref_put(v___y_994_, v___x_1017_);
v_a_982_ = v___x_1014_;
goto v___jp_981_;
}
}
}
v___jp_1021_:
{
lean_object* v_fileName_1030_; lean_object* v_fileMap_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1046_; 
v_fileName_1030_ = lean_ctor_get(v___y_1025_, 0);
v_fileMap_1031_ = lean_ctor_get(v___y_1025_, 1);
v___x_1032_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_973_);
v___x_1033_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44_spec__47(v___x_1032_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
v_a_1034_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1036_ = v___x_1033_;
v_isShared_1037_ = v_isSharedCheck_1046_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1033_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1046_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1041_; 
lean_inc_ref_n(v_fileMap_1031_, 2);
v___x_1038_ = l_Lean_FileMap_toPosition(v_fileMap_1031_, v___y_1027_);
lean_dec(v___y_1027_);
v___x_1039_ = l_Lean_FileMap_toPosition(v_fileMap_1031_, v___y_1029_);
lean_dec(v___y_1029_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set_tag(v___x_1036_, 1);
lean_ctor_set(v___x_1036_, 0, v___x_1039_);
v___x_1041_ = v___x_1036_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1039_);
v___x_1041_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
lean_object* v___x_1042_; 
v___x_1042_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44___closed__0));
if (v___y_1024_ == 0)
{
lean_dec_ref(v___y_1023_);
v___y_986_ = v___y_1026_;
v___y_987_ = v___x_1038_;
v___y_988_ = v___x_1041_;
v___y_989_ = v___x_1042_;
v___y_990_ = v_a_1034_;
v___y_991_ = v_fileName_1030_;
v___y_992_ = v___y_1028_;
v_toCold_993_ = v___y_1022_;
v___y_994_ = v___y_979_;
goto v___jp_985_;
}
else
{
uint8_t v___x_1043_; 
lean_inc(v_a_1034_);
v___x_1043_ = l_Lean_MessageData_hasTag(v___y_1023_, v_a_1034_);
if (v___x_1043_ == 0)
{
lean_object* v___x_1044_; 
lean_dec_ref(v___x_1041_);
lean_dec_ref(v___x_1038_);
lean_dec(v_a_1034_);
v___x_1044_ = lean_box(0);
v_a_982_ = v___x_1044_;
goto v___jp_981_;
}
else
{
v___y_986_ = v___y_1026_;
v___y_987_ = v___x_1038_;
v___y_988_ = v___x_1041_;
v___y_989_ = v___x_1042_;
v___y_990_ = v_a_1034_;
v___y_991_ = v_fileName_1030_;
v___y_992_ = v___y_1028_;
v_toCold_993_ = v___y_1022_;
v___y_994_ = v___y_979_;
goto v___jp_985_;
}
}
}
}
}
v___jp_1047_:
{
lean_object* v___x_1055_; 
v___x_1055_ = l_Lean_Syntax_getTailPos_x3f(v___y_1052_, v___y_1051_);
lean_dec(v___y_1052_);
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_inc(v___y_1054_);
v___y_1022_ = v___y_1048_;
v___y_1023_ = v___y_1050_;
v___y_1024_ = v___y_1049_;
v___y_1025_ = v___y_1048_;
v___y_1026_ = v___y_1051_;
v___y_1027_ = v___y_1054_;
v___y_1028_ = v___y_1053_;
v___y_1029_ = v___y_1054_;
goto v___jp_1021_;
}
else
{
lean_object* v_val_1056_; 
v_val_1056_ = lean_ctor_get(v___x_1055_, 0);
lean_inc(v_val_1056_);
lean_dec_ref_known(v___x_1055_, 1);
v___y_1022_ = v___y_1048_;
v___y_1023_ = v___y_1050_;
v___y_1024_ = v___y_1049_;
v___y_1025_ = v___y_1048_;
v___y_1026_ = v___y_1051_;
v___y_1027_ = v___y_1054_;
v___y_1028_ = v___y_1053_;
v___y_1029_ = v_val_1056_;
goto v___jp_1021_;
}
}
v___jp_1057_:
{
lean_object* v_toCold_1061_; lean_object* v_ref_1062_; uint8_t v_suppressElabErrors_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___f_1066_; lean_object* v_ref_1067_; lean_object* v___x_1068_; 
v_toCold_1061_ = lean_ctor_get(v___y_978_, 0);
v_ref_1062_ = lean_ctor_get(v___y_978_, 2);
v_suppressElabErrors_1063_ = lean_ctor_get_uint8(v___y_978_, sizeof(void*)*3 + 2);
v___x_1064_ = lean_box(v_suppressElabErrors_1063_);
v___x_1065_ = lean_box(v___y_1058_);
v___f_1066_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1066_, 0, v___x_1064_);
lean_closure_set(v___f_1066_, 1, v___x_1065_);
v_ref_1067_ = l_Lean_replaceRef(v_ref_972_, v_ref_1062_);
v___x_1068_ = l_Lean_Syntax_getPos_x3f(v_ref_1067_, v___y_1059_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v___x_1069_; 
v___x_1069_ = lean_unsigned_to_nat(0u);
v___y_1048_ = v_toCold_1061_;
v___y_1049_ = v_suppressElabErrors_1063_;
v___y_1050_ = v___f_1066_;
v___y_1051_ = v___y_1059_;
v___y_1052_ = v_ref_1067_;
v___y_1053_ = v___y_1060_;
v___y_1054_ = v___x_1069_;
goto v___jp_1047_;
}
else
{
lean_object* v_val_1070_; 
v_val_1070_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_val_1070_);
lean_dec_ref_known(v___x_1068_, 1);
v___y_1048_ = v_toCold_1061_;
v___y_1049_ = v_suppressElabErrors_1063_;
v___y_1050_ = v___f_1066_;
v___y_1051_ = v___y_1059_;
v___y_1052_ = v_ref_1067_;
v___y_1053_ = v___y_1060_;
v___y_1054_ = v_val_1070_;
goto v___jp_1047_;
}
}
v___jp_1072_:
{
if (v___y_1075_ == 0)
{
v___y_1058_ = v___y_1073_;
v___y_1059_ = v___y_1074_;
v___y_1060_ = v_severity_974_;
goto v___jp_1057_;
}
else
{
v___y_1058_ = v___y_1073_;
v___y_1059_ = v___y_1074_;
v___y_1060_ = v___x_1071_;
goto v___jp_1057_;
}
}
v___jp_1076_:
{
if (v___y_1077_ == 0)
{
uint8_t v___x_1078_; uint8_t v___x_1079_; 
v___x_1078_ = 1;
v___x_1079_ = l_Lean_instBEqMessageSeverity_beq(v_severity_974_, v___x_1078_);
if (v___x_1079_ == 0)
{
v___y_1073_ = v___y_1077_;
v___y_1074_ = v___y_1077_;
v___y_1075_ = v___x_1079_;
goto v___jp_1072_;
}
else
{
lean_object* v___x_1080_; lean_object* v___x_1081_; uint8_t v___x_1082_; 
v___x_1080_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_978_);
v___x_1081_ = l_Lean_warningAsError;
v___x_1082_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__4(v___x_1080_, v___x_1081_);
lean_dec_ref(v___x_1080_);
v___y_1073_ = v___y_1077_;
v___y_1074_ = v___y_1077_;
v___y_1075_ = v___x_1082_;
goto v___jp_1072_;
}
}
else
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
lean_dec_ref(v_msgData_973_);
v___x_1083_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48___closed__0));
v___x_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
return v___x_1084_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48___boxed(lean_object* v_ref_1087_, lean_object* v_msgData_1088_, lean_object* v_severity_1089_, lean_object* v_isSilent_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
uint8_t v_severity_boxed_1096_; uint8_t v_isSilent_boxed_1097_; lean_object* v_res_1098_; 
v_severity_boxed_1096_ = lean_unbox(v_severity_1089_);
v_isSilent_boxed_1097_ = lean_unbox(v_isSilent_1090_);
v_res_1098_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48(v_ref_1087_, v_msgData_1088_, v_severity_boxed_1096_, v_isSilent_boxed_1097_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec(v_ref_1087_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46(lean_object* v_msgData_1099_, uint8_t v_severity_1100_, uint8_t v_isSilent_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v_ref_1107_; lean_object* v___x_1108_; 
v_ref_1107_ = lean_ctor_get(v___y_1104_, 2);
v___x_1108_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48(v_ref_1107_, v_msgData_1099_, v_severity_1100_, v_isSilent_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46___boxed(lean_object* v_msgData_1109_, lean_object* v_severity_1110_, lean_object* v_isSilent_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
uint8_t v_severity_boxed_1117_; uint8_t v_isSilent_boxed_1118_; lean_object* v_res_1119_; 
v_severity_boxed_1117_ = lean_unbox(v_severity_1110_);
v_isSilent_boxed_1118_ = lean_unbox(v_isSilent_1111_);
v_res_1119_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46(v_msgData_1109_, v_severity_boxed_1117_, v_isSilent_boxed_1118_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44(lean_object* v_msgData_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
uint8_t v___x_1126_; uint8_t v___x_1127_; lean_object* v___x_1128_; 
v___x_1126_ = 1;
v___x_1127_ = 0;
v___x_1128_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46(v_msgData_1120_, v___x_1126_, v___x_1127_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44___boxed(lean_object* v_msgData_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44(v_msgData_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40(lean_object* v_id_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v___x_1142_; lean_object* v_env_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1166_; 
v___x_1142_ = lean_st_ref_get(v___y_1140_);
v_env_1143_ = lean_ctor_get(v___x_1142_, 0);
lean_inc_ref(v_env_1143_);
lean_dec(v___x_1142_);
v___x_1144_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1145_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43___redArg(v___x_1144_, v___y_1139_);
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1148_ = v___x_1145_;
v_isShared_1149_ = v_isSharedCheck_1166_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1145_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1166_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
uint8_t v_isExporting_1155_; 
v_isExporting_1155_ = lean_ctor_get_uint8(v_env_1143_, sizeof(void*)*8);
lean_dec_ref(v_env_1143_);
if (v_isExporting_1155_ == 0)
{
lean_dec(v_a_1146_);
lean_dec(v_id_1136_);
goto v___jp_1150_;
}
else
{
lean_object* v_val_1156_; uint8_t v___x_1157_; 
v_val_1156_ = lean_ctor_get(v_a_1146_, 0);
lean_inc(v_val_1156_);
lean_dec(v_a_1146_);
v___x_1157_ = l_Lean_isPrivateName(v_id_1136_);
if (v___x_1157_ == 0)
{
lean_dec(v_val_1156_);
lean_dec(v_id_1136_);
goto v___jp_1150_;
}
else
{
uint8_t v___x_1158_; 
v___x_1158_ = lean_unbox(v_val_1156_);
lean_dec(v_val_1156_);
if (v___x_1158_ == 0)
{
lean_dec(v_id_1136_);
goto v___jp_1150_;
}
else
{
lean_object* v___x_1159_; uint8_t v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
lean_del_object(v___x_1148_);
v___x_1159_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__1);
v___x_1160_ = 0;
v___x_1161_ = l_Lean_MessageData_ofConstName(v_id_1136_, v___x_1160_);
v___x_1162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1159_);
lean_ctor_set(v___x_1162_, 1, v___x_1161_);
v___x_1163_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__3);
v___x_1164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1162_);
lean_ctor_set(v___x_1164_, 1, v___x_1163_);
v___x_1165_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44(v___x_1164_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
return v___x_1165_;
}
}
}
v___jp_1150_:
{
lean_object* v___x_1151_; lean_object* v___x_1153_; 
v___x_1151_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48___closed__0));
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v___x_1151_);
v___x_1153_ = v___x_1148_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1151_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___boxed(lean_object* v_id_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40(v_id_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34(lean_object* v_id_1174_, uint8_t v_enableLog_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v___x_1181_; lean_object* v_toCold_1182_; lean_object* v_env_1183_; lean_object* v_currNamespace_1184_; lean_object* v_openDecls_1185_; lean_object* v___x_1186_; lean_object* v_res_1187_; lean_object* v___x_1191_; 
v___x_1181_ = lean_st_ref_get(v___y_1179_);
v_toCold_1182_ = lean_ctor_get(v___y_1178_, 0);
v_env_1183_ = lean_ctor_get(v___x_1181_, 0);
lean_inc_ref(v_env_1183_);
lean_dec(v___x_1181_);
v_currNamespace_1184_ = lean_ctor_get(v_toCold_1182_, 4);
v_openDecls_1185_ = lean_ctor_get(v_toCold_1182_, 5);
v___x_1186_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1178_);
lean_inc(v_openDecls_1185_);
lean_inc(v_currNamespace_1184_);
v_res_1187_ = l_Lean_ResolveName_resolveGlobalName(v_env_1183_, v___x_1186_, v_currNamespace_1184_, v_openDecls_1185_, v_id_1174_);
lean_dec_ref(v___x_1186_);
v___x_1191_ = lean_st_ref_get(v___y_1179_);
if (v_enableLog_1175_ == 0)
{
lean_dec(v___x_1191_);
goto v___jp_1188_;
}
else
{
lean_object* v_env_1192_; uint8_t v_isExporting_1193_; 
v_env_1192_ = lean_ctor_get(v___x_1191_, 0);
lean_inc_ref(v_env_1192_);
lean_dec(v___x_1191_);
v_isExporting_1193_ = lean_ctor_get_uint8(v_env_1192_, sizeof(void*)*8);
lean_dec_ref(v_env_1192_);
if (v_isExporting_1193_ == 0)
{
goto v___jp_1188_;
}
else
{
lean_object* v___x_1194_; 
v___x_1194_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__31(v_res_1187_);
if (lean_obj_tag(v___x_1194_) == 1)
{
lean_object* v_val_1195_; lean_object* v_fst_1196_; lean_object* v___x_1197_; 
v_val_1195_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_val_1195_);
lean_dec_ref_known(v___x_1194_, 1);
v_fst_1196_ = lean_ctor_get(v_val_1195_, 0);
lean_inc(v_fst_1196_);
lean_dec(v_val_1195_);
v___x_1197_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40(v_fst_1196_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
if (lean_obj_tag(v___x_1197_) == 0)
{
lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1206_; 
v_a_1198_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1200_ = v___x_1197_;
v_isShared_1201_ = v_isSharedCheck_1206_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_a_1198_);
lean_dec(v___x_1197_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1206_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
if (lean_obj_tag(v_a_1198_) == 0)
{
lean_object* v___x_1202_; lean_object* v___x_1204_; 
lean_dec(v_res_1187_);
v___x_1202_ = lean_box(0);
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 0, v___x_1202_);
v___x_1204_ = v___x_1200_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1202_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
else
{
lean_dec_ref_known(v_a_1198_, 1);
lean_del_object(v___x_1200_);
goto v___jp_1188_;
}
}
}
else
{
lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1214_; 
lean_dec(v_res_1187_);
v_a_1207_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1209_ = v___x_1197_;
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_dec(v___x_1197_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1212_; 
if (v_isShared_1210_ == 0)
{
v___x_1212_ = v___x_1209_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_a_1207_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
}
else
{
lean_dec(v___x_1194_);
goto v___jp_1188_;
}
}
}
v___jp_1188_:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1189_, 0, v_res_1187_);
v___x_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
return v___x_1190_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34___boxed(lean_object* v_id_1215_, lean_object* v_enableLog_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
uint8_t v_enableLog_boxed_1222_; lean_object* v_res_1223_; 
v_enableLog_boxed_1222_ = lean_unbox(v_enableLog_1216_);
v_res_1223_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34(v_id_1215_, v_enableLog_boxed_1222_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25(lean_object* v_n_u2080_1228_, lean_object* v_filter_1229_, lean_object* v_view_x3f_1230_, lean_object* v_n_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1273_; lean_object* v___y_1274_; lean_object* v___y_1307_; 
if (lean_obj_tag(v_view_x3f_1230_) == 1)
{
lean_object* v_val_1334_; lean_object* v_imported_1335_; lean_object* v_ctx_1336_; lean_object* v_scopes_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1345_; 
v_val_1334_ = lean_ctor_get(v_view_x3f_1230_, 0);
lean_inc(v_val_1334_);
lean_dec_ref_known(v_view_x3f_1230_, 1);
v_imported_1335_ = lean_ctor_get(v_val_1334_, 1);
v_ctx_1336_ = lean_ctor_get(v_val_1334_, 2);
v_scopes_1337_ = lean_ctor_get(v_val_1334_, 3);
v_isSharedCheck_1345_ = !lean_is_exclusive(v_val_1334_);
if (v_isSharedCheck_1345_ == 0)
{
lean_object* v_unused_1346_; 
v_unused_1346_ = lean_ctor_get(v_val_1334_, 0);
lean_dec(v_unused_1346_);
v___x_1339_ = v_val_1334_;
v_isShared_1340_ = v_isSharedCheck_1345_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_scopes_1337_);
lean_inc(v_ctx_1336_);
lean_inc(v_imported_1335_);
lean_dec(v_val_1334_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1345_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1342_; 
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 0, v_n_1231_);
v___x_1342_ = v___x_1339_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_n_1231_);
lean_ctor_set(v_reuseFailAlloc_1344_, 1, v_imported_1335_);
lean_ctor_set(v_reuseFailAlloc_1344_, 2, v_ctx_1336_);
lean_ctor_set(v_reuseFailAlloc_1344_, 3, v_scopes_1337_);
v___x_1342_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
lean_object* v___x_1343_; 
v___x_1343_ = l_Lean_MacroScopesView_review(v___x_1342_);
v___y_1307_ = v___x_1343_;
goto v___jp_1306_;
}
}
}
else
{
lean_dec(v_view_x3f_1230_);
v___y_1307_ = v_n_1231_;
goto v___jp_1306_;
}
v___jp_1237_:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1238_ = lean_box(0);
v___x_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1238_);
return v___x_1239_;
}
v___jp_1240_:
{
lean_object* v___x_1243_; 
lean_inc_ref(v___y_1242_);
lean_inc(v___y_1235_);
lean_inc_ref(v___y_1234_);
lean_inc(v___y_1233_);
lean_inc_ref(v___y_1232_);
v___x_1243_ = lean_apply_5(v___y_1242_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, lean_box(0));
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1263_; 
v_a_1244_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1246_ = v___x_1243_;
v_isShared_1247_ = v_isSharedCheck_1263_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_dec(v___x_1243_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1263_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
if (lean_obj_tag(v_a_1244_) == 0)
{
lean_object* v___x_1248_; lean_object* v___x_1250_; 
lean_dec(v___y_1241_);
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
else
{
lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1261_; 
v_isSharedCheck_1261_ = !lean_is_exclusive(v_a_1244_);
if (v_isSharedCheck_1261_ == 0)
{
lean_object* v_unused_1262_; 
v_unused_1262_ = lean_ctor_get(v_a_1244_, 0);
lean_dec(v_unused_1262_);
v___x_1253_ = v_a_1244_;
v_isShared_1254_ = v_isSharedCheck_1261_;
goto v_resetjp_1252_;
}
else
{
lean_dec(v_a_1244_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1261_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1256_; 
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 0, v___y_1241_);
v___x_1256_ = v___x_1253_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___y_1241_);
v___x_1256_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
lean_object* v___x_1258_; 
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 0, v___x_1256_);
v___x_1258_ = v___x_1246_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v___x_1256_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
}
}
else
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
lean_dec(v___y_1241_);
v_a_1264_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1266_ = v___x_1243_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1243_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1264_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
v___jp_1272_:
{
lean_object* v___x_1275_; 
lean_inc_ref(v___y_1274_);
lean_inc(v___y_1235_);
lean_inc_ref(v___y_1234_);
lean_inc(v___y_1233_);
lean_inc_ref(v___y_1232_);
v___x_1275_ = lean_apply_5(v___y_1274_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, lean_box(0));
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1297_; 
v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1278_ = v___x_1275_;
v_isShared_1279_ = v_isSharedCheck_1297_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1275_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1297_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
if (lean_obj_tag(v_a_1276_) == 0)
{
lean_object* v___x_1280_; lean_object* v___x_1282_; 
lean_dec(v___y_1273_);
lean_dec_ref(v_filter_1229_);
v___x_1280_ = lean_box(0);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 0, v___x_1280_);
v___x_1282_ = v___x_1278_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1280_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
else
{
lean_object* v___x_1284_; 
lean_dec_ref_known(v_a_1276_, 1);
lean_del_object(v___x_1278_);
lean_inc(v___y_1235_);
lean_inc_ref(v___y_1234_);
lean_inc(v___y_1233_);
lean_inc_ref(v___y_1232_);
lean_inc(v___y_1273_);
v___x_1284_ = lean_apply_6(v_filter_1229_, v___y_1273_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, lean_box(0));
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v_a_1285_; uint8_t v___x_1286_; 
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_a_1285_);
lean_dec_ref_known(v___x_1284_, 1);
v___x_1286_ = lean_unbox(v_a_1285_);
lean_dec(v_a_1285_);
if (v___x_1286_ == 0)
{
lean_object* v___f_1287_; 
v___f_1287_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__0));
v___y_1241_ = v___y_1273_;
v___y_1242_ = v___f_1287_;
goto v___jp_1240_;
}
else
{
lean_object* v___f_1288_; 
v___f_1288_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__1));
v___y_1241_ = v___y_1273_;
v___y_1242_ = v___f_1288_;
goto v___jp_1240_;
}
}
else
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
lean_dec(v___y_1273_);
v_a_1289_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___x_1284_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1284_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1292_ == 0)
{
v___x_1294_ = v___x_1291_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1289_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
}
}
}
else
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1305_; 
lean_dec(v___y_1273_);
lean_dec_ref(v_filter_1229_);
v_a_1298_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1300_ = v___x_1275_;
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1275_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1303_; 
if (v_isShared_1301_ == 0)
{
v___x_1303_ = v___x_1300_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_a_1298_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
}
v___jp_1306_:
{
uint8_t v___x_1308_; lean_object* v___x_1309_; 
v___x_1308_ = 0;
lean_inc(v___y_1307_);
v___x_1309_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34(v___y_1307_, v___x_1308_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1325_; 
v_a_1310_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1312_ = v___x_1309_;
v_isShared_1313_ = v_isSharedCheck_1325_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_dec(v___x_1309_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1325_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
if (lean_obj_tag(v_a_1310_) == 0)
{
lean_object* v___x_1314_; lean_object* v___x_1316_; 
lean_dec(v___y_1307_);
lean_dec_ref(v_filter_1229_);
v___x_1314_ = lean_box(0);
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 0, v___x_1314_);
v___x_1316_ = v___x_1312_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v___x_1314_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
else
{
lean_object* v_val_1318_; 
lean_del_object(v___x_1312_);
v_val_1318_ = lean_ctor_get(v_a_1310_, 0);
lean_inc(v_val_1318_);
lean_dec_ref_known(v_a_1310_, 1);
if (lean_obj_tag(v_val_1318_) == 1)
{
lean_object* v_head_1319_; lean_object* v_tail_1320_; 
v_head_1319_ = lean_ctor_get(v_val_1318_, 0);
lean_inc(v_head_1319_);
v_tail_1320_ = lean_ctor_get(v_val_1318_, 1);
lean_inc(v_tail_1320_);
lean_dec_ref_known(v_val_1318_, 2);
if (lean_obj_tag(v_tail_1320_) == 0)
{
lean_object* v_fst_1321_; uint8_t v___x_1322_; 
v_fst_1321_ = lean_ctor_get(v_head_1319_, 0);
lean_inc(v_fst_1321_);
lean_dec(v_head_1319_);
v___x_1322_ = lean_name_eq(v_fst_1321_, v_n_u2080_1228_);
lean_dec(v_fst_1321_);
if (v___x_1322_ == 0)
{
lean_object* v___f_1323_; 
v___f_1323_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__0));
v___y_1273_ = v___y_1307_;
v___y_1274_ = v___f_1323_;
goto v___jp_1272_;
}
else
{
lean_object* v___f_1324_; 
v___f_1324_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__1));
v___y_1273_ = v___y_1307_;
v___y_1274_ = v___f_1324_;
goto v___jp_1272_;
}
}
else
{
lean_dec(v_tail_1320_);
lean_dec(v_head_1319_);
lean_dec(v___y_1307_);
lean_dec_ref(v_filter_1229_);
goto v___jp_1237_;
}
}
else
{
lean_dec(v_val_1318_);
lean_dec(v___y_1307_);
lean_dec_ref(v_filter_1229_);
goto v___jp_1237_;
}
}
}
}
else
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
lean_dec(v___y_1307_);
lean_dec_ref(v_filter_1229_);
v_a_1326_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1328_ = v___x_1309_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1309_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1326_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25___boxed(lean_object* v_n_u2080_1347_, lean_object* v_filter_1348_, lean_object* v_view_x3f_1349_, lean_object* v_n_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25(v_n_u2080_1347_, v_filter_1348_, v_view_x3f_1349_, v_n_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
lean_dec(v_n_u2080_1347_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30___redArg(lean_object* v_n_u2080_1357_, lean_object* v_filter_1358_, lean_object* v_view_x3f_1359_, lean_object* v_as_x27_1360_, lean_object* v_b_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
if (lean_obj_tag(v_as_x27_1360_) == 0)
{
lean_object* v___x_1367_; lean_object* v___x_1368_; 
lean_dec(v_view_x3f_1359_);
lean_dec_ref(v_filter_1358_);
v___x_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1367_, 0, v_b_1361_);
v___x_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1367_);
return v___x_1368_;
}
else
{
lean_object* v_head_1369_; lean_object* v_tail_1370_; lean_object* v_snd_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1409_; 
v_head_1369_ = lean_ctor_get(v_as_x27_1360_, 0);
v_tail_1370_ = lean_ctor_get(v_as_x27_1360_, 1);
v_snd_1371_ = lean_ctor_get(v_b_1361_, 1);
v_isSharedCheck_1409_ = !lean_is_exclusive(v_b_1361_);
if (v_isSharedCheck_1409_ == 0)
{
lean_object* v_unused_1410_; 
v_unused_1410_ = lean_ctor_get(v_b_1361_, 0);
lean_dec(v_unused_1410_);
v___x_1373_ = v_b_1361_;
v_isShared_1374_ = v_isSharedCheck_1409_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_snd_1371_);
lean_dec(v_b_1361_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1409_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1375_ = lean_box(0);
v___x_1376_ = l_Lean_Name_appendCore(v_head_1369_, v_snd_1371_);
lean_inc(v___x_1376_);
lean_inc(v_view_x3f_1359_);
lean_inc_ref(v_filter_1358_);
v___x_1377_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25(v_n_u2080_1357_, v_filter_1358_, v_view_x3f_1359_, v___x_1376_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1400_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1380_ = v___x_1377_;
v_isShared_1381_ = v_isSharedCheck_1400_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1377_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1400_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
if (lean_obj_tag(v_a_1378_) == 0)
{
lean_object* v___x_1383_; 
lean_del_object(v___x_1380_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 1, v___x_1376_);
lean_ctor_set(v___x_1373_, 0, v___x_1375_);
v___x_1383_ = v___x_1373_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1375_);
lean_ctor_set(v_reuseFailAlloc_1385_, 1, v___x_1376_);
v___x_1383_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
v_as_x27_1360_ = v_tail_1370_;
v_b_1361_ = v___x_1383_;
goto _start;
}
}
else
{
lean_object* v___x_1387_; 
lean_dec(v_view_x3f_1359_);
lean_dec_ref(v_filter_1358_);
lean_inc_ref(v_a_1378_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 1, v___x_1376_);
lean_ctor_set(v___x_1373_, 0, v_a_1378_);
v___x_1387_ = v___x_1373_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_a_1378_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v___x_1376_);
v___x_1387_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1397_; 
v_isSharedCheck_1397_ = !lean_is_exclusive(v_a_1378_);
if (v_isSharedCheck_1397_ == 0)
{
lean_object* v_unused_1398_; 
v_unused_1398_ = lean_ctor_get(v_a_1378_, 0);
lean_dec(v_unused_1398_);
v___x_1389_ = v_a_1378_;
v_isShared_1390_ = v_isSharedCheck_1397_;
goto v_resetjp_1388_;
}
else
{
lean_dec(v_a_1378_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1397_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v___x_1387_);
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1387_);
v___x_1392_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
lean_object* v___x_1394_; 
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 0, v___x_1392_);
v___x_1394_ = v___x_1380_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1392_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1408_; 
lean_dec(v___x_1376_);
lean_del_object(v___x_1373_);
lean_dec(v_view_x3f_1359_);
lean_dec_ref(v_filter_1358_);
v_a_1401_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1403_ = v___x_1377_;
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_dec(v___x_1377_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1406_; 
if (v_isShared_1404_ == 0)
{
v___x_1406_ = v___x_1403_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_a_1401_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30___redArg___boxed(lean_object* v_n_u2080_1411_, lean_object* v_filter_1412_, lean_object* v_view_x3f_1413_, lean_object* v_as_x27_1414_, lean_object* v_b_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30___redArg(v_n_u2080_1411_, v_filter_1412_, v_view_x3f_1413_, v_as_x27_1414_, v_b_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec(v_as_x27_1414_);
lean_dec(v_n_u2080_1411_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22(lean_object* v_n_u2080_1425_, lean_object* v_filter_1426_, lean_object* v_view_x3f_1427_, lean_object* v_n_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
lean_object* v___y_1435_; uint8_t v___x_1476_; 
v___x_1476_ = l_Lean_Name_hasMacroScopes(v_n_1428_);
if (v___x_1476_ == 0)
{
lean_object* v___f_1477_; 
v___f_1477_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__1));
v___y_1435_ = v___f_1477_;
goto v___jp_1434_;
}
else
{
lean_object* v___f_1478_; 
v___f_1478_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__0));
v___y_1435_ = v___f_1478_;
goto v___jp_1434_;
}
v___jp_1434_:
{
lean_object* v___x_1436_; 
lean_inc_ref(v___y_1435_);
lean_inc(v___y_1432_);
lean_inc_ref(v___y_1431_);
lean_inc(v___y_1430_);
lean_inc_ref(v___y_1429_);
v___x_1436_ = lean_apply_5(v___y_1435_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, lean_box(0));
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1467_; 
v_a_1437_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1439_ = v___x_1436_;
v_isShared_1440_ = v_isSharedCheck_1467_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1436_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1467_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
if (lean_obj_tag(v_a_1437_) == 0)
{
lean_object* v___x_1441_; lean_object* v___x_1443_; 
lean_dec(v_n_1428_);
lean_dec(v_view_x3f_1427_);
lean_dec_ref(v_filter_1426_);
v___x_1441_ = lean_box(0);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 0, v___x_1441_);
v___x_1443_ = v___x_1439_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1441_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
else
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
lean_dec_ref_known(v_a_1437_, 1);
lean_del_object(v___x_1439_);
v___x_1445_ = l_Lean_privateToUserName(v_n_1428_);
v___x_1446_ = l_Lean_Name_componentsRev(v___x_1445_);
v___x_1447_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22___closed__0));
v___x_1448_ = l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30___redArg(v_n_u2080_1425_, v_filter_1426_, v_view_x3f_1427_, v___x_1446_, v___x_1447_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
lean_dec(v___x_1446_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1458_; 
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1451_ = v___x_1448_;
v_isShared_1452_ = v_isSharedCheck_1458_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1448_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1458_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v_val_1453_; lean_object* v_fst_1454_; lean_object* v___x_1456_; 
v_val_1453_ = lean_ctor_get(v_a_1449_, 0);
lean_inc(v_val_1453_);
lean_dec(v_a_1449_);
v_fst_1454_ = lean_ctor_get(v_val_1453_, 0);
lean_inc(v_fst_1454_);
lean_dec(v_val_1453_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 0, v_fst_1454_);
v___x_1456_ = v___x_1451_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_fst_1454_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
else
{
lean_object* v_a_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1466_; 
v_a_1459_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1461_ = v___x_1448_;
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_dec(v___x_1448_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1464_; 
if (v_isShared_1462_ == 0)
{
v___x_1464_ = v___x_1461_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_a_1459_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
}
}
}
else
{
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1475_; 
lean_dec(v_n_1428_);
lean_dec(v_view_x3f_1427_);
lean_dec_ref(v_filter_1426_);
v_a_1468_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1470_ = v___x_1436_;
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1436_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1473_; 
if (v_isShared_1471_ == 0)
{
v___x_1473_ = v___x_1470_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_a_1468_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22___boxed(lean_object* v_n_u2080_1479_, lean_object* v_filter_1480_, lean_object* v_view_x3f_1481_, lean_object* v_n_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_){
_start:
{
lean_object* v_res_1488_; 
v_res_1488_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22(v_n_u2080_1479_, v_filter_1480_, v_view_x3f_1481_, v_n_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
lean_dec(v_n_u2080_1479_);
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__23(lean_object* v_n_u2080_1489_, lean_object* v_filter_1490_, lean_object* v_as_1491_, lean_object* v_i_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_){
_start:
{
lean_object* v___x_1498_; uint8_t v___x_1499_; 
v___x_1498_ = lean_array_get_size(v_as_1491_);
v___x_1499_ = lean_nat_dec_lt(v_i_1492_, v___x_1498_);
if (v___x_1499_ == 0)
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
lean_dec(v_i_1492_);
lean_dec_ref(v_filter_1490_);
v___x_1500_ = lean_box(0);
v___x_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1500_);
return v___x_1501_;
}
else
{
lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1502_ = lean_box(0);
v___x_1503_ = lean_array_fget_borrowed(v_as_1491_, v_i_1492_);
lean_inc(v___x_1503_);
lean_inc_ref(v_filter_1490_);
v___x_1504_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22(v_n_u2080_1489_, v_filter_1490_, v___x_1502_, v___x_1503_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v_a_1505_; 
v_a_1505_ = lean_ctor_get(v___x_1504_, 0);
lean_inc(v_a_1505_);
if (lean_obj_tag(v_a_1505_) == 0)
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
lean_dec_ref_known(v___x_1504_, 1);
v___x_1506_ = lean_unsigned_to_nat(1u);
v___x_1507_ = lean_nat_add(v_i_1492_, v___x_1506_);
lean_dec(v_i_1492_);
v_i_1492_ = v___x_1507_;
goto _start;
}
else
{
lean_dec_ref_known(v_a_1505_, 1);
lean_dec(v_i_1492_);
lean_dec_ref(v_filter_1490_);
return v___x_1504_;
}
}
else
{
lean_dec(v_i_1492_);
lean_dec_ref(v_filter_1490_);
return v___x_1504_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__23___boxed(lean_object* v_n_u2080_1509_, lean_object* v_filter_1510_, lean_object* v_as_1511_, lean_object* v_i_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__23(v_n_u2080_1509_, v_filter_1510_, v_as_1511_, v_i_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
lean_dec_ref(v_as_1511_);
lean_dec(v_n_u2080_1509_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__24(lean_object* v_n_u2081_1519_, lean_object* v_as_1520_, size_t v_i_1521_, size_t v_stop_1522_, lean_object* v_b_1523_){
_start:
{
lean_object* v___y_1525_; uint8_t v___x_1529_; 
v___x_1529_ = lean_usize_dec_eq(v_i_1521_, v_stop_1522_);
if (v___x_1529_ == 0)
{
lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; uint8_t v___x_1533_; 
v___x_1530_ = lean_array_uget_borrowed(v_as_1520_, v_i_1521_);
v___x_1531_ = l_Lean_Name_getPrefix(v___x_1530_);
v___x_1532_ = l_Lean_Name_getPrefix(v_n_u2081_1519_);
v___x_1533_ = l_Lean_Name_isPrefixOf(v___x_1531_, v___x_1532_);
lean_dec(v___x_1532_);
lean_dec(v___x_1531_);
if (v___x_1533_ == 0)
{
v___y_1525_ = v_b_1523_;
goto v___jp_1524_;
}
else
{
lean_object* v___x_1534_; 
lean_inc(v___x_1530_);
v___x_1534_ = lean_array_push(v_b_1523_, v___x_1530_);
v___y_1525_ = v___x_1534_;
goto v___jp_1524_;
}
}
else
{
return v_b_1523_;
}
v___jp_1524_:
{
size_t v___x_1526_; size_t v___x_1527_; 
v___x_1526_ = ((size_t)1ULL);
v___x_1527_ = lean_usize_add(v_i_1521_, v___x_1526_);
v_i_1521_ = v___x_1527_;
v_b_1523_ = v___y_1525_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__24___boxed(lean_object* v_n_u2081_1535_, lean_object* v_as_1536_, lean_object* v_i_1537_, lean_object* v_stop_1538_, lean_object* v_b_1539_){
_start:
{
size_t v_i_boxed_1540_; size_t v_stop_boxed_1541_; lean_object* v_res_1542_; 
v_i_boxed_1540_ = lean_unbox_usize(v_i_1537_);
lean_dec(v_i_1537_);
v_stop_boxed_1541_ = lean_unbox_usize(v_stop_1538_);
lean_dec(v_stop_1538_);
v_res_1542_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__24(v_n_u2081_1535_, v_as_1536_, v_i_boxed_1540_, v_stop_boxed_1541_, v_b_1539_);
lean_dec_ref(v_as_1536_);
lean_dec(v_n_u2081_1535_);
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12(lean_object* v_n_u2080_1545_, uint8_t v_fullNames_1546_, uint8_t v_allowHorizAliases_1547_, lean_object* v_filter_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_){
_start:
{
lean_object* v_view_1554_; lean_object* v_name_1555_; lean_object* v_n_u2081_1556_; 
lean_inc(v_n_u2080_1545_);
v_view_1554_ = l_Lean_extractMacroScopes(v_n_u2080_1545_);
v_name_1555_ = lean_ctor_get(v_view_1554_, 0);
lean_inc(v_name_1555_);
v_n_u2081_1556_ = l_Lean_privateToUserName(v_name_1555_);
if (v_fullNames_1546_ == 0)
{
lean_object* v___x_1557_; lean_object* v_aliases_1559_; lean_object* v_env_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1557_ = lean_st_ref_get(v___y_1552_);
v_env_1574_ = lean_ctor_get(v___x_1557_, 0);
lean_inc_ref(v_env_1574_);
lean_dec(v___x_1557_);
lean_inc(v_n_u2080_1545_);
v___x_1575_ = l_Lean_getRevAliases(v_env_1574_, v_n_u2080_1545_);
v___x_1576_ = lean_array_mk(v___x_1575_);
if (v_allowHorizAliases_1547_ == 0)
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; uint8_t v___x_1580_; 
v___x_1577_ = lean_unsigned_to_nat(0u);
v___x_1578_ = lean_array_get_size(v___x_1576_);
v___x_1579_ = ((lean_object*)(l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12___closed__0));
v___x_1580_ = lean_nat_dec_lt(v___x_1577_, v___x_1578_);
if (v___x_1580_ == 0)
{
lean_dec_ref(v___x_1576_);
v_aliases_1559_ = v___x_1579_;
goto v___jp_1558_;
}
else
{
size_t v___x_1581_; size_t v___x_1582_; lean_object* v___x_1583_; 
v___x_1581_ = ((size_t)0ULL);
v___x_1582_ = lean_usize_of_nat(v___x_1578_);
v___x_1583_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__24(v_n_u2081_1556_, v___x_1576_, v___x_1581_, v___x_1582_, v___x_1579_);
lean_dec_ref(v___x_1576_);
v_aliases_1559_ = v___x_1583_;
goto v___jp_1558_;
}
}
else
{
v_aliases_1559_ = v___x_1576_;
goto v___jp_1558_;
}
v___jp_1558_:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1560_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_filter_1548_);
v___x_1561_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__23(v_n_u2080_1545_, v_filter_1548_, v_aliases_1559_, v___x_1560_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
lean_dec_ref(v_aliases_1559_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v_a_1562_; 
v_a_1562_ = lean_ctor_get(v___x_1561_, 0);
lean_inc(v_a_1562_);
if (lean_obj_tag(v_a_1562_) == 0)
{
lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1572_; 
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1572_ == 0)
{
lean_object* v_unused_1573_; 
v_unused_1573_ = lean_ctor_get(v___x_1561_, 0);
lean_dec(v_unused_1573_);
v___x_1564_ = v___x_1561_;
v_isShared_1565_ = v_isSharedCheck_1572_;
goto v_resetjp_1563_;
}
else
{
lean_dec(v___x_1561_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1572_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1567_; 
if (v_isShared_1565_ == 0)
{
lean_ctor_set_tag(v___x_1564_, 1);
lean_ctor_set(v___x_1564_, 0, v_view_1554_);
v___x_1567_ = v___x_1564_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_view_1554_);
v___x_1567_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1568_ = l_Lean_rootNamespace;
v___x_1569_ = l_Lean_Name_append(v___x_1568_, v_n_u2081_1556_);
v___x_1570_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22(v_n_u2080_1545_, v_filter_1548_, v___x_1567_, v___x_1569_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
lean_dec(v_n_u2080_1545_);
return v___x_1570_;
}
}
}
else
{
lean_dec_ref_known(v_a_1562_, 1);
lean_dec(v_n_u2081_1556_);
lean_dec_ref(v_view_1554_);
lean_dec_ref(v_filter_1548_);
lean_dec(v_n_u2080_1545_);
return v___x_1561_;
}
}
else
{
lean_dec(v_n_u2081_1556_);
lean_dec_ref(v_view_1554_);
lean_dec_ref(v_filter_1548_);
lean_dec(v_n_u2080_1545_);
return v___x_1561_;
}
}
}
else
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1584_, 0, v_view_1554_);
lean_inc(v_n_u2081_1556_);
lean_inc_ref(v___x_1584_);
lean_inc_ref(v_filter_1548_);
v___x_1585_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25(v_n_u2080_1545_, v_filter_1548_, v___x_1584_, v_n_u2081_1556_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v_a_1586_; 
v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_a_1586_);
if (lean_obj_tag(v_a_1586_) == 0)
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
lean_dec_ref_known(v___x_1585_, 1);
v___x_1587_ = l_Lean_rootNamespace;
v___x_1588_ = l_Lean_Name_append(v___x_1587_, v_n_u2081_1556_);
v___x_1589_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25(v_n_u2080_1545_, v_filter_1548_, v___x_1584_, v___x_1588_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
lean_dec(v_n_u2080_1545_);
return v___x_1589_;
}
else
{
lean_dec_ref_known(v_a_1586_, 1);
lean_dec_ref_known(v___x_1584_, 1);
lean_dec(v_n_u2081_1556_);
lean_dec_ref(v_filter_1548_);
lean_dec(v_n_u2080_1545_);
return v___x_1585_;
}
}
else
{
lean_dec_ref_known(v___x_1584_, 1);
lean_dec(v_n_u2081_1556_);
lean_dec_ref(v_filter_1548_);
lean_dec(v_n_u2080_1545_);
return v___x_1585_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12___boxed(lean_object* v_n_u2080_1590_, lean_object* v_fullNames_1591_, lean_object* v_allowHorizAliases_1592_, lean_object* v_filter_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
uint8_t v_fullNames_boxed_1599_; uint8_t v_allowHorizAliases_boxed_1600_; lean_object* v_res_1601_; 
v_fullNames_boxed_1599_ = lean_unbox(v_fullNames_1591_);
v_allowHorizAliases_boxed_1600_ = lean_unbox(v_allowHorizAliases_1592_);
v_res_1601_ = l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12(v_n_u2080_1590_, v_fullNames_boxed_1599_, v_allowHorizAliases_boxed_1600_, v_filter_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
lean_dec(v___y_1595_);
lean_dec_ref(v___y_1594_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5(lean_object* v_n_u2080_1605_, uint8_t v_fullNames_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
uint8_t v___x_1612_; lean_object* v___f_1613_; lean_object* v___x_1614_; 
v___x_1612_ = 0;
v___f_1613_ = ((lean_object*)(l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5___closed__0));
v___x_1614_ = l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12(v_n_u2080_1605_, v_fullNames_1606_, v___x_1612_, v___f_1613_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5___boxed(lean_object* v_n_u2080_1615_, lean_object* v_fullNames_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
uint8_t v_fullNames_boxed_1622_; lean_object* v_res_1623_; 
v_fullNames_boxed_1622_ = lean_unbox(v_fullNames_1616_);
v_res_1623_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5(v_n_u2080_1615_, v_fullNames_boxed_1622_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
return v_res_1623_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1624_; 
v___x_1624_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1624_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1625_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_1626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1625_);
return v___x_1626_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1627_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_1628_ = lean_unsigned_to_nat(0u);
v___x_1629_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1628_);
lean_ctor_set(v___x_1629_, 1, v___x_1628_);
lean_ctor_set(v___x_1629_, 2, v___x_1628_);
lean_ctor_set(v___x_1629_, 3, v___x_1628_);
lean_ctor_set(v___x_1629_, 4, v___x_1627_);
lean_ctor_set(v___x_1629_, 5, v___x_1627_);
lean_ctor_set(v___x_1629_, 6, v___x_1627_);
lean_ctor_set(v___x_1629_, 7, v___x_1627_);
lean_ctor_set(v___x_1629_, 8, v___x_1627_);
lean_ctor_set(v___x_1629_, 9, v___x_1627_);
lean_ctor_set(v___x_1629_, 10, v___x_1627_);
return v___x_1629_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1630_ = lean_unsigned_to_nat(32u);
v___x_1631_ = lean_mk_empty_array_with_capacity(v___x_1630_);
v___x_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1631_);
return v___x_1632_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1633_ = ((size_t)5ULL);
v___x_1634_ = lean_unsigned_to_nat(0u);
v___x_1635_ = lean_unsigned_to_nat(32u);
v___x_1636_ = lean_mk_empty_array_with_capacity(v___x_1635_);
v___x_1637_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_1638_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1638_, 0, v___x_1637_);
lean_ctor_set(v___x_1638_, 1, v___x_1636_);
lean_ctor_set(v___x_1638_, 2, v___x_1634_);
lean_ctor_set(v___x_1638_, 3, v___x_1634_);
lean_ctor_set_usize(v___x_1638_, 4, v___x_1633_);
return v___x_1638_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1639_ = lean_box(1);
v___x_1640_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_1641_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_1642_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1641_);
lean_ctor_set(v___x_1642_, 1, v___x_1640_);
lean_ctor_set(v___x_1642_, 2, v___x_1639_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
lean_object* v___x_1647_; lean_object* v_toCold_1648_; lean_object* v_env_1649_; lean_object* v_options_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1647_ = lean_st_ref_get(v___y_1645_);
v_toCold_1648_ = lean_ctor_get(v___y_1644_, 0);
v_env_1649_ = lean_ctor_get(v___x_1647_, 0);
lean_inc_ref(v_env_1649_);
lean_dec(v___x_1647_);
v_options_1650_ = lean_ctor_get(v_toCold_1648_, 2);
v___x_1651_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_1652_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_1650_);
v___x_1653_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1653_, 0, v_env_1649_);
lean_ctor_set(v___x_1653_, 1, v___x_1651_);
lean_ctor_set(v___x_1653_, 2, v___x_1652_);
lean_ctor_set(v___x_1653_, 3, v_options_1650_);
v___x_1654_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1653_);
lean_ctor_set(v___x_1654_, 1, v_msgData_1643_);
v___x_1655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1654_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0(v_msgData_1656_, v___y_1657_, v___y_1658_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5(lean_object* v_ref_1661_, lean_object* v_msgData_1662_, uint8_t v_severity_1663_, uint8_t v_isSilent_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_){
_start:
{
lean_object* v___y_1669_; uint8_t v___y_1670_; lean_object* v___y_1671_; uint8_t v___y_1672_; lean_object* v___y_1673_; lean_object* v___y_1674_; lean_object* v___y_1675_; lean_object* v_toCold_1676_; lean_object* v___y_1677_; lean_object* v___y_1706_; lean_object* v___y_1707_; uint8_t v___y_1708_; uint8_t v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; uint8_t v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1733_; lean_object* v___y_1734_; uint8_t v___y_1735_; uint8_t v___y_1736_; lean_object* v___y_1737_; uint8_t v___y_1738_; lean_object* v___y_1739_; uint8_t v___y_1743_; uint8_t v___y_1744_; uint8_t v___y_1745_; uint8_t v___x_1756_; uint8_t v___y_1758_; uint8_t v___y_1759_; uint8_t v___y_1760_; uint8_t v___y_1762_; uint8_t v___x_1770_; 
v___x_1756_ = 2;
v___x_1770_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1663_, v___x_1756_);
if (v___x_1770_ == 0)
{
v___y_1762_ = v___x_1770_;
goto v___jp_1761_;
}
else
{
uint8_t v___x_1771_; 
lean_inc_ref(v_msgData_1662_);
v___x_1771_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1662_);
v___y_1762_ = v___x_1771_;
goto v___jp_1761_;
}
v___jp_1668_:
{
lean_object* v_currNamespace_1678_; lean_object* v_openDecls_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v_env_1684_; lean_object* v_nextMacroScope_1685_; lean_object* v_ngen_1686_; lean_object* v_auxDeclNGen_1687_; lean_object* v_traceState_1688_; lean_object* v_cache_1689_; lean_object* v_recordedDeps_1690_; lean_object* v_messages_1691_; lean_object* v_infoState_1692_; lean_object* v_snapshotTasks_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1704_; 
v_currNamespace_1678_ = lean_ctor_get(v_toCold_1676_, 4);
v_openDecls_1679_ = lean_ctor_get(v_toCold_1676_, 5);
lean_inc(v_openDecls_1679_);
lean_inc(v_currNamespace_1678_);
v___x_1680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1680_, 0, v_currNamespace_1678_);
lean_ctor_set(v___x_1680_, 1, v_openDecls_1679_);
v___x_1681_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1680_);
lean_ctor_set(v___x_1681_, 1, v___y_1674_);
lean_inc_ref(v___y_1673_);
lean_inc_ref(v___y_1675_);
v___x_1682_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1682_, 0, v___y_1675_);
lean_ctor_set(v___x_1682_, 1, v___y_1671_);
lean_ctor_set(v___x_1682_, 2, v___y_1669_);
lean_ctor_set(v___x_1682_, 3, v___y_1673_);
lean_ctor_set(v___x_1682_, 4, v___x_1681_);
lean_ctor_set_uint8(v___x_1682_, sizeof(void*)*5, v___y_1670_);
lean_ctor_set_uint8(v___x_1682_, sizeof(void*)*5 + 1, v___y_1672_);
lean_ctor_set_uint8(v___x_1682_, sizeof(void*)*5 + 2, v_isSilent_1664_);
v___x_1683_ = lean_st_ref_take(v___y_1677_);
v_env_1684_ = lean_ctor_get(v___x_1683_, 0);
v_nextMacroScope_1685_ = lean_ctor_get(v___x_1683_, 1);
v_ngen_1686_ = lean_ctor_get(v___x_1683_, 2);
v_auxDeclNGen_1687_ = lean_ctor_get(v___x_1683_, 3);
v_traceState_1688_ = lean_ctor_get(v___x_1683_, 4);
v_cache_1689_ = lean_ctor_get(v___x_1683_, 5);
v_recordedDeps_1690_ = lean_ctor_get(v___x_1683_, 6);
v_messages_1691_ = lean_ctor_get(v___x_1683_, 7);
v_infoState_1692_ = lean_ctor_get(v___x_1683_, 8);
v_snapshotTasks_1693_ = lean_ctor_get(v___x_1683_, 9);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1695_ = v___x_1683_;
v_isShared_1696_ = v_isSharedCheck_1704_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_snapshotTasks_1693_);
lean_inc(v_infoState_1692_);
lean_inc(v_messages_1691_);
lean_inc(v_recordedDeps_1690_);
lean_inc(v_cache_1689_);
lean_inc(v_traceState_1688_);
lean_inc(v_auxDeclNGen_1687_);
lean_inc(v_ngen_1686_);
lean_inc(v_nextMacroScope_1685_);
lean_inc(v_env_1684_);
lean_dec(v___x_1683_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1704_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1700_; 
v___x_1697_ = lean_box(0);
v___x_1698_ = l_Lean_MessageLog_add(v___x_1682_, v_messages_1691_);
if (v_isShared_1696_ == 0)
{
lean_ctor_set(v___x_1695_, 7, v___x_1698_);
v___x_1700_ = v___x_1695_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_env_1684_);
lean_ctor_set(v_reuseFailAlloc_1703_, 1, v_nextMacroScope_1685_);
lean_ctor_set(v_reuseFailAlloc_1703_, 2, v_ngen_1686_);
lean_ctor_set(v_reuseFailAlloc_1703_, 3, v_auxDeclNGen_1687_);
lean_ctor_set(v_reuseFailAlloc_1703_, 4, v_traceState_1688_);
lean_ctor_set(v_reuseFailAlloc_1703_, 5, v_cache_1689_);
lean_ctor_set(v_reuseFailAlloc_1703_, 6, v_recordedDeps_1690_);
lean_ctor_set(v_reuseFailAlloc_1703_, 7, v___x_1698_);
lean_ctor_set(v_reuseFailAlloc_1703_, 8, v_infoState_1692_);
lean_ctor_set(v_reuseFailAlloc_1703_, 9, v_snapshotTasks_1693_);
v___x_1700_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1701_ = lean_st_ref_put(v___y_1677_, v___x_1700_);
v___x_1702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1702_, 0, v___x_1697_);
return v___x_1702_;
}
}
}
v___jp_1705_:
{
lean_object* v_fileName_1714_; lean_object* v_fileMap_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1731_; 
v_fileName_1714_ = lean_ctor_get(v___y_1710_, 0);
v_fileMap_1715_ = lean_ctor_get(v___y_1710_, 1);
v___x_1716_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1662_);
v___x_1717_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0(v___x_1716_, v___y_1665_, v___y_1666_);
v_a_1718_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1720_ = v___x_1717_;
v_isShared_1721_ = v_isSharedCheck_1731_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1717_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1731_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; 
lean_inc_ref_n(v_fileMap_1715_, 2);
v___x_1722_ = l_Lean_FileMap_toPosition(v_fileMap_1715_, v___y_1711_);
lean_dec(v___y_1711_);
v___x_1723_ = l_Lean_FileMap_toPosition(v_fileMap_1715_, v___y_1713_);
lean_dec(v___y_1713_);
v___x_1724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1724_, 0, v___x_1723_);
v___x_1725_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44___closed__0));
if (v___y_1709_ == 0)
{
lean_del_object(v___x_1720_);
lean_dec_ref(v___y_1706_);
v___y_1669_ = v___x_1724_;
v___y_1670_ = v___y_1708_;
v___y_1671_ = v___x_1722_;
v___y_1672_ = v___y_1712_;
v___y_1673_ = v___x_1725_;
v___y_1674_ = v_a_1718_;
v___y_1675_ = v_fileName_1714_;
v_toCold_1676_ = v___y_1707_;
v___y_1677_ = v___y_1666_;
goto v___jp_1668_;
}
else
{
uint8_t v___x_1726_; 
lean_inc(v_a_1718_);
v___x_1726_ = l_Lean_MessageData_hasTag(v___y_1706_, v_a_1718_);
if (v___x_1726_ == 0)
{
lean_object* v___x_1727_; lean_object* v___x_1729_; 
lean_dec_ref_known(v___x_1724_, 1);
lean_dec_ref(v___x_1722_);
lean_dec(v_a_1718_);
v___x_1727_ = lean_box(0);
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 0, v___x_1727_);
v___x_1729_ = v___x_1720_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v___x_1727_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
else
{
lean_del_object(v___x_1720_);
v___y_1669_ = v___x_1724_;
v___y_1670_ = v___y_1708_;
v___y_1671_ = v___x_1722_;
v___y_1672_ = v___y_1712_;
v___y_1673_ = v___x_1725_;
v___y_1674_ = v_a_1718_;
v___y_1675_ = v_fileName_1714_;
v_toCold_1676_ = v___y_1707_;
v___y_1677_ = v___y_1666_;
goto v___jp_1668_;
}
}
}
}
v___jp_1732_:
{
lean_object* v___x_1740_; 
v___x_1740_ = l_Lean_Syntax_getTailPos_x3f(v___y_1737_, v___y_1736_);
lean_dec(v___y_1737_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_inc(v___y_1739_);
v___y_1706_ = v___y_1733_;
v___y_1707_ = v___y_1734_;
v___y_1708_ = v___y_1736_;
v___y_1709_ = v___y_1735_;
v___y_1710_ = v___y_1734_;
v___y_1711_ = v___y_1739_;
v___y_1712_ = v___y_1738_;
v___y_1713_ = v___y_1739_;
goto v___jp_1705_;
}
else
{
lean_object* v_val_1741_; 
v_val_1741_ = lean_ctor_get(v___x_1740_, 0);
lean_inc(v_val_1741_);
lean_dec_ref_known(v___x_1740_, 1);
v___y_1706_ = v___y_1733_;
v___y_1707_ = v___y_1734_;
v___y_1708_ = v___y_1736_;
v___y_1709_ = v___y_1735_;
v___y_1710_ = v___y_1734_;
v___y_1711_ = v___y_1739_;
v___y_1712_ = v___y_1738_;
v___y_1713_ = v_val_1741_;
goto v___jp_1705_;
}
}
v___jp_1742_:
{
lean_object* v_toCold_1746_; lean_object* v_ref_1747_; uint8_t v_suppressElabErrors_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___f_1751_; lean_object* v_ref_1752_; lean_object* v___x_1753_; 
v_toCold_1746_ = lean_ctor_get(v___y_1665_, 0);
v_ref_1747_ = lean_ctor_get(v___y_1665_, 2);
v_suppressElabErrors_1748_ = lean_ctor_get_uint8(v___y_1665_, sizeof(void*)*3 + 2);
v___x_1749_ = lean_box(v_suppressElabErrors_1748_);
v___x_1750_ = lean_box(v___y_1743_);
v___f_1751_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1751_, 0, v___x_1749_);
lean_closure_set(v___f_1751_, 1, v___x_1750_);
v_ref_1752_ = l_Lean_replaceRef(v_ref_1661_, v_ref_1747_);
v___x_1753_ = l_Lean_Syntax_getPos_x3f(v_ref_1752_, v___y_1744_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v___x_1754_; 
v___x_1754_ = lean_unsigned_to_nat(0u);
v___y_1733_ = v___f_1751_;
v___y_1734_ = v_toCold_1746_;
v___y_1735_ = v_suppressElabErrors_1748_;
v___y_1736_ = v___y_1744_;
v___y_1737_ = v_ref_1752_;
v___y_1738_ = v___y_1745_;
v___y_1739_ = v___x_1754_;
goto v___jp_1732_;
}
else
{
lean_object* v_val_1755_; 
v_val_1755_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_val_1755_);
lean_dec_ref_known(v___x_1753_, 1);
v___y_1733_ = v___f_1751_;
v___y_1734_ = v_toCold_1746_;
v___y_1735_ = v_suppressElabErrors_1748_;
v___y_1736_ = v___y_1744_;
v___y_1737_ = v_ref_1752_;
v___y_1738_ = v___y_1745_;
v___y_1739_ = v_val_1755_;
goto v___jp_1732_;
}
}
v___jp_1757_:
{
if (v___y_1760_ == 0)
{
v___y_1743_ = v___y_1758_;
v___y_1744_ = v___y_1759_;
v___y_1745_ = v_severity_1663_;
goto v___jp_1742_;
}
else
{
v___y_1743_ = v___y_1758_;
v___y_1744_ = v___y_1759_;
v___y_1745_ = v___x_1756_;
goto v___jp_1742_;
}
}
v___jp_1761_:
{
if (v___y_1762_ == 0)
{
uint8_t v___x_1763_; uint8_t v___x_1764_; 
v___x_1763_ = 1;
v___x_1764_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1663_, v___x_1763_);
if (v___x_1764_ == 0)
{
v___y_1758_ = v___y_1762_;
v___y_1759_ = v___y_1762_;
v___y_1760_ = v___x_1764_;
goto v___jp_1757_;
}
else
{
lean_object* v___x_1765_; lean_object* v___x_1766_; uint8_t v___x_1767_; 
v___x_1765_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1665_);
v___x_1766_ = l_Lean_warningAsError;
v___x_1767_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__4(v___x_1765_, v___x_1766_);
lean_dec_ref(v___x_1765_);
v___y_1758_ = v___y_1762_;
v___y_1759_ = v___y_1762_;
v___y_1760_ = v___x_1767_;
goto v___jp_1757_;
}
}
else
{
lean_object* v___x_1768_; lean_object* v___x_1769_; 
lean_dec_ref(v_msgData_1662_);
v___x_1768_ = lean_box(0);
v___x_1769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1768_);
return v___x_1769_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___boxed(lean_object* v_ref_1772_, lean_object* v_msgData_1773_, lean_object* v_severity_1774_, lean_object* v_isSilent_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_){
_start:
{
uint8_t v_severity_boxed_1779_; uint8_t v_isSilent_boxed_1780_; lean_object* v_res_1781_; 
v_severity_boxed_1779_ = lean_unbox(v_severity_1774_);
v_isSilent_boxed_1780_ = lean_unbox(v_isSilent_1775_);
v_res_1781_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5(v_ref_1772_, v_msgData_1773_, v_severity_boxed_1779_, v_isSilent_boxed_1780_, v___y_1776_, v___y_1777_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
lean_dec(v_ref_1772_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_msgData_1782_, uint8_t v_severity_1783_, uint8_t v_isSilent_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
lean_object* v_ref_1788_; lean_object* v___x_1789_; 
v_ref_1788_ = lean_ctor_get(v___y_1785_, 2);
v___x_1789_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5(v_ref_1788_, v_msgData_1782_, v_severity_1783_, v_isSilent_1784_, v___y_1785_, v___y_1786_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_msgData_1790_, lean_object* v_severity_1791_, lean_object* v_isSilent_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_){
_start:
{
uint8_t v_severity_boxed_1796_; uint8_t v_isSilent_boxed_1797_; lean_object* v_res_1798_; 
v_severity_boxed_1796_ = lean_unbox(v_severity_1791_);
v_isSilent_boxed_1797_ = lean_unbox(v_isSilent_1792_);
v_res_1798_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2(v_msgData_1790_, v_severity_boxed_1796_, v_isSilent_boxed_1797_, v___y_1793_, v___y_1794_);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1793_);
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1(lean_object* v_msgData_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_){
_start:
{
uint8_t v___x_1803_; uint8_t v___x_1804_; lean_object* v___x_1805_; 
v___x_1803_ = 1;
v___x_1804_ = 0;
v___x_1805_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2(v_msgData_1799_, v___x_1803_, v___x_1804_, v___y_1800_, v___y_1801_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1___boxed(lean_object* v_msgData_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_){
_start:
{
lean_object* v_res_1810_; 
v_res_1810_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1(v_msgData_1806_, v___y_1807_, v___y_1808_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3_spec__8___redArg(lean_object* v_o_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v_env_1816_; lean_object* v___x_1817_; lean_object* v_toEnvExtension_1818_; lean_object* v_asyncMode_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v_merged_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1830_; 
v___x_1814_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_1815_ = lean_st_ref_get(v___y_1812_);
v_env_1816_ = lean_ctor_get(v___x_1815_, 0);
lean_inc_ref(v_env_1816_);
lean_dec(v___x_1815_);
v___x_1817_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_1818_ = lean_ctor_get(v___x_1817_, 0);
v_asyncMode_1819_ = lean_ctor_get(v_toEnvExtension_1818_, 2);
v___x_1820_ = lean_box(0);
v___x_1821_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1814_, v___x_1817_, v_env_1816_, v_asyncMode_1819_, v___x_1820_);
v_merged_1822_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1830_ == 0)
{
lean_object* v_unused_1831_; 
v_unused_1831_ = lean_ctor_get(v___x_1821_, 1);
lean_dec(v_unused_1831_);
v___x_1824_ = v___x_1821_;
v_isShared_1825_ = v_isSharedCheck_1830_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_merged_1822_);
lean_dec(v___x_1821_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1830_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1827_; 
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 1, v_merged_1822_);
lean_ctor_set(v___x_1824_, 0, v_o_1811_);
v___x_1827_ = v___x_1824_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_o_1811_);
lean_ctor_set(v_reuseFailAlloc_1829_, 1, v_merged_1822_);
v___x_1827_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
lean_object* v___x_1828_; 
v___x_1828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1827_);
return v___x_1828_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3_spec__8___redArg___boxed(lean_object* v_o_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_){
_start:
{
lean_object* v_res_1835_; 
v_res_1835_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3_spec__8___redArg(v_o_1832_, v___y_1833_);
lean_dec(v___y_1833_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3(lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1839_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1836_);
v___x_1840_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3_spec__8___redArg(v___x_1839_, v___y_1837_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3___boxed(lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3(v___y_1841_, v___y_1842_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1841_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_){
_start:
{
lean_object* v_ref_1849_; lean_object* v___x_1850_; lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1859_; 
v_ref_1849_ = lean_ctor_get(v___y_1846_, 2);
v___x_1850_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0(v_msg_1845_, v___y_1846_, v___y_1847_);
v_a_1851_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1853_ = v___x_1850_;
v_isShared_1854_ = v_isSharedCheck_1859_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1850_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1859_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1855_; lean_object* v___x_1857_; 
lean_inc(v_ref_1849_);
v___x_1855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1855_, 0, v_ref_1849_);
lean_ctor_set(v___x_1855_, 1, v_a_1851_);
if (v_isShared_1854_ == 0)
{
lean_ctor_set_tag(v___x_1853_, 1);
lean_ctor_set(v___x_1853_, 0, v___x_1855_);
v___x_1857_ = v___x_1853_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1855_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___redArg(v_msg_1860_, v___y_1861_, v___y_1862_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
return v_res_1864_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17___redArg(lean_object* v_keys_1865_, lean_object* v_i_1866_, lean_object* v_k_1867_){
_start:
{
lean_object* v___x_1868_; uint8_t v___x_1869_; 
v___x_1868_ = lean_array_get_size(v_keys_1865_);
v___x_1869_ = lean_nat_dec_lt(v_i_1866_, v___x_1868_);
if (v___x_1869_ == 0)
{
lean_dec(v_i_1866_);
return v___x_1869_;
}
else
{
lean_object* v_k_x27_1870_; uint8_t v___x_1871_; 
v_k_x27_1870_ = lean_array_fget_borrowed(v_keys_1865_, v_i_1866_);
v___x_1871_ = l_Lean_instBEqExtraModUse_beq(v_k_1867_, v_k_x27_1870_);
if (v___x_1871_ == 0)
{
lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1872_ = lean_unsigned_to_nat(1u);
v___x_1873_ = lean_nat_add(v_i_1866_, v___x_1872_);
lean_dec(v_i_1866_);
v_i_1866_ = v___x_1873_;
goto _start;
}
else
{
lean_dec(v_i_1866_);
return v___x_1869_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17___redArg___boxed(lean_object* v_keys_1875_, lean_object* v_i_1876_, lean_object* v_k_1877_){
_start:
{
uint8_t v_res_1878_; lean_object* v_r_1879_; 
v_res_1878_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17___redArg(v_keys_1875_, v_i_1876_, v_k_1877_);
lean_dec_ref(v_k_1877_);
lean_dec_ref(v_keys_1875_);
v_r_1879_ = lean_box(v_res_1878_);
return v_r_1879_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12___redArg(lean_object* v_x_1880_, size_t v_x_1881_, lean_object* v_x_1882_){
_start:
{
if (lean_obj_tag(v_x_1880_) == 0)
{
lean_object* v_es_1883_; lean_object* v___x_1884_; size_t v___x_1885_; size_t v___x_1886_; lean_object* v_j_1887_; lean_object* v___x_1888_; 
v_es_1883_ = lean_ctor_get(v_x_1880_, 0);
v___x_1884_ = lean_box(2);
v___x_1885_ = ((size_t)31ULL);
v___x_1886_ = lean_usize_land(v_x_1881_, v___x_1885_);
v_j_1887_ = lean_usize_to_nat(v___x_1886_);
v___x_1888_ = lean_array_get_borrowed(v___x_1884_, v_es_1883_, v_j_1887_);
lean_dec(v_j_1887_);
switch(lean_obj_tag(v___x_1888_))
{
case 0:
{
lean_object* v_key_1889_; uint8_t v___x_1890_; 
v_key_1889_ = lean_ctor_get(v___x_1888_, 0);
v___x_1890_ = l_Lean_instBEqExtraModUse_beq(v_x_1882_, v_key_1889_);
return v___x_1890_;
}
case 1:
{
lean_object* v_node_1891_; size_t v___x_1892_; size_t v___x_1893_; 
v_node_1891_ = lean_ctor_get(v___x_1888_, 0);
v___x_1892_ = ((size_t)5ULL);
v___x_1893_ = lean_usize_shift_right(v_x_1881_, v___x_1892_);
v_x_1880_ = v_node_1891_;
v_x_1881_ = v___x_1893_;
goto _start;
}
default: 
{
uint8_t v___x_1895_; 
v___x_1895_ = 0;
return v___x_1895_;
}
}
}
else
{
lean_object* v_ks_1896_; lean_object* v___x_1897_; uint8_t v___x_1898_; 
v_ks_1896_ = lean_ctor_get(v_x_1880_, 0);
v___x_1897_ = lean_unsigned_to_nat(0u);
v___x_1898_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17___redArg(v_ks_1896_, v___x_1897_, v_x_1882_);
return v___x_1898_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12___redArg___boxed(lean_object* v_x_1899_, lean_object* v_x_1900_, lean_object* v_x_1901_){
_start:
{
size_t v_x_45726__boxed_1902_; uint8_t v_res_1903_; lean_object* v_r_1904_; 
v_x_45726__boxed_1902_ = lean_unbox_usize(v_x_1900_);
lean_dec(v_x_1900_);
v_res_1903_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12___redArg(v_x_1899_, v_x_45726__boxed_1902_, v_x_1901_);
lean_dec_ref(v_x_1901_);
lean_dec_ref(v_x_1899_);
v_r_1904_ = lean_box(v_res_1903_);
return v_r_1904_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg(lean_object* v_x_1905_, lean_object* v_x_1906_){
_start:
{
uint64_t v___x_1907_; size_t v___x_1908_; uint8_t v___x_1909_; 
v___x_1907_ = l_Lean_instHashableExtraModUse_hash(v_x_1906_);
v___x_1908_ = lean_uint64_to_usize(v___x_1907_);
v___x_1909_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12___redArg(v_x_1905_, v___x_1908_, v_x_1906_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_x_1910_, lean_object* v_x_1911_){
_start:
{
uint8_t v_res_1912_; lean_object* v_r_1913_; 
v_res_1912_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg(v_x_1910_, v_x_1911_);
lean_dec_ref(v_x_1911_);
lean_dec_ref(v_x_1910_);
v_r_1913_ = lean_box(v_res_1912_);
return v_r_1913_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0(void){
_start:
{
lean_object* v___x_1914_; double v___x_1915_; 
v___x_1914_ = lean_unsigned_to_nat(0u);
v___x_1915_ = lean_float_of_nat(v___x_1914_);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__9(lean_object* v_cls_1918_, lean_object* v_msg_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_){
_start:
{
lean_object* v_ref_1923_; lean_object* v___x_1924_; lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1970_; 
v_ref_1923_ = lean_ctor_get(v___y_1920_, 2);
v___x_1924_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0(v_msg_1919_, v___y_1920_, v___y_1921_);
v_a_1925_ = lean_ctor_get(v___x_1924_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1927_ = v___x_1924_;
v_isShared_1928_ = v_isSharedCheck_1970_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___x_1924_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1970_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___x_1929_; lean_object* v_traceState_1930_; lean_object* v_env_1931_; lean_object* v_nextMacroScope_1932_; lean_object* v_ngen_1933_; lean_object* v_auxDeclNGen_1934_; lean_object* v_cache_1935_; lean_object* v_recordedDeps_1936_; lean_object* v_messages_1937_; lean_object* v_infoState_1938_; lean_object* v_snapshotTasks_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1969_; 
v___x_1929_ = lean_st_ref_take(v___y_1921_);
v_traceState_1930_ = lean_ctor_get(v___x_1929_, 4);
v_env_1931_ = lean_ctor_get(v___x_1929_, 0);
v_nextMacroScope_1932_ = lean_ctor_get(v___x_1929_, 1);
v_ngen_1933_ = lean_ctor_get(v___x_1929_, 2);
v_auxDeclNGen_1934_ = lean_ctor_get(v___x_1929_, 3);
v_cache_1935_ = lean_ctor_get(v___x_1929_, 5);
v_recordedDeps_1936_ = lean_ctor_get(v___x_1929_, 6);
v_messages_1937_ = lean_ctor_get(v___x_1929_, 7);
v_infoState_1938_ = lean_ctor_get(v___x_1929_, 8);
v_snapshotTasks_1939_ = lean_ctor_get(v___x_1929_, 9);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1941_ = v___x_1929_;
v_isShared_1942_ = v_isSharedCheck_1969_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_snapshotTasks_1939_);
lean_inc(v_infoState_1938_);
lean_inc(v_messages_1937_);
lean_inc(v_recordedDeps_1936_);
lean_inc(v_cache_1935_);
lean_inc(v_traceState_1930_);
lean_inc(v_auxDeclNGen_1934_);
lean_inc(v_ngen_1933_);
lean_inc(v_nextMacroScope_1932_);
lean_inc(v_env_1931_);
lean_dec(v___x_1929_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1969_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
uint64_t v_tid_1943_; lean_object* v_traces_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1968_; 
v_tid_1943_ = lean_ctor_get_uint64(v_traceState_1930_, sizeof(void*)*1);
v_traces_1944_ = lean_ctor_get(v_traceState_1930_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v_traceState_1930_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1946_ = v_traceState_1930_;
v_isShared_1947_ = v_isSharedCheck_1968_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_traces_1944_);
lean_dec(v_traceState_1930_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1968_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1948_; lean_object* v___x_1949_; double v___x_1950_; uint8_t v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1959_; 
v___x_1948_ = lean_box(0);
v___x_1949_ = lean_box(0);
v___x_1950_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0);
v___x_1951_ = 0;
v___x_1952_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44___closed__0));
v___x_1953_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1953_, 0, v_cls_1918_);
lean_ctor_set(v___x_1953_, 1, v___x_1949_);
lean_ctor_set(v___x_1953_, 2, v___x_1952_);
lean_ctor_set_float(v___x_1953_, sizeof(void*)*3, v___x_1950_);
lean_ctor_set_float(v___x_1953_, sizeof(void*)*3 + 8, v___x_1950_);
lean_ctor_set_uint8(v___x_1953_, sizeof(void*)*3 + 16, v___x_1951_);
v___x_1954_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__1));
v___x_1955_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1953_);
lean_ctor_set(v___x_1955_, 1, v_a_1925_);
lean_ctor_set(v___x_1955_, 2, v___x_1954_);
lean_inc(v_ref_1923_);
v___x_1956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1956_, 0, v_ref_1923_);
lean_ctor_set(v___x_1956_, 1, v___x_1955_);
v___x_1957_ = l_Lean_PersistentArray_push___redArg(v_traces_1944_, v___x_1956_);
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 0, v___x_1957_);
v___x_1959_ = v___x_1946_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v___x_1957_);
lean_ctor_set_uint64(v_reuseFailAlloc_1967_, sizeof(void*)*1, v_tid_1943_);
v___x_1959_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
lean_object* v___x_1961_; 
if (v_isShared_1942_ == 0)
{
lean_ctor_set(v___x_1941_, 4, v___x_1959_);
v___x_1961_ = v___x_1941_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_env_1931_);
lean_ctor_set(v_reuseFailAlloc_1966_, 1, v_nextMacroScope_1932_);
lean_ctor_set(v_reuseFailAlloc_1966_, 2, v_ngen_1933_);
lean_ctor_set(v_reuseFailAlloc_1966_, 3, v_auxDeclNGen_1934_);
lean_ctor_set(v_reuseFailAlloc_1966_, 4, v___x_1959_);
lean_ctor_set(v_reuseFailAlloc_1966_, 5, v_cache_1935_);
lean_ctor_set(v_reuseFailAlloc_1966_, 6, v_recordedDeps_1936_);
lean_ctor_set(v_reuseFailAlloc_1966_, 7, v_messages_1937_);
lean_ctor_set(v_reuseFailAlloc_1966_, 8, v_infoState_1938_);
lean_ctor_set(v_reuseFailAlloc_1966_, 9, v_snapshotTasks_1939_);
v___x_1961_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
lean_object* v___x_1962_; lean_object* v___x_1964_; 
v___x_1962_ = lean_st_ref_put(v___y_1921_, v___x_1961_);
if (v_isShared_1928_ == 0)
{
lean_ctor_set(v___x_1927_, 0, v___x_1948_);
v___x_1964_ = v___x_1927_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v___x_1948_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__9___boxed(lean_object* v_cls_1971_, lean_object* v_msg_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__9(v_cls_1971_, v_msg_1972_, v___y_1973_, v___y_1974_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
return v_res_1976_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1977_; 
v___x_1977_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_1977_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1978_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_1979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1978_);
return v___x_1979_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__2(void){
_start:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1980_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__1);
v___x_1981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1980_);
lean_ctor_set(v___x_1981_, 1, v___x_1980_);
return v___x_1981_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__6(void){
_start:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1986_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__5));
v___x_1987_ = l_Lean_stringToMessageData(v___x_1986_);
return v___x_1987_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__8(void){
_start:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1989_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__7));
v___x_1990_ = l_Lean_stringToMessageData(v___x_1989_);
return v___x_1990_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__9(void){
_start:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1991_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44___closed__0));
v___x_1992_ = l_Lean_stringToMessageData(v___x_1991_);
return v___x_1992_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__11(void){
_start:
{
lean_object* v_cls_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; 
v_cls_1995_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__4));
v___x_1996_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__10));
v___x_1997_ = l_Lean_Name_append(v___x_1996_, v_cls_1995_);
return v___x_1997_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__13(void){
_start:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1999_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__12));
v___x_2000_ = l_Lean_stringToMessageData(v___x_1999_);
return v___x_2000_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__15(void){
_start:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_2002_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__14));
v___x_2003_ = l_Lean_stringToMessageData(v___x_2002_);
return v___x_2003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4(lean_object* v_mod_2008_, uint8_t v_isMeta_2009_, lean_object* v_hint_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_){
_start:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v_env_2016_; uint8_t v_isExporting_2017_; lean_object* v_entry_2018_; lean_object* v___x_2019_; lean_object* v_env_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___y_2025_; lean_object* v___x_2051_; uint8_t v___x_2052_; 
v___x_2014_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__0);
v___x_2015_ = lean_st_ref_get(v___y_2012_);
v_env_2016_ = lean_ctor_get(v___x_2015_, 0);
lean_inc_ref(v_env_2016_);
lean_dec(v___x_2015_);
v_isExporting_2017_ = lean_ctor_get_uint8(v_env_2016_, sizeof(void*)*8);
lean_dec_ref(v_env_2016_);
lean_inc(v_mod_2008_);
v_entry_2018_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2018_, 0, v_mod_2008_);
lean_ctor_set_uint8(v_entry_2018_, sizeof(void*)*1, v_isExporting_2017_);
lean_ctor_set_uint8(v_entry_2018_, sizeof(void*)*1 + 1, v_isMeta_2009_);
v___x_2019_ = lean_st_ref_get(v___y_2012_);
v_env_2020_ = lean_ctor_get(v___x_2019_, 0);
lean_inc_ref(v_env_2020_);
lean_dec(v___x_2019_);
v___x_2021_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2022_ = lean_box(1);
v___x_2023_ = lean_box(0);
v___x_2051_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2014_, v___x_2021_, v_env_2020_, v___x_2022_, v___x_2023_);
v___x_2052_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg(v___x_2051_, v_entry_2018_);
lean_dec(v___x_2051_);
if (v___x_2052_ == 0)
{
lean_object* v_toCold_2053_; lean_object* v_options_2054_; uint8_t v_hasTrace_2055_; 
v_toCold_2053_ = lean_ctor_get(v___y_2011_, 0);
v_options_2054_ = lean_ctor_get(v_toCold_2053_, 2);
v_hasTrace_2055_ = lean_ctor_get_uint8(v_options_2054_, sizeof(void*)*1);
if (v_hasTrace_2055_ == 0)
{
lean_dec(v_hint_2010_);
lean_dec(v_mod_2008_);
v___y_2025_ = v___y_2012_;
goto v___jp_2024_;
}
else
{
lean_object* v_inheritedTraceOptions_2056_; lean_object* v_cls_2057_; lean_object* v___y_2059_; lean_object* v___y_2060_; lean_object* v___y_2064_; lean_object* v___y_2065_; lean_object* v___x_2077_; uint8_t v___x_2078_; 
v_inheritedTraceOptions_2056_ = lean_ctor_get(v_toCold_2053_, 11);
v_cls_2057_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__4));
v___x_2077_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__11);
v___x_2078_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2056_, v_options_2054_, v___x_2077_);
if (v___x_2078_ == 0)
{
lean_dec(v_hint_2010_);
lean_dec(v_mod_2008_);
v___y_2025_ = v___y_2012_;
goto v___jp_2024_;
}
else
{
lean_object* v___x_2079_; lean_object* v___y_2081_; 
v___x_2079_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__13);
if (v_isExporting_2017_ == 0)
{
lean_object* v___x_2088_; 
v___x_2088_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__18));
v___y_2081_ = v___x_2088_;
goto v___jp_2080_;
}
else
{
lean_object* v___x_2089_; 
v___x_2089_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__19));
v___y_2081_ = v___x_2089_;
goto v___jp_2080_;
}
v___jp_2080_:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
lean_inc_ref(v___y_2081_);
v___x_2082_ = l_Lean_stringToMessageData(v___y_2081_);
v___x_2083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2079_);
lean_ctor_set(v___x_2083_, 1, v___x_2082_);
v___x_2084_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__15, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__15_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__15);
v___x_2085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2083_);
lean_ctor_set(v___x_2085_, 1, v___x_2084_);
if (v_isMeta_2009_ == 0)
{
lean_object* v___x_2086_; 
v___x_2086_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__16));
v___y_2064_ = v___x_2085_;
v___y_2065_ = v___x_2086_;
goto v___jp_2063_;
}
else
{
lean_object* v___x_2087_; 
v___x_2087_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__17));
v___y_2064_ = v___x_2085_;
v___y_2065_ = v___x_2087_;
goto v___jp_2063_;
}
}
}
v___jp_2058_:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2061_, 0, v___y_2059_);
lean_ctor_set(v___x_2061_, 1, v___y_2060_);
v___x_2062_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__9(v_cls_2057_, v___x_2061_, v___y_2011_, v___y_2012_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_dec_ref_known(v___x_2062_, 1);
v___y_2025_ = v___y_2012_;
goto v___jp_2024_;
}
else
{
lean_dec_ref_known(v_entry_2018_, 1);
return v___x_2062_;
}
}
v___jp_2063_:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; uint8_t v___x_2072_; 
lean_inc_ref(v___y_2065_);
v___x_2066_ = l_Lean_stringToMessageData(v___y_2065_);
v___x_2067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2067_, 0, v___y_2064_);
lean_ctor_set(v___x_2067_, 1, v___x_2066_);
v___x_2068_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__6);
v___x_2069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2067_);
lean_ctor_set(v___x_2069_, 1, v___x_2068_);
v___x_2070_ = l_Lean_MessageData_ofName(v_mod_2008_);
v___x_2071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2069_);
lean_ctor_set(v___x_2071_, 1, v___x_2070_);
v___x_2072_ = l_Lean_Name_isAnonymous(v_hint_2010_);
if (v___x_2072_ == 0)
{
lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2073_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__8);
v___x_2074_ = l_Lean_MessageData_ofName(v_hint_2010_);
v___x_2075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2073_);
lean_ctor_set(v___x_2075_, 1, v___x_2074_);
v___y_2059_ = v___x_2071_;
v___y_2060_ = v___x_2075_;
goto v___jp_2058_;
}
else
{
lean_object* v___x_2076_; 
lean_dec(v_hint_2010_);
v___x_2076_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__9);
v___y_2059_ = v___x_2071_;
v___y_2060_ = v___x_2076_;
goto v___jp_2058_;
}
}
}
}
else
{
lean_object* v___x_2090_; lean_object* v___x_2091_; 
lean_dec_ref_known(v_entry_2018_, 1);
lean_dec(v_hint_2010_);
lean_dec(v_mod_2008_);
v___x_2090_ = lean_box(0);
v___x_2091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2090_);
return v___x_2091_;
}
v___jp_2024_:
{
lean_object* v___x_2026_; lean_object* v_toEnvExtension_2027_; lean_object* v_env_2028_; lean_object* v_nextMacroScope_2029_; lean_object* v_ngen_2030_; lean_object* v_auxDeclNGen_2031_; lean_object* v_traceState_2032_; lean_object* v_recordedDeps_2033_; lean_object* v_messages_2034_; lean_object* v_infoState_2035_; lean_object* v_snapshotTasks_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2049_; 
v___x_2026_ = lean_st_ref_take(v___y_2025_);
v_toEnvExtension_2027_ = lean_ctor_get(v___x_2021_, 0);
v_env_2028_ = lean_ctor_get(v___x_2026_, 0);
v_nextMacroScope_2029_ = lean_ctor_get(v___x_2026_, 1);
v_ngen_2030_ = lean_ctor_get(v___x_2026_, 2);
v_auxDeclNGen_2031_ = lean_ctor_get(v___x_2026_, 3);
v_traceState_2032_ = lean_ctor_get(v___x_2026_, 4);
v_recordedDeps_2033_ = lean_ctor_get(v___x_2026_, 6);
v_messages_2034_ = lean_ctor_get(v___x_2026_, 7);
v_infoState_2035_ = lean_ctor_get(v___x_2026_, 8);
v_snapshotTasks_2036_ = lean_ctor_get(v___x_2026_, 9);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2049_ == 0)
{
lean_object* v_unused_2050_; 
v_unused_2050_ = lean_ctor_get(v___x_2026_, 5);
lean_dec(v_unused_2050_);
v___x_2038_ = v___x_2026_;
v_isShared_2039_ = v_isSharedCheck_2049_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_snapshotTasks_2036_);
lean_inc(v_infoState_2035_);
lean_inc(v_messages_2034_);
lean_inc(v_recordedDeps_2033_);
lean_inc(v_traceState_2032_);
lean_inc(v_auxDeclNGen_2031_);
lean_inc(v_ngen_2030_);
lean_inc(v_nextMacroScope_2029_);
lean_inc(v_env_2028_);
lean_dec(v___x_2026_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2049_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v_asyncMode_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2045_; 
v_asyncMode_2040_ = lean_ctor_get(v_toEnvExtension_2027_, 2);
v___x_2041_ = lean_box(0);
v___x_2042_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2021_, v_env_2028_, v_entry_2018_, v_asyncMode_2040_, v___x_2023_);
v___x_2043_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__2);
if (v_isShared_2039_ == 0)
{
lean_ctor_set(v___x_2038_, 5, v___x_2043_);
lean_ctor_set(v___x_2038_, 0, v___x_2042_);
v___x_2045_ = v___x_2038_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2042_);
lean_ctor_set(v_reuseFailAlloc_2048_, 1, v_nextMacroScope_2029_);
lean_ctor_set(v_reuseFailAlloc_2048_, 2, v_ngen_2030_);
lean_ctor_set(v_reuseFailAlloc_2048_, 3, v_auxDeclNGen_2031_);
lean_ctor_set(v_reuseFailAlloc_2048_, 4, v_traceState_2032_);
lean_ctor_set(v_reuseFailAlloc_2048_, 5, v___x_2043_);
lean_ctor_set(v_reuseFailAlloc_2048_, 6, v_recordedDeps_2033_);
lean_ctor_set(v_reuseFailAlloc_2048_, 7, v_messages_2034_);
lean_ctor_set(v_reuseFailAlloc_2048_, 8, v_infoState_2035_);
lean_ctor_set(v_reuseFailAlloc_2048_, 9, v_snapshotTasks_2036_);
v___x_2045_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2046_ = lean_st_ref_put(v___y_2025_, v___x_2045_);
v___x_2047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2041_);
return v___x_2047_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___boxed(lean_object* v_mod_2092_, lean_object* v_isMeta_2093_, lean_object* v_hint_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
uint8_t v_isMeta_boxed_2098_; lean_object* v_res_2099_; 
v_isMeta_boxed_2098_ = lean_unbox(v_isMeta_2093_);
v_res_2099_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4(v_mod_2092_, v_isMeta_boxed_2098_, v_hint_2094_, v___y_2095_, v___y_2096_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
return v_res_2099_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__5(lean_object* v___x_2100_, lean_object* v_declName_2101_, lean_object* v_as_2102_, size_t v_sz_2103_, size_t v_i_2104_, lean_object* v_b_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_){
_start:
{
uint8_t v___x_2109_; 
v___x_2109_ = lean_usize_dec_lt(v_i_2104_, v_sz_2103_);
if (v___x_2109_ == 0)
{
lean_object* v___x_2110_; 
lean_dec(v_declName_2101_);
v___x_2110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2110_, 0, v_b_2105_);
return v___x_2110_;
}
else
{
lean_object* v___x_2111_; lean_object* v_modules_2112_; lean_object* v___x_2113_; lean_object* v_a_2114_; lean_object* v___x_2115_; lean_object* v_toImport_2116_; lean_object* v_module_2117_; lean_object* v___x_2118_; uint8_t v___x_2119_; lean_object* v___x_2120_; 
v___x_2111_ = l_Lean_Environment_header(v___x_2100_);
v_modules_2112_ = lean_ctor_get(v___x_2111_, 3);
lean_inc_ref(v_modules_2112_);
lean_dec_ref(v___x_2111_);
v___x_2113_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2114_ = lean_array_uget_borrowed(v_as_2102_, v_i_2104_);
v___x_2115_ = lean_array_get(v___x_2113_, v_modules_2112_, v_a_2114_);
lean_dec_ref(v_modules_2112_);
v_toImport_2116_ = lean_ctor_get(v___x_2115_, 0);
lean_inc_ref(v_toImport_2116_);
lean_dec(v___x_2115_);
v_module_2117_ = lean_ctor_get(v_toImport_2116_, 0);
lean_inc(v_module_2117_);
lean_dec_ref(v_toImport_2116_);
v___x_2118_ = lean_box(0);
v___x_2119_ = 0;
lean_inc(v_declName_2101_);
v___x_2120_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4(v_module_2117_, v___x_2119_, v_declName_2101_, v___y_2106_, v___y_2107_);
if (lean_obj_tag(v___x_2120_) == 0)
{
size_t v___x_2121_; size_t v___x_2122_; 
lean_dec_ref_known(v___x_2120_, 1);
v___x_2121_ = ((size_t)1ULL);
v___x_2122_ = lean_usize_add(v_i_2104_, v___x_2121_);
v_i_2104_ = v___x_2122_;
v_b_2105_ = v___x_2118_;
goto _start;
}
else
{
lean_dec(v_declName_2101_);
return v___x_2120_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__5___boxed(lean_object* v___x_2124_, lean_object* v_declName_2125_, lean_object* v_as_2126_, lean_object* v_sz_2127_, lean_object* v_i_2128_, lean_object* v_b_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
size_t v_sz_boxed_2133_; size_t v_i_boxed_2134_; lean_object* v_res_2135_; 
v_sz_boxed_2133_ = lean_unbox_usize(v_sz_2127_);
lean_dec(v_sz_2127_);
v_i_boxed_2134_ = lean_unbox_usize(v_i_2128_);
lean_dec(v_i_2128_);
v_res_2135_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__5(v___x_2124_, v_declName_2125_, v_as_2126_, v_sz_boxed_2133_, v_i_boxed_2134_, v_b_2129_, v___y_2130_, v___y_2131_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec_ref(v_as_2126_);
lean_dec_ref(v___x_2124_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg(lean_object* v_a_2136_, lean_object* v_x_2137_){
_start:
{
if (lean_obj_tag(v_x_2137_) == 0)
{
lean_object* v___x_2138_; 
v___x_2138_ = lean_box(0);
return v___x_2138_;
}
else
{
lean_object* v_key_2139_; lean_object* v_value_2140_; lean_object* v_tail_2141_; uint8_t v___x_2142_; 
v_key_2139_ = lean_ctor_get(v_x_2137_, 0);
v_value_2140_ = lean_ctor_get(v_x_2137_, 1);
v_tail_2141_ = lean_ctor_get(v_x_2137_, 2);
v___x_2142_ = lean_name_eq(v_key_2139_, v_a_2136_);
if (v___x_2142_ == 0)
{
v_x_2137_ = v_tail_2141_;
goto _start;
}
else
{
lean_object* v___x_2144_; 
lean_inc(v_value_2140_);
v___x_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2144_, 0, v_value_2140_);
return v___x_2144_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg___boxed(lean_object* v_a_2145_, lean_object* v_x_2146_){
_start:
{
lean_object* v_res_2147_; 
v_res_2147_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg(v_a_2145_, v_x_2146_);
lean_dec(v_x_2146_);
lean_dec(v_a_2145_);
return v_res_2147_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6___redArg(lean_object* v_m_2148_, lean_object* v_a_2149_){
_start:
{
lean_object* v_buckets_2150_; lean_object* v___x_2151_; uint64_t v___y_2153_; 
v_buckets_2150_ = lean_ctor_get(v_m_2148_, 1);
v___x_2151_ = lean_array_get_size(v_buckets_2150_);
if (lean_obj_tag(v_a_2149_) == 0)
{
uint64_t v___x_2167_; 
v___x_2167_ = 1723ULL;
v___y_2153_ = v___x_2167_;
goto v___jp_2152_;
}
else
{
uint64_t v_hash_2168_; 
v_hash_2168_ = lean_ctor_get_uint64(v_a_2149_, sizeof(void*)*2);
v___y_2153_ = v_hash_2168_;
goto v___jp_2152_;
}
v___jp_2152_:
{
uint64_t v___x_2154_; uint64_t v___x_2155_; uint64_t v_fold_2156_; uint64_t v___x_2157_; uint64_t v___x_2158_; uint64_t v___x_2159_; size_t v___x_2160_; size_t v___x_2161_; size_t v___x_2162_; size_t v___x_2163_; size_t v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2154_ = 32ULL;
v___x_2155_ = lean_uint64_shift_right(v___y_2153_, v___x_2154_);
v_fold_2156_ = lean_uint64_xor(v___y_2153_, v___x_2155_);
v___x_2157_ = 16ULL;
v___x_2158_ = lean_uint64_shift_right(v_fold_2156_, v___x_2157_);
v___x_2159_ = lean_uint64_xor(v_fold_2156_, v___x_2158_);
v___x_2160_ = lean_uint64_to_usize(v___x_2159_);
v___x_2161_ = lean_usize_of_nat(v___x_2151_);
v___x_2162_ = ((size_t)1ULL);
v___x_2163_ = lean_usize_sub(v___x_2161_, v___x_2162_);
v___x_2164_ = lean_usize_land(v___x_2160_, v___x_2163_);
v___x_2165_ = lean_array_uget_borrowed(v_buckets_2150_, v___x_2164_);
v___x_2166_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg(v_a_2149_, v___x_2165_);
return v___x_2166_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6___redArg___boxed(lean_object* v_m_2169_, lean_object* v_a_2170_){
_start:
{
lean_object* v_res_2171_; 
v_res_2171_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6___redArg(v_m_2169_, v_a_2170_);
lean_dec(v_a_2170_);
lean_dec_ref(v_m_2169_);
return v_res_2171_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2___closed__0(void){
_start:
{
lean_object* v___x_2172_; 
v___x_2172_ = l_Std_HashMap_instInhabited___redArg();
return v___x_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2(lean_object* v_declName_2175_, uint8_t v_isMeta_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_){
_start:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v_env_2185_; lean_object* v___y_2187_; lean_object* v___x_2200_; 
v___x_2180_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2___closed__0);
v___x_2181_ = lean_st_ref_get(v___y_2178_);
v_env_2185_ = lean_ctor_get(v___x_2181_, 0);
lean_inc_ref(v_env_2185_);
lean_dec(v___x_2181_);
v___x_2200_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2185_, v_declName_2175_);
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_dec_ref(v_env_2185_);
lean_dec(v_declName_2175_);
goto v___jp_2182_;
}
else
{
lean_object* v_val_2201_; lean_object* v___x_2202_; lean_object* v_modules_2203_; lean_object* v___x_2204_; uint8_t v___x_2205_; 
v_val_2201_ = lean_ctor_get(v___x_2200_, 0);
lean_inc(v_val_2201_);
lean_dec_ref_known(v___x_2200_, 1);
v___x_2202_ = l_Lean_Environment_header(v_env_2185_);
v_modules_2203_ = lean_ctor_get(v___x_2202_, 3);
lean_inc_ref(v_modules_2203_);
lean_dec_ref(v___x_2202_);
v___x_2204_ = lean_array_get_size(v_modules_2203_);
v___x_2205_ = lean_nat_dec_lt(v_val_2201_, v___x_2204_);
if (v___x_2205_ == 0)
{
lean_dec_ref(v_modules_2203_);
lean_dec(v_val_2201_);
lean_dec_ref(v_env_2185_);
lean_dec(v_declName_2175_);
goto v___jp_2182_;
}
else
{
lean_object* v___x_2206_; lean_object* v___x_2207_; uint8_t v___y_2209_; 
v___x_2206_ = lean_array_fget(v_modules_2203_, v_val_2201_);
lean_dec(v_val_2201_);
lean_dec_ref(v_modules_2203_);
v___x_2207_ = lean_st_ref_get(v___y_2178_);
if (v_isMeta_2176_ == 0)
{
lean_dec(v___x_2207_);
v___y_2209_ = v_isMeta_2176_;
goto v___jp_2208_;
}
else
{
lean_object* v_env_2220_; uint8_t v___x_2221_; 
v_env_2220_ = lean_ctor_get(v___x_2207_, 0);
lean_inc_ref(v_env_2220_);
lean_dec(v___x_2207_);
lean_inc(v_declName_2175_);
v___x_2221_ = l_Lean_isMarkedMeta(v_env_2220_, v_declName_2175_);
if (v___x_2221_ == 0)
{
v___y_2209_ = v_isMeta_2176_;
goto v___jp_2208_;
}
else
{
uint8_t v___x_2222_; 
v___x_2222_ = 0;
v___y_2209_ = v___x_2222_;
goto v___jp_2208_;
}
}
v___jp_2208_:
{
lean_object* v_toImport_2210_; lean_object* v_module_2211_; lean_object* v___x_2212_; 
v_toImport_2210_ = lean_ctor_get(v___x_2206_, 0);
lean_inc_ref(v_toImport_2210_);
lean_dec(v___x_2206_);
v_module_2211_ = lean_ctor_get(v_toImport_2210_, 0);
lean_inc(v_module_2211_);
lean_dec_ref(v_toImport_2210_);
lean_inc(v_declName_2175_);
v___x_2212_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4(v_module_2211_, v___y_2209_, v_declName_2175_, v___y_2177_, v___y_2178_);
if (lean_obj_tag(v___x_2212_) == 0)
{
lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
lean_dec_ref_known(v___x_2212_, 1);
v___x_2213_ = l_Lean_indirectModUseExt;
v___x_2214_ = lean_box(1);
v___x_2215_ = lean_box(0);
lean_inc_ref(v_env_2185_);
v___x_2216_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2180_, v___x_2213_, v_env_2185_, v___x_2214_, v___x_2215_);
v___x_2217_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6___redArg(v___x_2216_, v_declName_2175_);
lean_dec(v___x_2216_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v___x_2218_; 
v___x_2218_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2___closed__1));
v___y_2187_ = v___x_2218_;
goto v___jp_2186_;
}
else
{
lean_object* v_val_2219_; 
v_val_2219_ = lean_ctor_get(v___x_2217_, 0);
lean_inc(v_val_2219_);
lean_dec_ref_known(v___x_2217_, 1);
v___y_2187_ = v_val_2219_;
goto v___jp_2186_;
}
}
else
{
lean_dec_ref(v_env_2185_);
lean_dec(v_declName_2175_);
return v___x_2212_;
}
}
}
}
v___jp_2182_:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2183_ = lean_box(0);
v___x_2184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2183_);
return v___x_2184_;
}
v___jp_2186_:
{
lean_object* v___x_2188_; size_t v_sz_2189_; size_t v___x_2190_; lean_object* v___x_2191_; 
v___x_2188_ = lean_box(0);
v_sz_2189_ = lean_array_size(v___y_2187_);
v___x_2190_ = ((size_t)0ULL);
v___x_2191_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__5(v_env_2185_, v_declName_2175_, v___y_2187_, v_sz_2189_, v___x_2190_, v___x_2188_, v___y_2177_, v___y_2178_);
lean_dec_ref(v___y_2187_);
lean_dec_ref(v_env_2185_);
if (lean_obj_tag(v___x_2191_) == 0)
{
lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2198_; 
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2198_ == 0)
{
lean_object* v_unused_2199_; 
v_unused_2199_ = lean_ctor_get(v___x_2191_, 0);
lean_dec(v_unused_2199_);
v___x_2193_ = v___x_2191_;
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
else
{
lean_dec(v___x_2191_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2196_; 
if (v_isShared_2194_ == 0)
{
lean_ctor_set(v___x_2193_, 0, v___x_2188_);
v___x_2196_ = v___x_2193_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v___x_2188_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
}
else
{
return v___x_2191_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2___boxed(lean_object* v_declName_2223_, lean_object* v_isMeta_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_){
_start:
{
uint8_t v_isMeta_boxed_2228_; lean_object* v_res_2229_; 
v_isMeta_boxed_2228_ = lean_unbox(v_isMeta_2224_);
v_res_2229_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2(v_declName_2223_, v_isMeta_boxed_2228_, v___y_2225_, v___y_2226_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
return v_res_2229_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__2_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2233_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__1_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2234_ = l_Lean_MessageData_ofFormat(v___x_2233_);
return v___x_2234_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__5_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2238_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__4_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2239_ = l_Lean_MessageData_ofFormat(v___x_2238_);
return v___x_2239_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2241_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2242_ = l_Lean_stringToMessageData(v___x_2241_);
return v___x_2242_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2244_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2245_ = l_Lean_stringToMessageData(v___x_2244_);
return v___x_2245_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__11_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; 
v___x_2247_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__10_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2248_ = l_Lean_stringToMessageData(v___x_2247_);
return v___x_2248_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__14_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2252_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__13_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2253_ = l_Lean_MessageData_ofFormat(v___x_2252_);
return v___x_2253_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__15_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2254_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__14_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__14_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__14_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2255_ = l_Lean_MessageData_hint_x27(v___x_2254_);
return v___x_2255_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2257_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2258_ = l_Lean_stringToMessageData(v___x_2257_);
return v___x_2258_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__20_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2262_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__19_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2263_ = l_Lean_MessageData_ofFormat(v___x_2262_);
return v___x_2263_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__25_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2270_; lean_object* v___x_2271_; 
v___x_2270_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__24_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2271_ = l_Lean_MessageData_ofFormat(v___x_2270_);
return v___x_2271_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2272_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__25_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__25_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__25_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2272_);
return v___x_2273_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2277_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__28_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2278_ = l_Lean_MessageData_ofFormat(v___x_2277_);
return v___x_2278_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2279_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_2280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2279_);
return v___x_2280_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2281_ = lean_box(1);
v___x_2282_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_2283_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2284_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2283_);
lean_ctor_set(v___x_2284_, 1, v___x_2282_);
lean_ctor_set(v___x_2284_, 2, v___x_2281_);
return v___x_2284_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2287_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2288_ = lean_unsigned_to_nat(0u);
v___x_2289_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2288_);
lean_ctor_set(v___x_2289_, 1, v___x_2288_);
lean_ctor_set(v___x_2289_, 2, v___x_2288_);
lean_ctor_set(v___x_2289_, 3, v___x_2288_);
lean_ctor_set(v___x_2289_, 4, v___x_2287_);
lean_ctor_set(v___x_2289_, 5, v___x_2287_);
lean_ctor_set(v___x_2289_, 6, v___x_2287_);
lean_ctor_set(v___x_2289_, 7, v___x_2287_);
lean_ctor_set(v___x_2289_, 8, v___x_2287_);
lean_ctor_set(v___x_2289_, 9, v___x_2287_);
lean_ctor_set(v___x_2289_, 10, v___x_2287_);
return v___x_2289_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2290_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2291_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2290_);
lean_ctor_set(v___x_2291_, 1, v___x_2290_);
lean_ctor_set(v___x_2291_, 2, v___x_2290_);
lean_ctor_set(v___x_2291_, 3, v___x_2290_);
lean_ctor_set(v___x_2291_, 4, v___x_2290_);
lean_ctor_set(v___x_2291_, 5, v___x_2290_);
return v___x_2291_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2292_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2293_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2292_);
lean_ctor_set(v___x_2293_, 1, v___x_2292_);
lean_ctor_set(v___x_2293_, 2, v___x_2292_);
lean_ctor_set(v___x_2293_, 3, v___x_2292_);
lean_ctor_set(v___x_2293_, 4, v___x_2292_);
return v___x_2293_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__37_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2295_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__36_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2296_ = l_Lean_stringToMessageData(v___x_2295_);
return v___x_2296_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__39_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2298_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__38_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2299_ = l_Lean_stringToMessageData(v___x_2298_);
return v___x_2299_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; 
v___x_2301_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__40_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2302_ = l_Lean_stringToMessageData(v___x_2301_);
return v___x_2302_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2304_; lean_object* v___x_2305_; 
v___x_2304_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2305_ = l_Lean_stringToMessageData(v___x_2304_);
return v___x_2305_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2307_; lean_object* v___x_2308_; 
v___x_2307_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2308_ = l_Lean_stringToMessageData(v___x_2307_);
return v___x_2308_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__47_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2310_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2311_ = l_Lean_stringToMessageData(v___x_2310_);
return v___x_2311_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__49_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2313_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__48_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2314_ = l_Lean_stringToMessageData(v___x_2313_);
return v___x_2314_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__51_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2316_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__50_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2317_ = l_Lean_stringToMessageData(v___x_2316_);
return v___x_2317_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__53_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2319_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__52_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2320_ = l_Lean_stringToMessageData(v___x_2319_);
return v___x_2320_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__55_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2322_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__54_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2323_ = l_Lean_stringToMessageData(v___x_2322_);
return v___x_2323_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__57_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; 
v___x_2325_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__56_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2326_ = l_Lean_stringToMessageData(v___x_2325_);
return v___x_2326_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__59_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2328_; lean_object* v___x_2329_; 
v___x_2328_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__58_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2329_ = l_Lean_stringToMessageData(v___x_2328_);
return v___x_2329_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__61_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2331_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__60_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2332_ = l_Lean_stringToMessageData(v___x_2331_);
return v___x_2332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(lean_object* v___x_2333_, lean_object* v___x_2334_, lean_object* v___f_2335_, uint8_t v___x_2336_, lean_object* v___x_2337_, lean_object* v___x_2338_, lean_object* v_a_2339_, lean_object* v_declName_2340_, lean_object* v_stx_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_){
_start:
{
lean_object* v___y_2346_; lean_object* v___y_2347_; lean_object* v___y_2348_; lean_object* v___x_2351_; uint8_t v___x_2352_; lean_object* v___y_2354_; lean_object* v___y_2355_; lean_object* v___y_2356_; lean_object* v___y_2357_; lean_object* v___y_2358_; lean_object* v___y_2370_; lean_object* v___y_2371_; lean_object* v___y_2372_; lean_object* v___y_2373_; lean_object* v___y_2374_; lean_object* v___y_2375_; lean_object* v___y_2387_; lean_object* v___y_2388_; lean_object* v___y_2389_; lean_object* v___y_2390_; lean_object* v___y_2391_; lean_object* v___y_2392_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___y_2406_; lean_object* v___y_2407_; lean_object* v___y_2408_; lean_object* v___y_2409_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v_hint_2427_; lean_object* v___y_2428_; lean_object* v___y_2429_; lean_object* v___y_2452_; lean_object* v___y_2453_; lean_object* v___y_2454_; lean_object* v___y_2455_; lean_object* v___y_2456_; lean_object* v___y_2457_; lean_object* v___y_2458_; lean_object* v___y_2459_; 
v___x_2351_ = l_Lean_Name_mkStr2(v___x_2333_, v___x_2334_);
lean_inc(v_stx_2341_);
v___x_2352_ = l_Lean_Syntax_isOfKind(v_stx_2341_, v___x_2351_);
lean_dec(v___x_2351_);
if (v___x_2352_ == 0)
{
lean_object* v___x_2461_; lean_object* v___x_2462_; 
lean_dec(v_stx_2341_);
lean_dec(v_declName_2340_);
lean_dec_ref(v___x_2338_);
lean_dec(v___x_2337_);
lean_dec_ref(v___f_2335_);
v___x_2461_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2462_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___redArg(v___x_2461_, v___y_2342_, v___y_2343_);
return v___x_2462_;
}
else
{
lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___y_2466_; lean_object* v___y_2467_; lean_object* v___y_2468_; lean_object* v___y_2469_; lean_object* v___y_2470_; lean_object* v___y_2471_; lean_object* v___y_2472_; lean_object* v___y_2473_; lean_object* v_val_2474_; lean_object* v___y_2499_; lean_object* v___y_2500_; lean_object* v___y_2501_; lean_object* v___y_2502_; lean_object* v___y_2503_; lean_object* v___y_2504_; lean_object* v___y_2505_; lean_object* v___y_2506_; lean_object* v___y_2511_; lean_object* v___y_2512_; lean_object* v___y_2513_; lean_object* v___y_2514_; lean_object* v___y_2515_; lean_object* v___y_2516_; lean_object* v___y_2517_; lean_object* v___y_2518_; lean_object* v___y_2519_; uint8_t v___y_2520_; uint8_t v_a_2521_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; uint8_t v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2586_; lean_object* v___y_2587_; uint8_t v___y_2588_; lean_object* v_msg_2589_; lean_object* v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2602_; lean_object* v___y_2603_; lean_object* v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; uint8_t v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2611_; lean_object* v___y_2612_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v_a_2615_; lean_object* v___y_2648_; lean_object* v___y_2649_; lean_object* v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2753_; lean_object* v___y_2754_; lean_object* v___y_2755_; lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v_a_2759_; lean_object* v___y_2777_; lean_object* v___y_2778_; lean_object* v___y_2779_; lean_object* v_since_x3f_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2798_; lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v_typeChanged_x3f_2801_; lean_object* v___y_2802_; lean_object* v___y_2803_; lean_object* v___y_2815_; lean_object* v_text_x3f_2816_; lean_object* v___y_2817_; lean_object* v___y_2818_; lean_object* v_id_x3f_2829_; lean_object* v___y_2830_; lean_object* v___y_2831_; lean_object* v___x_2841_; uint8_t v___x_2842_; 
v___x_2463_ = lean_unsigned_to_nat(0u);
v___x_2464_ = lean_unsigned_to_nat(1u);
v___x_2841_ = l_Lean_Syntax_getArg(v_stx_2341_, v___x_2464_);
v___x_2842_ = l_Lean_Syntax_isNone(v___x_2841_);
if (v___x_2842_ == 0)
{
uint8_t v___x_2843_; 
lean_inc(v___x_2841_);
v___x_2843_ = l_Lean_Syntax_matchesNull(v___x_2841_, v___x_2464_);
if (v___x_2843_ == 0)
{
lean_object* v___x_2844_; lean_object* v___x_2845_; 
lean_dec(v___x_2841_);
lean_dec(v_stx_2341_);
lean_dec(v_declName_2340_);
lean_dec_ref(v___x_2338_);
lean_dec(v___x_2337_);
lean_dec_ref(v___f_2335_);
v___x_2844_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2845_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___redArg(v___x_2844_, v___y_2342_, v___y_2343_);
return v___x_2845_;
}
else
{
lean_object* v___x_2846_; lean_object* v___x_2847_; 
v___x_2846_ = l_Lean_Syntax_getArg(v___x_2841_, v___x_2463_);
lean_dec(v___x_2841_);
v___x_2847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2847_, 0, v___x_2846_);
v_id_x3f_2829_ = v___x_2847_;
v___y_2830_ = v___y_2342_;
v___y_2831_ = v___y_2343_;
goto v___jp_2828_;
}
}
else
{
lean_object* v___x_2848_; 
lean_dec(v___x_2841_);
v___x_2848_ = lean_box(0);
v_id_x3f_2829_ = v___x_2848_;
v___y_2830_ = v___y_2342_;
v___y_2831_ = v___y_2343_;
goto v___jp_2828_;
}
v___jp_2465_:
{
lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; uint8_t v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; 
v___x_2475_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__20_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__20_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__20_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2476_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__22_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2477_ = lean_box(0);
v___x_2478_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2479_, 0, v___f_2335_);
v___x_2480_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2476_);
lean_ctor_set(v___x_2480_, 1, v___x_2477_);
lean_ctor_set(v___x_2480_, 2, v___x_2477_);
lean_ctor_set(v___x_2480_, 3, v___x_2477_);
lean_ctor_set(v___x_2480_, 4, v___x_2478_);
lean_ctor_set(v___x_2480_, 5, v___x_2479_);
lean_inc(v_val_2474_);
v___x_2481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2481_, 0, v_val_2474_);
lean_ctor_set(v___x_2481_, 1, v_val_2474_);
v___x_2482_ = l_Lean_Syntax_ofRange(v___x_2481_, v___x_2352_);
v___x_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2482_);
v___x_2484_ = 4;
v___x_2485_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2485_, 0, v___x_2480_);
lean_ctor_set(v___x_2485_, 1, v___x_2483_);
lean_ctor_set(v___x_2485_, 2, v___x_2477_);
lean_ctor_set_uint8(v___x_2485_, sizeof(void*)*3, v___x_2484_);
v___x_2486_ = lean_mk_empty_array_with_capacity(v___x_2464_);
v___x_2487_ = lean_array_push(v___x_2486_, v___x_2485_);
v___x_2488_ = l_Lean_MessageData_hint(v___x_2475_, v___x_2487_, v___x_2477_, v___x_2477_, v___x_2336_, v___y_2468_, v___y_2467_);
lean_dec_ref(v___x_2487_);
if (lean_obj_tag(v___x_2488_) == 0)
{
lean_object* v_a_2489_; 
v_a_2489_ = lean_ctor_get(v___x_2488_, 0);
lean_inc(v_a_2489_);
lean_dec_ref_known(v___x_2488_, 1);
v___y_2421_ = v___y_2466_;
v___y_2422_ = v___y_2470_;
v___y_2423_ = v___y_2469_;
v___y_2424_ = v___y_2472_;
v___y_2425_ = v___y_2471_;
v___y_2426_ = v___y_2473_;
v_hint_2427_ = v_a_2489_;
v___y_2428_ = v___y_2468_;
v___y_2429_ = v___y_2467_;
goto v___jp_2420_;
}
else
{
lean_object* v_a_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2497_; 
lean_dec(v___y_2473_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
lean_dec(v___y_2470_);
lean_dec(v___y_2469_);
lean_dec_ref(v___y_2466_);
v_a_2490_ = lean_ctor_get(v___x_2488_, 0);
v_isSharedCheck_2497_ = !lean_is_exclusive(v___x_2488_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2492_ = v___x_2488_;
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_a_2490_);
lean_dec(v___x_2488_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v___x_2495_; 
if (v_isShared_2493_ == 0)
{
v___x_2495_ = v___x_2492_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_a_2490_);
v___x_2495_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
return v___x_2495_;
}
}
}
}
v___jp_2498_:
{
if (lean_obj_tag(v___y_2505_) == 0)
{
lean_dec_ref(v___f_2335_);
v___y_2452_ = v___y_2499_;
v___y_2453_ = v___y_2500_;
v___y_2454_ = v___y_2501_;
v___y_2455_ = v___y_2503_;
v___y_2456_ = v___y_2502_;
v___y_2457_ = v___y_2504_;
v___y_2458_ = v___y_2505_;
v___y_2459_ = v___y_2506_;
goto v___jp_2451_;
}
else
{
lean_object* v_val_2507_; lean_object* v___x_2508_; 
v_val_2507_ = lean_ctor_get(v___y_2505_, 0);
v___x_2508_ = l_Lean_Syntax_getTailPos_x3f(v_val_2507_, v___x_2352_);
if (lean_obj_tag(v___x_2508_) == 1)
{
lean_object* v_val_2509_; 
v_val_2509_ = lean_ctor_get(v___x_2508_, 0);
lean_inc(v_val_2509_);
lean_dec_ref_known(v___x_2508_, 1);
v___y_2466_ = v___y_2499_;
v___y_2467_ = v___y_2500_;
v___y_2468_ = v___y_2501_;
v___y_2469_ = v___y_2503_;
v___y_2470_ = v___y_2502_;
v___y_2471_ = v___y_2504_;
v___y_2472_ = v___y_2505_;
v___y_2473_ = v___y_2506_;
v_val_2474_ = v_val_2509_;
goto v___jp_2465_;
}
else
{
lean_dec(v___x_2508_);
lean_dec_ref(v___f_2335_);
v___y_2452_ = v___y_2499_;
v___y_2453_ = v___y_2500_;
v___y_2454_ = v___y_2501_;
v___y_2455_ = v___y_2503_;
v___y_2456_ = v___y_2502_;
v___y_2457_ = v___y_2504_;
v___y_2458_ = v___y_2505_;
v___y_2459_ = v___y_2506_;
goto v___jp_2451_;
}
}
}
v___jp_2510_:
{
if (v_a_2521_ == 0)
{
if (lean_obj_tag(v___y_2516_) == 0)
{
if (v___y_2520_ == 0)
{
lean_dec_ref(v___y_2518_);
lean_dec_ref(v___y_2511_);
lean_dec_ref(v___f_2335_);
v___y_2404_ = v___y_2515_;
v___y_2405_ = v___y_2514_;
v___y_2406_ = v___y_2517_;
v___y_2407_ = v___y_2519_;
v___y_2408_ = v___y_2513_;
v___y_2409_ = v___y_2512_;
goto v___jp_2403_;
}
else
{
if (lean_obj_tag(v___y_2519_) == 0)
{
v___y_2499_ = v___y_2511_;
v___y_2500_ = v___y_2512_;
v___y_2501_ = v___y_2513_;
v___y_2502_ = v___y_2514_;
v___y_2503_ = v___y_2515_;
v___y_2504_ = v___y_2518_;
v___y_2505_ = v___y_2517_;
v___y_2506_ = v___y_2519_;
goto v___jp_2498_;
}
else
{
lean_object* v_val_2522_; lean_object* v___x_2523_; 
v_val_2522_ = lean_ctor_get(v___y_2519_, 0);
v___x_2523_ = l_Lean_Syntax_getTailPos_x3f(v_val_2522_, v___x_2352_);
if (lean_obj_tag(v___x_2523_) == 0)
{
v___y_2499_ = v___y_2511_;
v___y_2500_ = v___y_2512_;
v___y_2501_ = v___y_2513_;
v___y_2502_ = v___y_2514_;
v___y_2503_ = v___y_2515_;
v___y_2504_ = v___y_2518_;
v___y_2505_ = v___y_2517_;
v___y_2506_ = v___y_2519_;
goto v___jp_2498_;
}
else
{
lean_object* v_val_2524_; 
v_val_2524_ = lean_ctor_get(v___x_2523_, 0);
lean_inc(v_val_2524_);
lean_dec_ref_known(v___x_2523_, 1);
v___y_2466_ = v___y_2511_;
v___y_2467_ = v___y_2512_;
v___y_2468_ = v___y_2513_;
v___y_2469_ = v___y_2515_;
v___y_2470_ = v___y_2514_;
v___y_2471_ = v___y_2518_;
v___y_2472_ = v___y_2517_;
v___y_2473_ = v___y_2519_;
v_val_2474_ = v_val_2524_;
goto v___jp_2465_;
}
}
}
}
else
{
lean_dec_ref_known(v___y_2516_, 1);
lean_dec_ref(v___y_2518_);
lean_dec_ref(v___y_2511_);
lean_dec_ref(v___f_2335_);
v___y_2404_ = v___y_2515_;
v___y_2405_ = v___y_2514_;
v___y_2406_ = v___y_2517_;
v___y_2407_ = v___y_2519_;
v___y_2408_ = v___y_2513_;
v___y_2409_ = v___y_2512_;
goto v___jp_2403_;
}
}
else
{
lean_dec_ref(v___y_2518_);
lean_dec_ref(v___y_2511_);
lean_dec_ref(v___f_2335_);
if (lean_obj_tag(v___y_2516_) == 0)
{
v___y_2404_ = v___y_2515_;
v___y_2405_ = v___y_2514_;
v___y_2406_ = v___y_2517_;
v___y_2407_ = v___y_2519_;
v___y_2408_ = v___y_2513_;
v___y_2409_ = v___y_2512_;
goto v___jp_2403_;
}
else
{
lean_object* v___x_2525_; lean_object* v___x_2526_; 
lean_dec_ref_known(v___y_2516_, 1);
v___x_2525_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2526_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1(v___x_2525_, v___y_2513_, v___y_2512_);
if (lean_obj_tag(v___x_2526_) == 0)
{
lean_dec_ref_known(v___x_2526_, 1);
v___y_2404_ = v___y_2515_;
v___y_2405_ = v___y_2514_;
v___y_2406_ = v___y_2517_;
v___y_2407_ = v___y_2519_;
v___y_2408_ = v___y_2513_;
v___y_2409_ = v___y_2512_;
goto v___jp_2403_;
}
else
{
lean_object* v_a_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2534_; 
lean_dec(v___y_2519_);
lean_dec(v___y_2517_);
lean_dec(v___y_2515_);
lean_dec(v___y_2514_);
v_a_2527_ = lean_ctor_get(v___x_2526_, 0);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2526_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2529_ = v___x_2526_;
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_a_2527_);
lean_dec(v___x_2526_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2532_; 
if (v_isShared_2530_ == 0)
{
v___x_2532_ = v___x_2529_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_a_2527_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
}
}
}
}
v___jp_2535_:
{
lean_object* v___x_2546_; 
lean_inc_ref(v___y_2540_);
v___x_2546_ = l_Lean_Environment_find_x3f(v___y_2540_, v_declName_2340_, v___x_2336_);
if (lean_obj_tag(v___x_2546_) == 1)
{
lean_object* v_val_2547_; lean_object* v___x_2548_; 
v_val_2547_ = lean_ctor_get(v___x_2546_, 0);
lean_inc(v_val_2547_);
lean_dec_ref_known(v___x_2546_, 1);
v___x_2548_ = l_Lean_Environment_find_x3f(v___y_2540_, v___y_2542_, v___x_2336_);
if (lean_obj_tag(v___x_2548_) == 1)
{
lean_object* v_val_2549_; uint8_t v___x_2550_; uint8_t v___x_2551_; uint8_t v___x_2552_; lean_object* v___x_2553_; uint64_t v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
v_val_2549_ = lean_ctor_get(v___x_2548_, 0);
lean_inc(v_val_2549_);
lean_dec_ref_known(v___x_2548_, 1);
v___x_2550_ = 1;
v___x_2551_ = 0;
v___x_2552_ = 2;
v___x_2553_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_2553_, 0, v___x_2336_);
lean_ctor_set_uint8(v___x_2553_, 1, v___x_2336_);
lean_ctor_set_uint8(v___x_2553_, 2, v___x_2336_);
lean_ctor_set_uint8(v___x_2553_, 3, v___x_2336_);
lean_ctor_set_uint8(v___x_2553_, 4, v___x_2336_);
lean_ctor_set_uint8(v___x_2553_, 5, v___y_2543_);
lean_ctor_set_uint8(v___x_2553_, 6, v___y_2543_);
lean_ctor_set_uint8(v___x_2553_, 7, v___x_2336_);
lean_ctor_set_uint8(v___x_2553_, 8, v___y_2543_);
lean_ctor_set_uint8(v___x_2553_, 9, v___x_2550_);
lean_ctor_set_uint8(v___x_2553_, 10, v___x_2551_);
lean_ctor_set_uint8(v___x_2553_, 11, v___y_2543_);
lean_ctor_set_uint8(v___x_2553_, 12, v___y_2543_);
lean_ctor_set_uint8(v___x_2553_, 13, v___y_2543_);
lean_ctor_set_uint8(v___x_2553_, 14, v___x_2552_);
lean_ctor_set_uint8(v___x_2553_, 15, v___y_2543_);
lean_ctor_set_uint8(v___x_2553_, 16, v___y_2543_);
lean_ctor_set_uint8(v___x_2553_, 17, v___y_2543_);
lean_ctor_set_uint8(v___x_2553_, 18, v___y_2543_);
lean_ctor_set_uint8(v___x_2553_, 19, v___x_2336_);
v___x_2554_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2553_);
v___x_2555_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2555_, 0, v___x_2553_);
lean_ctor_set_uint64(v___x_2555_, sizeof(void*)*1, v___x_2554_);
v___x_2556_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_2557_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2558_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2559_ = lean_box(0);
lean_inc(v___x_2337_);
v___x_2560_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2560_, 0, v___x_2555_);
lean_ctor_set(v___x_2560_, 1, v___x_2337_);
lean_ctor_set(v___x_2560_, 2, v___x_2557_);
lean_ctor_set(v___x_2560_, 3, v___x_2558_);
lean_ctor_set(v___x_2560_, 4, v___x_2559_);
lean_ctor_set(v___x_2560_, 5, v___x_2463_);
lean_ctor_set(v___x_2560_, 6, v___x_2559_);
lean_ctor_set_uint8(v___x_2560_, sizeof(void*)*7, v___x_2336_);
lean_ctor_set_uint8(v___x_2560_, sizeof(void*)*7 + 1, v___x_2336_);
lean_ctor_set_uint8(v___x_2560_, sizeof(void*)*7 + 2, v___x_2336_);
lean_ctor_set_uint8(v___x_2560_, sizeof(void*)*7 + 3, v___x_2352_);
v___x_2561_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2562_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2563_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2564_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2564_, 0, v___x_2561_);
lean_ctor_set(v___x_2564_, 1, v___x_2562_);
lean_ctor_set(v___x_2564_, 2, v___x_2337_);
lean_ctor_set(v___x_2564_, 3, v___x_2556_);
lean_ctor_set(v___x_2564_, 4, v___x_2563_);
v___x_2565_ = lean_st_mk_ref(v___x_2564_);
v___x_2566_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq(v_val_2547_, v_val_2549_, v___x_2560_, v___x_2565_, v___y_2544_, v___y_2545_);
lean_dec_ref_known(v___x_2560_, 7);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_a_2567_; lean_object* v___x_2568_; uint8_t v___x_2569_; 
v_a_2567_ = lean_ctor_get(v___x_2566_, 0);
lean_inc(v_a_2567_);
lean_dec_ref_known(v___x_2566_, 1);
v___x_2568_ = lean_st_ref_get(v___x_2565_);
lean_dec(v___x_2565_);
lean_dec(v___x_2568_);
v___x_2569_ = lean_unbox(v_a_2567_);
lean_dec(v_a_2567_);
v___y_2511_ = v_val_2549_;
v___y_2512_ = v___y_2545_;
v___y_2513_ = v___y_2544_;
v___y_2514_ = v___y_2537_;
v___y_2515_ = v___y_2536_;
v___y_2516_ = v___y_2538_;
v___y_2517_ = v___y_2539_;
v___y_2518_ = v_val_2547_;
v___y_2519_ = v___y_2541_;
v___y_2520_ = v___y_2543_;
v_a_2521_ = v___x_2569_;
goto v___jp_2510_;
}
else
{
lean_dec(v___x_2565_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_a_2570_; uint8_t v___x_2571_; 
v_a_2570_ = lean_ctor_get(v___x_2566_, 0);
lean_inc(v_a_2570_);
lean_dec_ref_known(v___x_2566_, 1);
v___x_2571_ = lean_unbox(v_a_2570_);
lean_dec(v_a_2570_);
v___y_2511_ = v_val_2549_;
v___y_2512_ = v___y_2545_;
v___y_2513_ = v___y_2544_;
v___y_2514_ = v___y_2537_;
v___y_2515_ = v___y_2536_;
v___y_2516_ = v___y_2538_;
v___y_2517_ = v___y_2539_;
v___y_2518_ = v_val_2547_;
v___y_2519_ = v___y_2541_;
v___y_2520_ = v___y_2543_;
v_a_2521_ = v___x_2571_;
goto v___jp_2510_;
}
else
{
lean_object* v_a_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2579_; 
lean_dec(v_val_2549_);
lean_dec(v_val_2547_);
lean_dec(v___y_2541_);
lean_dec(v___y_2539_);
lean_dec(v___y_2538_);
lean_dec(v___y_2537_);
lean_dec(v___y_2536_);
lean_dec_ref(v___f_2335_);
v_a_2572_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2574_ = v___x_2566_;
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_a_2572_);
lean_dec(v___x_2566_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2577_; 
if (v_isShared_2575_ == 0)
{
v___x_2577_ = v___x_2574_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_a_2572_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
}
}
else
{
lean_dec(v___x_2548_);
lean_dec(v_val_2547_);
lean_dec(v___y_2538_);
lean_dec(v___x_2337_);
lean_dec_ref(v___f_2335_);
v___y_2404_ = v___y_2536_;
v___y_2405_ = v___y_2537_;
v___y_2406_ = v___y_2539_;
v___y_2407_ = v___y_2541_;
v___y_2408_ = v___y_2544_;
v___y_2409_ = v___y_2545_;
goto v___jp_2403_;
}
}
else
{
lean_dec(v___x_2546_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2540_);
lean_dec(v___y_2538_);
lean_dec(v___x_2337_);
lean_dec_ref(v___f_2335_);
v___y_2404_ = v___y_2536_;
v___y_2405_ = v___y_2537_;
v___y_2406_ = v___y_2539_;
v___y_2407_ = v___y_2541_;
v___y_2408_ = v___y_2544_;
v___y_2409_ = v___y_2545_;
goto v___jp_2403_;
}
}
v___jp_2580_:
{
lean_object* v___x_2592_; 
v___x_2592_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1(v_msg_2589_, v___y_2590_, v___y_2591_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_dec_ref_known(v___x_2592_, 1);
v___y_2536_ = v___y_2582_;
v___y_2537_ = v___y_2581_;
v___y_2538_ = v___y_2585_;
v___y_2539_ = v___y_2584_;
v___y_2540_ = v___y_2583_;
v___y_2541_ = v___y_2587_;
v___y_2542_ = v___y_2586_;
v___y_2543_ = v___y_2588_;
v___y_2544_ = v___y_2590_;
v___y_2545_ = v___y_2591_;
goto v___jp_2535_;
}
else
{
lean_object* v_a_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2600_; 
lean_dec(v___y_2587_);
lean_dec(v___y_2586_);
lean_dec(v___y_2585_);
lean_dec(v___y_2584_);
lean_dec_ref(v___y_2583_);
lean_dec(v___y_2582_);
lean_dec(v___y_2581_);
lean_dec(v_declName_2340_);
lean_dec(v___x_2337_);
lean_dec_ref(v___f_2335_);
v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2600_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2595_ = v___x_2592_;
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_a_2593_);
lean_dec(v___x_2592_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2598_; 
if (v_isShared_2596_ == 0)
{
v___x_2598_ = v___x_2595_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_a_2593_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
}
}
v___jp_2601_:
{
if (lean_obj_tag(v_a_2615_) == 1)
{
lean_object* v_val_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2646_; 
v_val_2616_ = lean_ctor_get(v_a_2615_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v_a_2615_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2618_ = v_a_2615_;
v_isShared_2619_ = v_isSharedCheck_2646_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_val_2616_);
lean_dec(v_a_2615_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2646_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; uint8_t v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2633_; 
v___x_2620_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__37_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__37_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__37_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2621_, 0, v___x_2620_);
lean_ctor_set(v___x_2621_, 1, v___y_2606_);
v___x_2622_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__39_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__39_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__39_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2621_);
lean_ctor_set(v___x_2623_, 1, v___x_2622_);
v___x_2624_ = l_Lean_Name_toString(v_val_2616_, v___x_2352_);
v___x_2625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2625_, 0, v___x_2624_);
v___x_2626_ = lean_box(0);
v___x_2627_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2625_);
lean_ctor_set(v___x_2627_, 1, v___x_2626_);
lean_ctor_set(v___x_2627_, 2, v___x_2626_);
lean_ctor_set(v___x_2627_, 3, v___x_2626_);
lean_ctor_set(v___x_2627_, 4, v___x_2626_);
lean_ctor_set(v___x_2627_, 5, v___x_2626_);
v___x_2628_ = 0;
v___x_2629_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2629_, 0, v___x_2627_);
lean_ctor_set(v___x_2629_, 1, v___x_2626_);
lean_ctor_set(v___x_2629_, 2, v___x_2626_);
lean_ctor_set_uint8(v___x_2629_, sizeof(void*)*3, v___x_2628_);
v___x_2630_ = lean_mk_empty_array_with_capacity(v___x_2464_);
v___x_2631_ = lean_array_push(v___x_2630_, v___x_2629_);
if (v_isShared_2619_ == 0)
{
lean_ctor_set(v___x_2618_, 0, v___y_2603_);
v___x_2633_ = v___x_2618_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v___y_2603_);
v___x_2633_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
lean_object* v___x_2634_; 
v___x_2634_ = l_Lean_MessageData_hint(v___x_2623_, v___x_2631_, v___x_2633_, v___x_2626_, v___x_2336_, v___y_2612_, v___y_2614_);
lean_dec_ref(v___x_2631_);
if (lean_obj_tag(v___x_2634_) == 0)
{
lean_object* v_a_2635_; lean_object* v___x_2636_; 
v_a_2635_ = lean_ctor_get(v___x_2634_, 0);
lean_inc(v_a_2635_);
lean_dec_ref_known(v___x_2634_, 1);
v___x_2636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2636_, 0, v___y_2602_);
lean_ctor_set(v___x_2636_, 1, v_a_2635_);
v___y_2581_ = v___y_2604_;
v___y_2582_ = v___y_2605_;
v___y_2583_ = v___y_2609_;
v___y_2584_ = v___y_2610_;
v___y_2585_ = v___y_2611_;
v___y_2586_ = v___y_2607_;
v___y_2587_ = v___y_2613_;
v___y_2588_ = v___y_2608_;
v_msg_2589_ = v___x_2636_;
v___y_2590_ = v___y_2612_;
v___y_2591_ = v___y_2614_;
goto v___jp_2580_;
}
else
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2644_; 
lean_dec(v___y_2613_);
lean_dec(v___y_2611_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2607_);
lean_dec(v___y_2605_);
lean_dec(v___y_2604_);
lean_dec_ref(v___y_2602_);
lean_dec(v_declName_2340_);
lean_dec(v___x_2337_);
lean_dec_ref(v___f_2335_);
v_a_2637_ = lean_ctor_get(v___x_2634_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2634_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2639_ = v___x_2634_;
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___x_2634_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2642_; 
if (v_isShared_2640_ == 0)
{
v___x_2642_ = v___x_2639_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_a_2637_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2615_);
lean_dec_ref(v___y_2606_);
lean_dec(v___y_2603_);
v___y_2581_ = v___y_2604_;
v___y_2582_ = v___y_2605_;
v___y_2583_ = v___y_2609_;
v___y_2584_ = v___y_2610_;
v___y_2585_ = v___y_2611_;
v___y_2586_ = v___y_2607_;
v___y_2587_ = v___y_2613_;
v___y_2588_ = v___y_2608_;
v_msg_2589_ = v___y_2602_;
v___y_2590_ = v___y_2612_;
v___y_2591_ = v___y_2614_;
goto v___jp_2580_;
}
}
v___jp_2647_:
{
if (lean_obj_tag(v___y_2649_) == 1)
{
lean_object* v_val_2655_; lean_object* v___x_2656_; 
v_val_2655_ = lean_ctor_get(v___y_2649_, 0);
lean_inc(v_val_2655_);
v___x_2656_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2(v_val_2655_, v___x_2336_, v___y_2653_, v___y_2654_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v___x_2657_; lean_object* v_a_2658_; lean_object* v___x_2659_; uint8_t v___x_2660_; 
lean_dec_ref_known(v___x_2656_, 1);
v___x_2657_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3(v___y_2653_, v___y_2654_);
v_a_2658_ = lean_ctor_get(v___x_2657_, 0);
lean_inc(v_a_2658_);
lean_dec_ref(v___x_2657_);
v___x_2659_ = l_Lean_Linter_linter_deprecated;
v___x_2660_ = l_Lean_Linter_getLinterValue(v___x_2659_, v_a_2658_);
lean_dec(v_a_2658_);
if (v___x_2660_ == 0)
{
lean_dec(v___y_2650_);
lean_dec(v_declName_2340_);
lean_dec_ref(v___x_2338_);
lean_dec(v___x_2337_);
lean_dec_ref(v___f_2335_);
v___y_2404_ = v___y_2649_;
v___y_2405_ = v___y_2648_;
v___y_2406_ = v___y_2651_;
v___y_2407_ = v___y_2652_;
v___y_2408_ = v___y_2653_;
v___y_2409_ = v___y_2654_;
goto v___jp_2403_;
}
else
{
lean_object* v___x_2661_; lean_object* v_env_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; uint8_t v___x_2665_; 
lean_inc(v_val_2655_);
v___x_2661_ = lean_st_ref_get(v___y_2654_);
v_env_2662_ = lean_ctor_get(v___x_2661_, 0);
lean_inc_ref(v_env_2662_);
lean_dec(v___x_2661_);
v___x_2663_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2653_);
v___x_2664_ = l_Lean_Linter_linter_deprecated_deprecatedTarget;
v___x_2665_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__4(v___x_2663_, v___x_2664_);
lean_dec_ref(v___x_2663_);
if (v___x_2665_ == 0)
{
lean_dec_ref(v___x_2338_);
v___y_2536_ = v___y_2649_;
v___y_2537_ = v___y_2648_;
v___y_2538_ = v___y_2650_;
v___y_2539_ = v___y_2651_;
v___y_2540_ = v_env_2662_;
v___y_2541_ = v___y_2652_;
v___y_2542_ = v_val_2655_;
v___y_2543_ = v___x_2660_;
v___y_2544_ = v___y_2653_;
v___y_2545_ = v___y_2654_;
goto v___jp_2535_;
}
else
{
lean_object* v___x_2666_; 
lean_inc(v_val_2655_);
lean_inc_ref(v_env_2662_);
v___x_2666_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v___x_2338_, v_a_2339_, v___x_2336_, v_env_2662_, v_val_2655_);
if (lean_obj_tag(v___x_2666_) == 1)
{
lean_object* v_val_2667_; lean_object* v_name_2668_; lean_object* v_newName_x3f_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; 
v_val_2667_ = lean_ctor_get(v___x_2666_, 0);
lean_inc(v_val_2667_);
lean_dec_ref_known(v___x_2666_, 1);
v_name_2668_ = lean_ctor_get(v___x_2664_, 0);
v_newName_x3f_2669_ = lean_ctor_get(v_val_2667_, 0);
lean_inc(v_newName_x3f_2669_);
lean_dec(v_val_2667_);
v___x_2670_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
lean_inc(v_name_2668_);
v___x_2671_ = l_Lean_MessageData_ofName(v_name_2668_);
v___x_2672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2672_, 0, v___x_2670_);
lean_ctor_set(v___x_2672_, 1, v___x_2671_);
v___x_2673_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2672_);
lean_ctor_set(v___x_2674_, 1, v___x_2673_);
v___x_2675_ = l_Lean_MessageData_note(v___x_2674_);
if (lean_obj_tag(v_newName_x3f_2669_) == 0)
{
lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___x_2676_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
lean_inc(v_val_2655_);
v___x_2677_ = l_Lean_MessageData_ofConstName(v_val_2655_, v___x_2352_);
v___x_2678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2678_, 0, v___x_2676_);
lean_ctor_set(v___x_2678_, 1, v___x_2677_);
v___x_2679_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__47_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__47_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__47_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2680_, 0, v___x_2678_);
lean_ctor_set(v___x_2680_, 1, v___x_2679_);
lean_inc(v_declName_2340_);
v___x_2681_ = l_Lean_MessageData_ofConstName(v_declName_2340_, v___x_2352_);
v___x_2682_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2682_, 0, v___x_2680_);
lean_ctor_set(v___x_2682_, 1, v___x_2681_);
v___x_2683_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__49_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__49_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__49_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2682_);
lean_ctor_set(v___x_2684_, 1, v___x_2683_);
v___x_2685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2684_);
lean_ctor_set(v___x_2685_, 1, v___x_2675_);
v___x_2686_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1(v___x_2685_, v___y_2653_, v___y_2654_);
if (lean_obj_tag(v___x_2686_) == 0)
{
lean_dec_ref_known(v___x_2686_, 1);
v___y_2536_ = v___y_2649_;
v___y_2537_ = v___y_2648_;
v___y_2538_ = v___y_2650_;
v___y_2539_ = v___y_2651_;
v___y_2540_ = v_env_2662_;
v___y_2541_ = v___y_2652_;
v___y_2542_ = v_val_2655_;
v___y_2543_ = v___x_2660_;
v___y_2544_ = v___y_2653_;
v___y_2545_ = v___y_2654_;
goto v___jp_2535_;
}
else
{
lean_object* v_a_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2694_; 
lean_dec_ref(v_env_2662_);
lean_dec(v_val_2655_);
lean_dec_ref_known(v___y_2649_, 1);
lean_dec(v___y_2652_);
lean_dec(v___y_2651_);
lean_dec(v___y_2650_);
lean_dec(v___y_2648_);
lean_dec(v_declName_2340_);
lean_dec(v___x_2337_);
lean_dec_ref(v___f_2335_);
v_a_2687_ = lean_ctor_get(v___x_2686_, 0);
v_isSharedCheck_2694_ = !lean_is_exclusive(v___x_2686_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2689_ = v___x_2686_;
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_a_2687_);
lean_dec(v___x_2686_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v___x_2692_; 
if (v_isShared_2690_ == 0)
{
v___x_2692_ = v___x_2689_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v_a_2687_);
v___x_2692_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
return v___x_2692_;
}
}
}
}
else
{
lean_object* v_val_2695_; uint8_t v___x_2696_; 
v_val_2695_ = lean_ctor_get(v_newName_x3f_2669_, 0);
lean_inc(v_val_2695_);
lean_dec_ref_known(v_newName_x3f_2669_, 1);
v___x_2696_ = lean_name_eq(v_val_2695_, v_val_2655_);
if (v___x_2696_ == 0)
{
if (v___x_2665_ == 0)
{
lean_dec(v_val_2695_);
lean_dec_ref(v___x_2675_);
v___y_2536_ = v___y_2649_;
v___y_2537_ = v___y_2648_;
v___y_2538_ = v___y_2650_;
v___y_2539_ = v___y_2651_;
v___y_2540_ = v_env_2662_;
v___y_2541_ = v___y_2652_;
v___y_2542_ = v_val_2655_;
v___y_2543_ = v___x_2660_;
v___y_2544_ = v___y_2653_;
v___y_2545_ = v___y_2654_;
goto v___jp_2535_;
}
else
{
lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; 
v___x_2697_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
lean_inc(v_val_2655_);
v___x_2698_ = l_Lean_MessageData_ofConstName(v_val_2655_, v___x_2352_);
v___x_2699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2699_, 0, v___x_2697_);
lean_ctor_set(v___x_2699_, 1, v___x_2698_);
v___x_2700_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__51_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__51_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__51_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2699_);
lean_ctor_set(v___x_2701_, 1, v___x_2700_);
lean_inc(v_val_2695_);
v___x_2702_ = l_Lean_MessageData_ofConstName(v_val_2695_, v___x_2352_);
lean_inc_ref_n(v___x_2702_, 2);
v___x_2703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2701_);
lean_ctor_set(v___x_2703_, 1, v___x_2702_);
v___x_2704_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__53_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__53_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__53_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2703_);
lean_ctor_set(v___x_2705_, 1, v___x_2704_);
lean_inc(v_declName_2340_);
v___x_2706_ = l_Lean_MessageData_ofConstName(v_declName_2340_, v___x_2352_);
v___x_2707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2707_, 0, v___x_2705_);
lean_ctor_set(v___x_2707_, 1, v___x_2706_);
v___x_2708_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__55_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__55_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__55_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2707_);
lean_ctor_set(v___x_2709_, 1, v___x_2708_);
v___x_2710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2710_, 0, v___x_2709_);
lean_ctor_set(v___x_2710_, 1, v___x_2702_);
v___x_2711_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__57_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__57_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__57_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2712_, 0, v___x_2710_);
lean_ctor_set(v___x_2712_, 1, v___x_2711_);
v___x_2713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2713_, 0, v___x_2712_);
lean_ctor_set(v___x_2713_, 1, v___x_2675_);
if (lean_obj_tag(v___y_2651_) == 1)
{
lean_object* v_val_2714_; lean_object* v___x_2715_; 
v_val_2714_ = lean_ctor_get(v___y_2651_, 0);
v___x_2715_ = l_Lean_Syntax_getRange_x3f(v_val_2714_, v___x_2352_);
if (lean_obj_tag(v___x_2715_) == 0)
{
lean_dec_ref(v___x_2702_);
lean_dec(v_val_2695_);
v___y_2581_ = v___y_2648_;
v___y_2582_ = v___y_2649_;
v___y_2583_ = v_env_2662_;
v___y_2584_ = v___y_2651_;
v___y_2585_ = v___y_2650_;
v___y_2586_ = v_val_2655_;
v___y_2587_ = v___y_2652_;
v___y_2588_ = v___x_2660_;
v_msg_2589_ = v___x_2713_;
v___y_2590_ = v___y_2653_;
v___y_2591_ = v___y_2654_;
goto v___jp_2580_;
}
else
{
uint8_t v___x_2716_; uint8_t v___x_2717_; uint8_t v___x_2718_; lean_object* v___x_2719_; uint64_t v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; 
lean_inc(v_val_2714_);
lean_dec_ref_known(v___x_2715_, 1);
v___x_2716_ = 1;
v___x_2717_ = 0;
v___x_2718_ = 2;
v___x_2719_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_2719_, 0, v___x_2696_);
lean_ctor_set_uint8(v___x_2719_, 1, v___x_2696_);
lean_ctor_set_uint8(v___x_2719_, 2, v___x_2696_);
lean_ctor_set_uint8(v___x_2719_, 3, v___x_2696_);
lean_ctor_set_uint8(v___x_2719_, 4, v___x_2696_);
lean_ctor_set_uint8(v___x_2719_, 5, v___x_2665_);
lean_ctor_set_uint8(v___x_2719_, 6, v___x_2665_);
lean_ctor_set_uint8(v___x_2719_, 7, v___x_2696_);
lean_ctor_set_uint8(v___x_2719_, 8, v___x_2665_);
lean_ctor_set_uint8(v___x_2719_, 9, v___x_2716_);
lean_ctor_set_uint8(v___x_2719_, 10, v___x_2717_);
lean_ctor_set_uint8(v___x_2719_, 11, v___x_2665_);
lean_ctor_set_uint8(v___x_2719_, 12, v___x_2665_);
lean_ctor_set_uint8(v___x_2719_, 13, v___x_2665_);
lean_ctor_set_uint8(v___x_2719_, 14, v___x_2718_);
lean_ctor_set_uint8(v___x_2719_, 15, v___x_2665_);
lean_ctor_set_uint8(v___x_2719_, 16, v___x_2665_);
lean_ctor_set_uint8(v___x_2719_, 17, v___x_2665_);
lean_ctor_set_uint8(v___x_2719_, 18, v___x_2665_);
lean_ctor_set_uint8(v___x_2719_, 19, v___x_2696_);
v___x_2720_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2719_);
v___x_2721_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2721_, 0, v___x_2719_);
lean_ctor_set_uint64(v___x_2721_, sizeof(void*)*1, v___x_2720_);
v___x_2722_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_2723_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2724_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2725_ = lean_box(0);
lean_inc_n(v___x_2337_, 2);
v___x_2726_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2726_, 0, v___x_2721_);
lean_ctor_set(v___x_2726_, 1, v___x_2337_);
lean_ctor_set(v___x_2726_, 2, v___x_2723_);
lean_ctor_set(v___x_2726_, 3, v___x_2724_);
lean_ctor_set(v___x_2726_, 4, v___x_2725_);
lean_ctor_set(v___x_2726_, 5, v___x_2463_);
lean_ctor_set(v___x_2726_, 6, v___x_2725_);
lean_ctor_set_uint8(v___x_2726_, sizeof(void*)*7, v___x_2336_);
lean_ctor_set_uint8(v___x_2726_, sizeof(void*)*7 + 1, v___x_2336_);
lean_ctor_set_uint8(v___x_2726_, sizeof(void*)*7 + 2, v___x_2336_);
lean_ctor_set_uint8(v___x_2726_, sizeof(void*)*7 + 3, v___x_2352_);
v___x_2727_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2728_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2729_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2730_, 0, v___x_2727_);
lean_ctor_set(v___x_2730_, 1, v___x_2728_);
lean_ctor_set(v___x_2730_, 2, v___x_2337_);
lean_ctor_set(v___x_2730_, 3, v___x_2722_);
lean_ctor_set(v___x_2730_, 4, v___x_2729_);
v___x_2731_ = lean_st_mk_ref(v___x_2730_);
v___x_2732_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5(v_val_2695_, v___x_2336_, v___x_2726_, v___x_2731_, v___y_2653_, v___y_2654_);
lean_dec_ref_known(v___x_2726_, 7);
if (lean_obj_tag(v___x_2732_) == 0)
{
lean_object* v_a_2733_; lean_object* v___x_2734_; 
v_a_2733_ = lean_ctor_get(v___x_2732_, 0);
lean_inc(v_a_2733_);
lean_dec_ref_known(v___x_2732_, 1);
v___x_2734_ = lean_st_ref_get(v___x_2731_);
lean_dec(v___x_2731_);
lean_dec(v___x_2734_);
v___y_2602_ = v___x_2713_;
v___y_2603_ = v_val_2714_;
v___y_2604_ = v___y_2648_;
v___y_2605_ = v___y_2649_;
v___y_2606_ = v___x_2702_;
v___y_2607_ = v_val_2655_;
v___y_2608_ = v___x_2660_;
v___y_2609_ = v_env_2662_;
v___y_2610_ = v___y_2651_;
v___y_2611_ = v___y_2650_;
v___y_2612_ = v___y_2653_;
v___y_2613_ = v___y_2652_;
v___y_2614_ = v___y_2654_;
v_a_2615_ = v_a_2733_;
goto v___jp_2601_;
}
else
{
lean_dec(v___x_2731_);
if (lean_obj_tag(v___x_2732_) == 0)
{
lean_object* v_a_2735_; 
v_a_2735_ = lean_ctor_get(v___x_2732_, 0);
lean_inc(v_a_2735_);
lean_dec_ref_known(v___x_2732_, 1);
v___y_2602_ = v___x_2713_;
v___y_2603_ = v_val_2714_;
v___y_2604_ = v___y_2648_;
v___y_2605_ = v___y_2649_;
v___y_2606_ = v___x_2702_;
v___y_2607_ = v_val_2655_;
v___y_2608_ = v___x_2660_;
v___y_2609_ = v_env_2662_;
v___y_2610_ = v___y_2651_;
v___y_2611_ = v___y_2650_;
v___y_2612_ = v___y_2653_;
v___y_2613_ = v___y_2652_;
v___y_2614_ = v___y_2654_;
v_a_2615_ = v_a_2735_;
goto v___jp_2601_;
}
else
{
lean_object* v_a_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2743_; 
lean_dec(v_val_2714_);
lean_dec_ref_known(v___y_2651_, 1);
lean_dec_ref_known(v___x_2713_, 2);
lean_dec_ref(v___x_2702_);
lean_dec_ref(v_env_2662_);
lean_dec_ref_known(v___y_2649_, 1);
lean_dec(v_val_2655_);
lean_dec(v___y_2652_);
lean_dec(v___y_2650_);
lean_dec(v___y_2648_);
lean_dec(v_declName_2340_);
lean_dec(v___x_2337_);
lean_dec_ref(v___f_2335_);
v_a_2736_ = lean_ctor_get(v___x_2732_, 0);
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2732_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2738_ = v___x_2732_;
v_isShared_2739_ = v_isSharedCheck_2743_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_a_2736_);
lean_dec(v___x_2732_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2743_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
lean_object* v___x_2741_; 
if (v_isShared_2739_ == 0)
{
v___x_2741_ = v___x_2738_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v_a_2736_);
v___x_2741_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
return v___x_2741_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_2702_);
lean_dec(v_val_2695_);
v___y_2581_ = v___y_2648_;
v___y_2582_ = v___y_2649_;
v___y_2583_ = v_env_2662_;
v___y_2584_ = v___y_2651_;
v___y_2585_ = v___y_2650_;
v___y_2586_ = v_val_2655_;
v___y_2587_ = v___y_2652_;
v___y_2588_ = v___x_2660_;
v_msg_2589_ = v___x_2713_;
v___y_2590_ = v___y_2653_;
v___y_2591_ = v___y_2654_;
goto v___jp_2580_;
}
}
}
else
{
lean_dec(v_val_2695_);
lean_dec_ref(v___x_2675_);
v___y_2536_ = v___y_2649_;
v___y_2537_ = v___y_2648_;
v___y_2538_ = v___y_2650_;
v___y_2539_ = v___y_2651_;
v___y_2540_ = v_env_2662_;
v___y_2541_ = v___y_2652_;
v___y_2542_ = v_val_2655_;
v___y_2543_ = v___x_2660_;
v___y_2544_ = v___y_2653_;
v___y_2545_ = v___y_2654_;
goto v___jp_2535_;
}
}
}
else
{
lean_dec(v___x_2666_);
v___y_2536_ = v___y_2649_;
v___y_2537_ = v___y_2648_;
v___y_2538_ = v___y_2650_;
v___y_2539_ = v___y_2651_;
v___y_2540_ = v_env_2662_;
v___y_2541_ = v___y_2652_;
v___y_2542_ = v_val_2655_;
v___y_2543_ = v___x_2660_;
v___y_2544_ = v___y_2653_;
v___y_2545_ = v___y_2654_;
goto v___jp_2535_;
}
}
}
}
else
{
lean_object* v_a_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2751_; 
lean_dec_ref_known(v___y_2649_, 1);
lean_dec(v___y_2652_);
lean_dec(v___y_2651_);
lean_dec(v___y_2650_);
lean_dec(v___y_2648_);
lean_dec(v_declName_2340_);
lean_dec_ref(v___x_2338_);
lean_dec(v___x_2337_);
lean_dec_ref(v___f_2335_);
v_a_2744_ = lean_ctor_get(v___x_2656_, 0);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2746_ = v___x_2656_;
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_a_2744_);
lean_dec(v___x_2656_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2749_; 
if (v_isShared_2747_ == 0)
{
v___x_2749_ = v___x_2746_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_a_2744_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
}
}
else
{
lean_dec(v___y_2650_);
lean_dec(v_declName_2340_);
lean_dec_ref(v___x_2338_);
lean_dec(v___x_2337_);
lean_dec_ref(v___f_2335_);
v___y_2404_ = v___y_2649_;
v___y_2405_ = v___y_2648_;
v___y_2406_ = v___y_2651_;
v___y_2407_ = v___y_2652_;
v___y_2408_ = v___y_2653_;
v___y_2409_ = v___y_2654_;
goto v___jp_2403_;
}
}
v___jp_2752_:
{
lean_object* v___x_2760_; uint8_t v___x_2761_; 
lean_inc(v_declName_2340_);
v___x_2760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2760_, 0, v_declName_2340_);
v___x_2761_ = l_Option_instBEq_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__6(v_a_2759_, v___x_2760_);
lean_dec_ref_known(v___x_2760_, 1);
if (v___x_2761_ == 0)
{
v___y_2648_ = v___y_2755_;
v___y_2649_ = v_a_2759_;
v___y_2650_ = v___y_2756_;
v___y_2651_ = v___y_2757_;
v___y_2652_ = v___y_2758_;
v___y_2653_ = v___y_2754_;
v___y_2654_ = v___y_2753_;
goto v___jp_2647_;
}
else
{
lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v_a_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2775_; 
lean_dec(v_a_2759_);
lean_dec(v___y_2758_);
lean_dec(v___y_2757_);
lean_dec(v___y_2756_);
lean_dec(v___y_2755_);
lean_dec_ref(v___x_2338_);
lean_dec(v___x_2337_);
lean_dec_ref(v___f_2335_);
v___x_2762_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__59_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__59_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__59_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2763_ = l_Lean_MessageData_ofConstName(v_declName_2340_, v___x_2352_);
v___x_2764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2764_, 0, v___x_2762_);
lean_ctor_set(v___x_2764_, 1, v___x_2763_);
v___x_2765_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__61_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__61_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__61_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2766_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2766_, 0, v___x_2764_);
lean_ctor_set(v___x_2766_, 1, v___x_2765_);
v___x_2767_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___redArg(v___x_2766_, v___y_2754_, v___y_2753_);
v_a_2768_ = lean_ctor_get(v___x_2767_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2767_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2770_ = v___x_2767_;
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_a_2768_);
lean_dec(v___x_2767_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2773_; 
if (v_isShared_2771_ == 0)
{
v___x_2773_ = v___x_2770_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_a_2768_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
}
}
v___jp_2776_:
{
if (lean_obj_tag(v___y_2777_) == 0)
{
lean_object* v___x_2783_; 
v___x_2783_ = lean_box(0);
v___y_2753_ = v___y_2782_;
v___y_2754_ = v___y_2781_;
v___y_2755_ = v_since_x3f_2780_;
v___y_2756_ = v___y_2778_;
v___y_2757_ = v___y_2777_;
v___y_2758_ = v___y_2779_;
v_a_2759_ = v___x_2783_;
goto v___jp_2752_;
}
else
{
lean_object* v_val_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; 
v_val_2784_ = lean_ctor_get(v___y_2777_, 0);
v___x_2785_ = lean_box(0);
lean_inc(v_val_2784_);
v___x_2786_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_val_2784_, v___x_2785_, v___y_2781_, v___y_2782_);
if (lean_obj_tag(v___x_2786_) == 0)
{
lean_object* v_a_2787_; lean_object* v___x_2788_; 
v_a_2787_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_a_2787_);
lean_dec_ref_known(v___x_2786_, 1);
v___x_2788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2788_, 0, v_a_2787_);
v___y_2753_ = v___y_2782_;
v___y_2754_ = v___y_2781_;
v___y_2755_ = v_since_x3f_2780_;
v___y_2756_ = v___y_2778_;
v___y_2757_ = v___y_2777_;
v___y_2758_ = v___y_2779_;
v_a_2759_ = v___x_2788_;
goto v___jp_2752_;
}
else
{
lean_object* v_a_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2796_; 
lean_dec_ref_known(v___y_2777_, 1);
lean_dec(v_since_x3f_2780_);
lean_dec(v___y_2779_);
lean_dec(v___y_2778_);
lean_dec(v_declName_2340_);
lean_dec_ref(v___x_2338_);
lean_dec(v___x_2337_);
lean_dec_ref(v___f_2335_);
v_a_2789_ = lean_ctor_get(v___x_2786_, 0);
v_isSharedCheck_2796_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2791_ = v___x_2786_;
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_a_2789_);
lean_dec(v___x_2786_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2794_; 
if (v_isShared_2792_ == 0)
{
v___x_2794_ = v___x_2791_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_a_2789_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
return v___x_2794_;
}
}
}
}
}
v___jp_2797_:
{
lean_object* v___x_2804_; lean_object* v___x_2805_; uint8_t v___x_2806_; 
v___x_2804_ = lean_unsigned_to_nat(4u);
v___x_2805_ = l_Lean_Syntax_getArg(v_stx_2341_, v___x_2804_);
lean_dec(v_stx_2341_);
v___x_2806_ = l_Lean_Syntax_isNone(v___x_2805_);
if (v___x_2806_ == 0)
{
lean_object* v___x_2807_; uint8_t v___x_2808_; 
v___x_2807_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_2805_);
v___x_2808_ = l_Lean_Syntax_matchesNull(v___x_2805_, v___x_2807_);
if (v___x_2808_ == 0)
{
lean_object* v___x_2809_; lean_object* v___x_2810_; 
lean_dec(v___x_2805_);
lean_dec(v_typeChanged_x3f_2801_);
lean_dec(v___y_2800_);
lean_dec(v___y_2799_);
lean_dec(v_declName_2340_);
lean_dec_ref(v___x_2338_);
lean_dec(v___x_2337_);
lean_dec_ref(v___f_2335_);
v___x_2809_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2810_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___redArg(v___x_2809_, v___y_2802_, v___y_2803_);
return v___x_2810_;
}
else
{
lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2811_ = l_Lean_Syntax_getArg(v___x_2805_, v___y_2798_);
lean_dec(v___x_2805_);
v___x_2812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2812_, 0, v___x_2811_);
v___y_2777_ = v___y_2799_;
v___y_2778_ = v_typeChanged_x3f_2801_;
v___y_2779_ = v___y_2800_;
v_since_x3f_2780_ = v___x_2812_;
v___y_2781_ = v___y_2802_;
v___y_2782_ = v___y_2803_;
goto v___jp_2776_;
}
}
else
{
lean_object* v___x_2813_; 
lean_dec(v___x_2805_);
v___x_2813_ = lean_box(0);
v___y_2777_ = v___y_2799_;
v___y_2778_ = v_typeChanged_x3f_2801_;
v___y_2779_ = v___y_2800_;
v_since_x3f_2780_ = v___x_2813_;
v___y_2781_ = v___y_2802_;
v___y_2782_ = v___y_2803_;
goto v___jp_2776_;
}
}
v___jp_2814_:
{
lean_object* v___x_2819_; lean_object* v___x_2820_; uint8_t v___x_2821_; 
v___x_2819_ = lean_unsigned_to_nat(3u);
v___x_2820_ = l_Lean_Syntax_getArg(v_stx_2341_, v___x_2819_);
v___x_2821_ = l_Lean_Syntax_isNone(v___x_2820_);
if (v___x_2821_ == 0)
{
uint8_t v___x_2822_; 
lean_inc(v___x_2820_);
v___x_2822_ = l_Lean_Syntax_matchesNull(v___x_2820_, v___x_2464_);
if (v___x_2822_ == 0)
{
lean_object* v___x_2823_; lean_object* v___x_2824_; 
lean_dec(v___x_2820_);
lean_dec(v_text_x3f_2816_);
lean_dec(v___y_2815_);
lean_dec(v_stx_2341_);
lean_dec(v_declName_2340_);
lean_dec_ref(v___x_2338_);
lean_dec(v___x_2337_);
lean_dec_ref(v___f_2335_);
v___x_2823_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2824_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___redArg(v___x_2823_, v___y_2817_, v___y_2818_);
return v___x_2824_;
}
else
{
lean_object* v___x_2825_; lean_object* v___x_2826_; 
v___x_2825_ = l_Lean_Syntax_getArg(v___x_2820_, v___x_2463_);
lean_dec(v___x_2820_);
v___x_2826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2825_);
v___y_2798_ = v___x_2819_;
v___y_2799_ = v___y_2815_;
v___y_2800_ = v_text_x3f_2816_;
v_typeChanged_x3f_2801_ = v___x_2826_;
v___y_2802_ = v___y_2817_;
v___y_2803_ = v___y_2818_;
goto v___jp_2797_;
}
}
else
{
lean_object* v___x_2827_; 
lean_dec(v___x_2820_);
v___x_2827_ = lean_box(0);
v___y_2798_ = v___x_2819_;
v___y_2799_ = v___y_2815_;
v___y_2800_ = v_text_x3f_2816_;
v_typeChanged_x3f_2801_ = v___x_2827_;
v___y_2802_ = v___y_2817_;
v___y_2803_ = v___y_2818_;
goto v___jp_2797_;
}
}
v___jp_2828_:
{
lean_object* v___x_2832_; lean_object* v___x_2833_; uint8_t v___x_2834_; 
v___x_2832_ = lean_unsigned_to_nat(2u);
v___x_2833_ = l_Lean_Syntax_getArg(v_stx_2341_, v___x_2832_);
v___x_2834_ = l_Lean_Syntax_isNone(v___x_2833_);
if (v___x_2834_ == 0)
{
uint8_t v___x_2835_; 
lean_inc(v___x_2833_);
v___x_2835_ = l_Lean_Syntax_matchesNull(v___x_2833_, v___x_2464_);
if (v___x_2835_ == 0)
{
lean_object* v___x_2836_; lean_object* v___x_2837_; 
lean_dec(v___x_2833_);
lean_dec(v_id_x3f_2829_);
lean_dec(v_stx_2341_);
lean_dec(v_declName_2340_);
lean_dec_ref(v___x_2338_);
lean_dec(v___x_2337_);
lean_dec_ref(v___f_2335_);
v___x_2836_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2837_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___redArg(v___x_2836_, v___y_2830_, v___y_2831_);
return v___x_2837_;
}
else
{
lean_object* v___x_2838_; lean_object* v___x_2839_; 
v___x_2838_ = l_Lean_Syntax_getArg(v___x_2833_, v___x_2463_);
lean_dec(v___x_2833_);
v___x_2839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2839_, 0, v___x_2838_);
v___y_2815_ = v_id_x3f_2829_;
v_text_x3f_2816_ = v___x_2839_;
v___y_2817_ = v___y_2830_;
v___y_2818_ = v___y_2831_;
goto v___jp_2814_;
}
}
else
{
lean_object* v___x_2840_; 
lean_dec(v___x_2833_);
v___x_2840_ = lean_box(0);
v___y_2815_ = v_id_x3f_2829_;
v_text_x3f_2816_ = v___x_2840_;
v___y_2817_ = v___y_2830_;
v___y_2818_ = v___y_2831_;
goto v___jp_2814_;
}
}
}
v___jp_2345_:
{
lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___x_2349_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2349_, 0, v___y_2348_);
lean_ctor_set(v___x_2349_, 1, v___y_2347_);
lean_ctor_set(v___x_2349_, 2, v___y_2346_);
v___x_2350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2349_);
return v___x_2350_;
}
v___jp_2353_:
{
if (lean_obj_tag(v___y_2354_) == 0)
{
if (v___x_2352_ == 0)
{
v___y_2346_ = v___y_2354_;
v___y_2347_ = v___y_2356_;
v___y_2348_ = v___y_2355_;
goto v___jp_2345_;
}
else
{
lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2359_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__2_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__2_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__2_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2360_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1(v___x_2359_, v___y_2357_, v___y_2358_);
if (lean_obj_tag(v___x_2360_) == 0)
{
lean_dec_ref_known(v___x_2360_, 1);
v___y_2346_ = v___y_2354_;
v___y_2347_ = v___y_2356_;
v___y_2348_ = v___y_2355_;
goto v___jp_2345_;
}
else
{
lean_object* v_a_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2368_; 
lean_dec(v___y_2356_);
lean_dec(v___y_2355_);
v_a_2361_ = lean_ctor_get(v___x_2360_, 0);
v_isSharedCheck_2368_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2363_ = v___x_2360_;
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_a_2361_);
lean_dec(v___x_2360_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___x_2366_; 
if (v_isShared_2364_ == 0)
{
v___x_2366_ = v___x_2363_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v_a_2361_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
return v___x_2366_;
}
}
}
}
}
else
{
v___y_2346_ = v___y_2354_;
v___y_2347_ = v___y_2356_;
v___y_2348_ = v___y_2355_;
goto v___jp_2345_;
}
}
v___jp_2369_:
{
if (lean_obj_tag(v___y_2374_) == 0)
{
if (v___x_2352_ == 0)
{
v___y_2354_ = v___y_2375_;
v___y_2355_ = v___y_2372_;
v___y_2356_ = v___y_2373_;
v___y_2357_ = v___y_2370_;
v___y_2358_ = v___y_2371_;
goto v___jp_2353_;
}
else
{
if (lean_obj_tag(v___y_2373_) == 0)
{
if (v___x_2352_ == 0)
{
v___y_2354_ = v___y_2375_;
v___y_2355_ = v___y_2372_;
v___y_2356_ = v___y_2373_;
v___y_2357_ = v___y_2370_;
v___y_2358_ = v___y_2371_;
goto v___jp_2353_;
}
else
{
lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2376_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__5_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__5_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__5_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2377_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1(v___x_2376_, v___y_2370_, v___y_2371_);
if (lean_obj_tag(v___x_2377_) == 0)
{
lean_dec_ref_known(v___x_2377_, 1);
v___y_2354_ = v___y_2375_;
v___y_2355_ = v___y_2372_;
v___y_2356_ = v___y_2373_;
v___y_2357_ = v___y_2370_;
v___y_2358_ = v___y_2371_;
goto v___jp_2353_;
}
else
{
lean_object* v_a_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2385_; 
lean_dec(v___y_2375_);
lean_dec(v___y_2372_);
v_a_2378_ = lean_ctor_get(v___x_2377_, 0);
v_isSharedCheck_2385_ = !lean_is_exclusive(v___x_2377_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2380_ = v___x_2377_;
v_isShared_2381_ = v_isSharedCheck_2385_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_a_2378_);
lean_dec(v___x_2377_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2385_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v___x_2383_; 
if (v_isShared_2381_ == 0)
{
v___x_2383_ = v___x_2380_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v_a_2378_);
v___x_2383_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
return v___x_2383_;
}
}
}
}
}
else
{
v___y_2354_ = v___y_2375_;
v___y_2355_ = v___y_2372_;
v___y_2356_ = v___y_2373_;
v___y_2357_ = v___y_2370_;
v___y_2358_ = v___y_2371_;
goto v___jp_2353_;
}
}
}
else
{
lean_dec_ref_known(v___y_2374_, 1);
v___y_2354_ = v___y_2375_;
v___y_2355_ = v___y_2372_;
v___y_2356_ = v___y_2373_;
v___y_2357_ = v___y_2370_;
v___y_2358_ = v___y_2371_;
goto v___jp_2353_;
}
}
v___jp_2386_:
{
if (lean_obj_tag(v___y_2389_) == 0)
{
lean_object* v___x_2393_; 
v___x_2393_ = lean_box(0);
v___y_2370_ = v___y_2387_;
v___y_2371_ = v___y_2388_;
v___y_2372_ = v___y_2390_;
v___y_2373_ = v___y_2392_;
v___y_2374_ = v___y_2391_;
v___y_2375_ = v___x_2393_;
goto v___jp_2369_;
}
else
{
lean_object* v_val_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2402_; 
v_val_2394_ = lean_ctor_get(v___y_2389_, 0);
v_isSharedCheck_2402_ = !lean_is_exclusive(v___y_2389_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2396_ = v___y_2389_;
v_isShared_2397_ = v_isSharedCheck_2402_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_val_2394_);
lean_dec(v___y_2389_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2402_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v___x_2398_; lean_object* v___x_2400_; 
v___x_2398_ = l_Lean_TSyntax_getString(v_val_2394_);
lean_dec(v_val_2394_);
if (v_isShared_2397_ == 0)
{
lean_ctor_set(v___x_2396_, 0, v___x_2398_);
v___x_2400_ = v___x_2396_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v___x_2398_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
v___y_2370_ = v___y_2387_;
v___y_2371_ = v___y_2388_;
v___y_2372_ = v___y_2390_;
v___y_2373_ = v___y_2392_;
v___y_2374_ = v___y_2391_;
v___y_2375_ = v___x_2400_;
goto v___jp_2369_;
}
}
}
}
v___jp_2403_:
{
if (lean_obj_tag(v___y_2407_) == 0)
{
lean_object* v___x_2410_; 
v___x_2410_ = lean_box(0);
v___y_2387_ = v___y_2408_;
v___y_2388_ = v___y_2409_;
v___y_2389_ = v___y_2405_;
v___y_2390_ = v___y_2404_;
v___y_2391_ = v___y_2406_;
v___y_2392_ = v___x_2410_;
goto v___jp_2386_;
}
else
{
lean_object* v_val_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2419_; 
v_val_2411_ = lean_ctor_get(v___y_2407_, 0);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___y_2407_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2413_ = v___y_2407_;
v_isShared_2414_ = v_isSharedCheck_2419_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_val_2411_);
lean_dec(v___y_2407_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2419_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2415_; lean_object* v___x_2417_; 
v___x_2415_ = l_Lean_TSyntax_getString(v_val_2411_);
lean_dec(v_val_2411_);
if (v_isShared_2414_ == 0)
{
lean_ctor_set(v___x_2413_, 0, v___x_2415_);
v___x_2417_ = v___x_2413_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___x_2415_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
v___y_2387_ = v___y_2408_;
v___y_2388_ = v___y_2409_;
v___y_2389_ = v___y_2405_;
v___y_2390_ = v___y_2404_;
v___y_2391_ = v___y_2406_;
v___y_2392_ = v___x_2417_;
goto v___jp_2386_;
}
}
}
}
v___jp_2420_:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2430_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2431_ = l_Lean_ConstantInfo_type(v___y_2421_);
lean_dec_ref(v___y_2421_);
v___x_2432_ = l_Lean_indentExpr(v___x_2431_);
v___x_2433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2430_);
lean_ctor_set(v___x_2433_, 1, v___x_2432_);
v___x_2434_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2433_);
lean_ctor_set(v___x_2435_, 1, v___x_2434_);
v___x_2436_ = l_Lean_ConstantInfo_type(v___y_2425_);
lean_dec_ref(v___y_2425_);
v___x_2437_ = l_Lean_indentExpr(v___x_2436_);
v___x_2438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2435_);
lean_ctor_set(v___x_2438_, 1, v___x_2437_);
v___x_2439_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__11_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__11_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__11_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2440_, 0, v___x_2438_);
lean_ctor_set(v___x_2440_, 1, v___x_2439_);
v___x_2441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2440_);
lean_ctor_set(v___x_2441_, 1, v_hint_2427_);
v___x_2442_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1(v___x_2441_, v___y_2428_, v___y_2429_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_dec_ref_known(v___x_2442_, 1);
v___y_2404_ = v___y_2423_;
v___y_2405_ = v___y_2422_;
v___y_2406_ = v___y_2424_;
v___y_2407_ = v___y_2426_;
v___y_2408_ = v___y_2428_;
v___y_2409_ = v___y_2429_;
goto v___jp_2403_;
}
else
{
lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2450_; 
lean_dec(v___y_2426_);
lean_dec(v___y_2424_);
lean_dec(v___y_2423_);
lean_dec(v___y_2422_);
v_a_2443_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2445_ = v___x_2442_;
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2442_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2448_; 
if (v_isShared_2446_ == 0)
{
v___x_2448_ = v___x_2445_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_a_2443_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
}
}
v___jp_2451_:
{
lean_object* v___x_2460_; 
v___x_2460_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__15_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__15_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__15_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___y_2421_ = v___y_2452_;
v___y_2422_ = v___y_2456_;
v___y_2423_ = v___y_2455_;
v___y_2424_ = v___y_2458_;
v___y_2425_ = v___y_2457_;
v___y_2426_ = v___y_2459_;
v_hint_2427_ = v___x_2460_;
v___y_2428_ = v___y_2454_;
v___y_2429_ = v___y_2453_;
goto v___jp_2420_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2____boxed(lean_object* v___x_2849_, lean_object* v___x_2850_, lean_object* v___f_2851_, lean_object* v___x_2852_, lean_object* v___x_2853_, lean_object* v___x_2854_, lean_object* v_a_2855_, lean_object* v_declName_2856_, lean_object* v_stx_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_){
_start:
{
uint8_t v___x_46597__boxed_2861_; lean_object* v_res_2862_; 
v___x_46597__boxed_2861_ = lean_unbox(v___x_2852_);
v_res_2862_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(v___x_2849_, v___x_2850_, v___f_2851_, v___x_46597__boxed_2861_, v___x_2853_, v___x_2854_, v_a_2855_, v_declName_2856_, v_stx_2857_, v___y_2858_, v___y_2859_);
lean_dec(v___y_2859_);
lean_dec_ref(v___y_2858_);
lean_dec_ref(v_a_2855_);
return v_res_2862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_2882_; lean_object* v___f_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; uint8_t v___x_2888_; lean_object* v___f_2889_; lean_object* v___x_2890_; 
v___f_2882_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___f_2883_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2884_ = lean_box(1);
v___x_2885_ = ((lean_object*)(l_Lean_Linter_instInhabitedDeprecationEntry_default));
v___x_2886_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_));
v___x_2887_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2888_ = 0;
v___f_2889_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2890_ = l_Lean_registerParametricAttributeExt___redArg(v___x_2887_, v___x_2888_, v___f_2889_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v_a_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___f_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; 
v_a_2891_ = lean_ctor_get(v___x_2890_, 0);
lean_inc_n(v_a_2891_, 2);
lean_dec_ref_known(v___x_2890_, 1);
v___x_2892_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_));
v___x_2893_ = lean_box(v___x_2888_);
v___f_2894_ = lean_alloc_closure((void*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2____boxed), 12, 7);
lean_closure_set(v___f_2894_, 0, v___x_2886_);
lean_closure_set(v___f_2894_, 1, v___x_2892_);
lean_closure_set(v___f_2894_, 2, v___f_2882_);
lean_closure_set(v___f_2894_, 3, v___x_2893_);
lean_closure_set(v___f_2894_, 4, v___x_2884_);
lean_closure_set(v___f_2894_, 5, v___x_2885_);
lean_closure_set(v___f_2894_, 6, v_a_2891_);
v___x_2895_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2896_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2896_, 0, v___x_2895_);
lean_ctor_set(v___x_2896_, 1, v___f_2894_);
lean_ctor_set(v___x_2896_, 2, v___f_2883_);
lean_ctor_set(v___x_2896_, 3, v___f_2889_);
lean_ctor_set_uint8(v___x_2896_, sizeof(void*)*4, v___x_2888_);
v___x_2897_ = l_Lean_registerParametricAttributeForExt___redArg(v___x_2896_, v_a_2891_);
return v___x_2897_;
}
else
{
lean_object* v_a_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2905_; 
v_a_2898_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2900_ = v___x_2890_;
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_a_2898_);
lean_dec(v___x_2890_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v___x_2903_; 
if (v_isShared_2901_ == 0)
{
v___x_2903_ = v___x_2900_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v_a_2898_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2____boxed(lean_object* v_a_2906_){
_start:
{
lean_object* v_res_2907_; 
v_res_2907_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_();
return v_res_2907_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_2908_, lean_object* v_msg_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_){
_start:
{
lean_object* v___x_2913_; 
v___x_2913_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___redArg(v_msg_2909_, v___y_2910_, v___y_2911_);
return v___x_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_2914_, lean_object* v_msg_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_){
_start:
{
lean_object* v_res_2919_; 
v_res_2919_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0(v_00_u03b1_2914_, v_msg_2915_, v___y_2916_, v___y_2917_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
return v_res_2919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3_spec__8(lean_object* v_o_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_){
_start:
{
lean_object* v___x_2924_; 
v___x_2924_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3_spec__8___redArg(v_o_2920_, v___y_2922_);
return v___x_2924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3_spec__8___boxed(lean_object* v_o_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_){
_start:
{
lean_object* v_res_2929_; 
v_res_2929_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3_spec__8(v_o_2925_, v___y_2926_, v___y_2927_);
lean_dec(v___y_2927_);
lean_dec_ref(v___y_2926_);
return v_res_2929_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6(lean_object* v_00_u03b2_2930_, lean_object* v_m_2931_, lean_object* v_a_2932_){
_start:
{
lean_object* v___x_2933_; 
v___x_2933_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6___redArg(v_m_2931_, v_a_2932_);
return v___x_2933_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6___boxed(lean_object* v_00_u03b2_2934_, lean_object* v_m_2935_, lean_object* v_a_2936_){
_start:
{
lean_object* v_res_2937_; 
v_res_2937_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6(v_00_u03b2_2934_, v_m_2935_, v_a_2936_);
lean_dec(v_a_2936_);
lean_dec_ref(v_m_2935_);
return v_res_2937_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8(lean_object* v_00_u03b2_2938_, lean_object* v_x_2939_, lean_object* v_x_2940_){
_start:
{
uint8_t v___x_2941_; 
v___x_2941_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg(v_x_2939_, v_x_2940_);
return v___x_2941_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_2942_, lean_object* v_x_2943_, lean_object* v_x_2944_){
_start:
{
uint8_t v_res_2945_; lean_object* v_r_2946_; 
v_res_2945_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8(v_00_u03b2_2942_, v_x_2943_, v_x_2944_);
lean_dec_ref(v_x_2944_);
lean_dec_ref(v_x_2943_);
v_r_2946_ = lean_box(v_res_2945_);
return v_r_2946_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6_spec__12(lean_object* v_00_u03b2_2947_, lean_object* v_a_2948_, lean_object* v_x_2949_){
_start:
{
lean_object* v___x_2950_; 
v___x_2950_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg(v_a_2948_, v_x_2949_);
return v___x_2950_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6_spec__12___boxed(lean_object* v_00_u03b2_2951_, lean_object* v_a_2952_, lean_object* v_x_2953_){
_start:
{
lean_object* v_res_2954_; 
v_res_2954_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6_spec__12(v_00_u03b2_2951_, v_a_2952_, v_x_2953_);
lean_dec(v_x_2953_);
lean_dec(v_a_2952_);
return v_res_2954_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__17(lean_object* v_00_u03b4_2955_, lean_object* v_t_2956_, lean_object* v_k_2957_){
_start:
{
lean_object* v___x_2958_; 
v___x_2958_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__17___redArg(v_t_2956_, v_k_2957_);
return v___x_2958_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__17___boxed(lean_object* v_00_u03b4_2959_, lean_object* v_t_2960_, lean_object* v_k_2961_){
_start:
{
lean_object* v_res_2962_; 
v_res_2962_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__17(v_00_u03b4_2959_, v_t_2960_, v_k_2961_);
lean_dec(v_k_2961_);
lean_dec(v_t_2960_);
return v_res_2962_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12(lean_object* v_00_u03b2_2963_, lean_object* v_x_2964_, size_t v_x_2965_, lean_object* v_x_2966_){
_start:
{
uint8_t v___x_2967_; 
v___x_2967_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12___redArg(v_x_2964_, v_x_2965_, v_x_2966_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12___boxed(lean_object* v_00_u03b2_2968_, lean_object* v_x_2969_, lean_object* v_x_2970_, lean_object* v_x_2971_){
_start:
{
size_t v_x_47879__boxed_2972_; uint8_t v_res_2973_; lean_object* v_r_2974_; 
v_x_47879__boxed_2972_ = lean_unbox_usize(v_x_2970_);
lean_dec(v_x_2970_);
v_res_2973_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12(v_00_u03b2_2968_, v_x_2969_, v_x_47879__boxed_2972_, v_x_2971_);
lean_dec_ref(v_x_2971_);
lean_dec_ref(v_x_2969_);
v_r_2974_ = lean_box(v_res_2973_);
return v_r_2974_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20(lean_object* v_givenName_2975_, uint8_t v_skipAuxDecl_2976_, lean_object* v_auxDeclToFullName_2977_, lean_object* v___x_2978_, lean_object* v_givenNameView_2979_, lean_object* v_as_2980_, lean_object* v_i_2981_, lean_object* v_a_2982_){
_start:
{
lean_object* v___x_2983_; 
v___x_2983_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg(v_givenName_2975_, v_skipAuxDecl_2976_, v_auxDeclToFullName_2977_, v___x_2978_, v_givenNameView_2979_, v_as_2980_, v_i_2981_);
return v___x_2983_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___boxed(lean_object* v_givenName_2984_, lean_object* v_skipAuxDecl_2985_, lean_object* v_auxDeclToFullName_2986_, lean_object* v___x_2987_, lean_object* v_givenNameView_2988_, lean_object* v_as_2989_, lean_object* v_i_2990_, lean_object* v_a_2991_){
_start:
{
uint8_t v_skipAuxDecl_boxed_2992_; lean_object* v_res_2993_; 
v_skipAuxDecl_boxed_2992_ = lean_unbox(v_skipAuxDecl_2985_);
v_res_2993_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20(v_givenName_2984_, v_skipAuxDecl_boxed_2992_, v_auxDeclToFullName_2986_, v___x_2987_, v_givenNameView_2988_, v_as_2989_, v_i_2990_, v_a_2991_);
lean_dec_ref(v_as_2989_);
lean_dec(v_auxDeclToFullName_2986_);
lean_dec(v_givenName_2984_);
return v_res_2993_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23(lean_object* v_localDecl_x3f_2994_, lean_object* v_givenName_2995_, lean_object* v_as_2996_, lean_object* v_i_2997_, lean_object* v_a_2998_){
_start:
{
lean_object* v___x_2999_; 
v___x_2999_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___redArg(v_localDecl_x3f_2994_, v_givenName_2995_, v_as_2996_, v_i_2997_);
return v___x_2999_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___boxed(lean_object* v_localDecl_x3f_3000_, lean_object* v_givenName_3001_, lean_object* v_as_3002_, lean_object* v_i_3003_, lean_object* v_a_3004_){
_start:
{
lean_object* v_res_3005_; 
v_res_3005_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23(v_localDecl_x3f_3000_, v_givenName_3001_, v_as_3002_, v_i_3003_, v_a_3004_);
lean_dec_ref(v_as_3002_);
lean_dec(v_givenName_3001_);
lean_dec(v_localDecl_x3f_3000_);
return v_res_3005_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30(lean_object* v_n_u2080_3006_, lean_object* v_filter_3007_, lean_object* v_view_x3f_3008_, lean_object* v_as_3009_, lean_object* v_as_x27_3010_, lean_object* v_b_3011_, lean_object* v_a_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_){
_start:
{
lean_object* v___x_3018_; 
v___x_3018_ = l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30___redArg(v_n_u2080_3006_, v_filter_3007_, v_view_x3f_3008_, v_as_x27_3010_, v_b_3011_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_);
return v___x_3018_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30___boxed(lean_object* v_n_u2080_3019_, lean_object* v_filter_3020_, lean_object* v_view_x3f_3021_, lean_object* v_as_3022_, lean_object* v_as_x27_3023_, lean_object* v_b_3024_, lean_object* v_a_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_){
_start:
{
lean_object* v_res_3031_; 
v_res_3031_ = l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30(v_n_u2080_3019_, v_filter_3020_, v_view_x3f_3021_, v_as_3022_, v_as_x27_3023_, v_b_3024_, v_a_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_);
lean_dec(v___y_3029_);
lean_dec_ref(v___y_3028_);
lean_dec(v___y_3027_);
lean_dec_ref(v___y_3026_);
lean_dec(v_as_x27_3023_);
lean_dec(v_as_3022_);
lean_dec(v_n_u2080_3019_);
return v_res_3031_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17(lean_object* v_00_u03b2_3032_, lean_object* v_keys_3033_, lean_object* v_vals_3034_, lean_object* v_heq_3035_, lean_object* v_i_3036_, lean_object* v_k_3037_){
_start:
{
uint8_t v___x_3038_; 
v___x_3038_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17___redArg(v_keys_3033_, v_i_3036_, v_k_3037_);
return v___x_3038_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17___boxed(lean_object* v_00_u03b2_3039_, lean_object* v_keys_3040_, lean_object* v_vals_3041_, lean_object* v_heq_3042_, lean_object* v_i_3043_, lean_object* v_k_3044_){
_start:
{
uint8_t v_res_3045_; lean_object* v_r_3046_; 
v_res_3045_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17(v_00_u03b2_3039_, v_keys_3040_, v_vals_3041_, v_heq_3042_, v_i_3043_, v_k_3044_);
lean_dec_ref(v_k_3044_);
lean_dec_ref(v_vals_3041_);
lean_dec_ref(v_keys_3040_);
v_r_3046_ = lean_box(v_res_3045_);
return v_r_3046_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24(lean_object* v_givenName_3047_, uint8_t v_skipAuxDecl_3048_, lean_object* v_auxDeclToFullName_3049_, lean_object* v___x_3050_, lean_object* v_givenNameView_3051_, lean_object* v_as_3052_, lean_object* v_i_3053_, lean_object* v_a_3054_){
_start:
{
lean_object* v___x_3055_; 
v___x_3055_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24___redArg(v_givenName_3047_, v_skipAuxDecl_3048_, v_auxDeclToFullName_3049_, v___x_3050_, v_givenNameView_3051_, v_as_3052_, v_i_3053_);
return v___x_3055_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24___boxed(lean_object* v_givenName_3056_, lean_object* v_skipAuxDecl_3057_, lean_object* v_auxDeclToFullName_3058_, lean_object* v___x_3059_, lean_object* v_givenNameView_3060_, lean_object* v_as_3061_, lean_object* v_i_3062_, lean_object* v_a_3063_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3064_; lean_object* v_res_3065_; 
v_skipAuxDecl_boxed_3064_ = lean_unbox(v_skipAuxDecl_3057_);
v_res_3065_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24(v_givenName_3056_, v_skipAuxDecl_boxed_3064_, v_auxDeclToFullName_3058_, v___x_3059_, v_givenNameView_3060_, v_as_3061_, v_i_3062_, v_a_3063_);
lean_dec_ref(v_as_3061_);
lean_dec(v_auxDeclToFullName_3058_);
lean_dec(v_givenName_3056_);
return v_res_3065_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28(lean_object* v_localDecl_x3f_3066_, lean_object* v_givenName_3067_, lean_object* v_as_3068_, lean_object* v_i_3069_, lean_object* v_a_3070_){
_start:
{
lean_object* v___x_3071_; 
v___x_3071_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28___redArg(v_localDecl_x3f_3066_, v_givenName_3067_, v_as_3068_, v_i_3069_);
return v___x_3071_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28___boxed(lean_object* v_localDecl_x3f_3072_, lean_object* v_givenName_3073_, lean_object* v_as_3074_, lean_object* v_i_3075_, lean_object* v_a_3076_){
_start:
{
lean_object* v_res_3077_; 
v_res_3077_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28(v_localDecl_x3f_3072_, v_givenName_3073_, v_as_3074_, v_i_3075_, v_a_3076_);
lean_dec_ref(v_as_3074_);
lean_dec(v_givenName_3073_);
lean_dec(v_localDecl_x3f_3072_);
return v_res_3077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37(lean_object* v_opt_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_){
_start:
{
lean_object* v___x_3084_; 
v___x_3084_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37___redArg(v_opt_3078_, v___y_3081_);
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37___boxed(lean_object* v_opt_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_){
_start:
{
lean_object* v_res_3091_; 
v_res_3091_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37(v_opt_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_);
lean_dec(v___y_3089_);
lean_dec_ref(v___y_3088_);
lean_dec(v___y_3087_);
lean_dec_ref(v___y_3086_);
lean_dec_ref(v_opt_3085_);
return v_res_3091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43(lean_object* v_opt_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_){
_start:
{
lean_object* v___x_3098_; 
v___x_3098_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43___redArg(v_opt_3092_, v___y_3095_);
return v___x_3098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43___boxed(lean_object* v_opt_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_){
_start:
{
lean_object* v_res_3105_; 
v_res_3105_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43(v_opt_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_);
lean_dec(v___y_3103_);
lean_dec_ref(v___y_3102_);
lean_dec(v___y_3101_);
lean_dec_ref(v___y_3100_);
lean_dec_ref(v_opt_3099_);
return v_res_3105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___redArg___lam__0(lean_object* v_declName_3106_, lean_object* v_entry_3107_, lean_object* v_inst_3108_, lean_object* v_inst_3109_, lean_object* v_inst_3110_, lean_object* v_env_3111_){
_start:
{
lean_object* v___x_3112_; lean_object* v___x_3113_; 
v___x_3112_ = l_Lean_Linter_deprecatedAttr;
v___x_3113_ = l_Lean_ParametricAttribute_setParam___redArg(v___x_3112_, v_env_3111_, v_declName_3106_, v_entry_3107_);
if (lean_obj_tag(v___x_3113_) == 0)
{
lean_object* v_a_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3123_; 
lean_dec_ref(v_inst_3110_);
v_a_3114_ = lean_ctor_get(v___x_3113_, 0);
v_isSharedCheck_3123_ = !lean_is_exclusive(v___x_3113_);
if (v_isSharedCheck_3123_ == 0)
{
v___x_3116_ = v___x_3113_;
v_isShared_3117_ = v_isSharedCheck_3123_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_a_3114_);
lean_dec(v___x_3113_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3123_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v___x_3119_; 
if (v_isShared_3117_ == 0)
{
lean_ctor_set_tag(v___x_3116_, 3);
v___x_3119_ = v___x_3116_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_a_3114_);
v___x_3119_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; 
v___x_3120_ = l_Lean_MessageData_ofFormat(v___x_3119_);
v___x_3121_ = l_Lean_throwError___redArg(v_inst_3108_, v_inst_3109_, v___x_3120_);
return v___x_3121_;
}
}
}
else
{
lean_object* v_a_3124_; lean_object* v___x_3125_; 
lean_dec_ref(v_inst_3109_);
lean_dec_ref(v_inst_3108_);
v_a_3124_ = lean_ctor_get(v___x_3113_, 0);
lean_inc(v_a_3124_);
lean_dec_ref_known(v___x_3113_, 1);
v___x_3125_ = l_Lean_setEnv___redArg(v_inst_3110_, v_a_3124_);
return v___x_3125_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___redArg(lean_object* v_inst_3126_, lean_object* v_inst_3127_, lean_object* v_inst_3128_, lean_object* v_declName_3129_, lean_object* v_entry_3130_){
_start:
{
lean_object* v_toBind_3131_; lean_object* v_getEnv_3132_; lean_object* v___f_3133_; lean_object* v___x_3134_; 
v_toBind_3131_ = lean_ctor_get(v_inst_3126_, 1);
lean_inc(v_toBind_3131_);
v_getEnv_3132_ = lean_ctor_get(v_inst_3127_, 0);
lean_inc(v_getEnv_3132_);
v___f_3133_ = lean_alloc_closure((void*)(l_Lean_Linter_setDeprecated___redArg___lam__0), 6, 5);
lean_closure_set(v___f_3133_, 0, v_declName_3129_);
lean_closure_set(v___f_3133_, 1, v_entry_3130_);
lean_closure_set(v___f_3133_, 2, v_inst_3126_);
lean_closure_set(v___f_3133_, 3, v_inst_3128_);
lean_closure_set(v___f_3133_, 4, v_inst_3127_);
v___x_3134_ = lean_apply_4(v_toBind_3131_, lean_box(0), lean_box(0), v_getEnv_3132_, v___f_3133_);
return v___x_3134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated(lean_object* v_m_3135_, lean_object* v_inst_3136_, lean_object* v_inst_3137_, lean_object* v_inst_3138_, lean_object* v_declName_3139_, lean_object* v_entry_3140_){
_start:
{
lean_object* v___x_3141_; 
v___x_3141_ = l_Lean_Linter_setDeprecated___redArg(v_inst_3136_, v_inst_3137_, v_inst_3138_, v_declName_3139_, v_entry_3140_);
return v___x_3141_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_isDeprecated(lean_object* v_env_3142_, lean_object* v_declName_3143_){
_start:
{
lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; 
v___x_3144_ = ((lean_object*)(l_Lean_Linter_instInhabitedDeprecationEntry_default));
v___x_3145_ = l_Lean_Linter_deprecatedAttr;
v___x_3146_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_3144_, v___x_3145_, v_env_3142_, v_declName_3143_);
if (lean_obj_tag(v___x_3146_) == 0)
{
uint8_t v___x_3147_; 
v___x_3147_ = 0;
return v___x_3147_;
}
else
{
uint8_t v___x_3148_; 
lean_dec_ref_known(v___x_3146_, 1);
v___x_3148_ = 1;
return v___x_3148_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_isDeprecated___boxed(lean_object* v_env_3149_, lean_object* v_declName_3150_){
_start:
{
uint8_t v_res_3151_; lean_object* v_r_3152_; 
v_res_3151_ = l_Lean_Linter_isDeprecated(v_env_3149_, v_declName_3150_);
v_r_3152_ = lean_box(v_res_3151_);
return v_r_3152_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_isDeprecationWarning___lam__0(lean_object* v_x_3153_){
_start:
{
lean_object* v___x_3154_; uint8_t v___x_3155_; 
v___x_3154_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_3155_ = lean_name_eq(v_x_3153_, v___x_3154_);
return v___x_3155_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_isDeprecationWarning___lam__0___boxed(lean_object* v_x_3156_){
_start:
{
uint8_t v_res_3157_; lean_object* v_r_3158_; 
v_res_3157_ = l_Lean_MessageData_isDeprecationWarning___lam__0(v_x_3156_);
lean_dec(v_x_3156_);
v_r_3158_ = lean_box(v_res_3157_);
return v_r_3158_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_isDeprecationWarning(lean_object* v_msg_3160_){
_start:
{
lean_object* v___f_3161_; uint8_t v___x_3162_; 
v___f_3161_ = ((lean_object*)(l_Lean_MessageData_isDeprecationWarning___closed__0));
v___x_3162_ = l_Lean_MessageData_hasTag(v___f_3161_, v_msg_3160_);
return v___x_3162_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_isDeprecationWarning___boxed(lean_object* v_msg_3163_){
_start:
{
uint8_t v_res_3164_; lean_object* v_r_3165_; 
v_res_3164_ = l_Lean_MessageData_isDeprecationWarning(v_msg_3163_);
v_r_3165_ = lean_box(v_res_3164_);
return v_r_3165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getDeprecatedNewName(lean_object* v_env_3166_, lean_object* v_declName_3167_){
_start:
{
lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; 
v___x_3168_ = ((lean_object*)(l_Lean_Linter_instInhabitedDeprecationEntry_default));
v___x_3169_ = l_Lean_Linter_deprecatedAttr;
v___x_3170_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_3168_, v___x_3169_, v_env_3166_, v_declName_3167_);
if (lean_obj_tag(v___x_3170_) == 0)
{
lean_object* v___x_3171_; 
v___x_3171_ = lean_box(0);
return v___x_3171_;
}
else
{
lean_object* v_val_3172_; lean_object* v_newName_x3f_3173_; 
v_val_3172_ = lean_ctor_get(v___x_3170_, 0);
lean_inc(v_val_3172_);
lean_dec_ref_known(v___x_3170_, 1);
v_newName_x3f_3173_ = lean_ctor_get(v_val_3172_, 0);
lean_inc(v_newName_x3f_3173_);
lean_dec(v_val_3172_);
return v_newName_x3f_3173_;
}
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0(lean_object* v_x_3174_, lean_object* v_x_3175_){
_start:
{
if (lean_obj_tag(v_x_3174_) == 0)
{
if (lean_obj_tag(v_x_3175_) == 0)
{
uint8_t v___x_3176_; 
v___x_3176_ = 1;
return v___x_3176_;
}
else
{
uint8_t v___x_3177_; 
v___x_3177_ = 0;
return v___x_3177_;
}
}
else
{
if (lean_obj_tag(v_x_3175_) == 0)
{
uint8_t v___x_3178_; 
v___x_3178_ = 0;
return v___x_3178_;
}
else
{
lean_object* v_head_3179_; lean_object* v_tail_3180_; lean_object* v_head_3181_; lean_object* v_tail_3182_; uint8_t v___x_3183_; 
v_head_3179_ = lean_ctor_get(v_x_3174_, 0);
v_tail_3180_ = lean_ctor_get(v_x_3174_, 1);
v_head_3181_ = lean_ctor_get(v_x_3175_, 0);
v_tail_3182_ = lean_ctor_get(v_x_3175_, 1);
v___x_3183_ = lean_string_dec_eq(v_head_3179_, v_head_3181_);
if (v___x_3183_ == 0)
{
return v___x_3183_;
}
else
{
v_x_3174_ = v_tail_3180_;
v_x_3175_ = v_tail_3182_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0___boxed(lean_object* v_x_3185_, lean_object* v_x_3186_){
_start:
{
uint8_t v_res_3187_; lean_object* v_r_3188_; 
v_res_3187_ = l_List_beq___at___00List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0(v_x_3185_, v_x_3186_);
lean_dec(v_x_3186_);
lean_dec(v_x_3185_);
v_r_3188_ = lean_box(v_res_3187_);
return v_r_3188_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0(lean_object* v_x_3189_, lean_object* v_x_3190_){
_start:
{
if (lean_obj_tag(v_x_3189_) == 0)
{
if (lean_obj_tag(v_x_3190_) == 0)
{
uint8_t v___x_3191_; 
v___x_3191_ = 1;
return v___x_3191_;
}
else
{
uint8_t v___x_3192_; 
v___x_3192_ = 0;
return v___x_3192_;
}
}
else
{
if (lean_obj_tag(v_x_3190_) == 0)
{
uint8_t v___x_3193_; 
v___x_3193_ = 0;
return v___x_3193_;
}
else
{
lean_object* v_head_3194_; lean_object* v_tail_3195_; lean_object* v_head_3196_; lean_object* v_tail_3197_; uint8_t v___y_3199_; lean_object* v_fst_3201_; lean_object* v_snd_3202_; lean_object* v_fst_3203_; lean_object* v_snd_3204_; uint8_t v___x_3205_; 
v_head_3194_ = lean_ctor_get(v_x_3189_, 0);
v_tail_3195_ = lean_ctor_get(v_x_3189_, 1);
v_head_3196_ = lean_ctor_get(v_x_3190_, 0);
v_tail_3197_ = lean_ctor_get(v_x_3190_, 1);
v_fst_3201_ = lean_ctor_get(v_head_3194_, 0);
v_snd_3202_ = lean_ctor_get(v_head_3194_, 1);
v_fst_3203_ = lean_ctor_get(v_head_3196_, 0);
v_snd_3204_ = lean_ctor_get(v_head_3196_, 1);
v___x_3205_ = lean_name_eq(v_fst_3201_, v_fst_3203_);
if (v___x_3205_ == 0)
{
v___y_3199_ = v___x_3205_;
goto v___jp_3198_;
}
else
{
uint8_t v___x_3206_; 
v___x_3206_ = l_List_beq___at___00List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0(v_snd_3202_, v_snd_3204_);
v___y_3199_ = v___x_3206_;
goto v___jp_3198_;
}
v___jp_3198_:
{
if (v___y_3199_ == 0)
{
return v___y_3199_;
}
else
{
v_x_3189_ = v_tail_3195_;
v_x_3190_ = v_tail_3197_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0___boxed(lean_object* v_x_3207_, lean_object* v_x_3208_){
_start:
{
uint8_t v_res_3209_; lean_object* v_r_3210_; 
v_res_3209_ = l_List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0(v_x_3207_, v_x_3208_);
lean_dec(v_x_3208_);
lean_dec(v_x_3207_);
v_r_3210_ = lean_box(v_res_3209_);
return v_r_3210_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__1(void){
_start:
{
lean_object* v___x_3212_; lean_object* v___x_3213_; 
v___x_3212_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__0));
v___x_3213_ = l_Lean_stringToMessageData(v___x_3212_);
return v___x_3213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f(lean_object* v_declName_3214_, lean_object* v_newName_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_){
_start:
{
lean_object* v_ref_3221_; 
v_ref_3221_ = lean_ctor_get(v_a_3218_, 2);
if (lean_obj_tag(v_ref_3221_) == 3)
{
lean_object* v_val_3222_; uint8_t v___x_3223_; 
v_val_3222_ = lean_ctor_get(v_ref_3221_, 2);
v___x_3223_ = l_Lean_Name_hasMacroScopes(v_val_3222_);
if (v___x_3223_ == 0)
{
uint8_t v___x_3224_; lean_object* v___x_3302_; 
v___x_3224_ = 1;
v___x_3302_ = l_Lean_Syntax_getRange_x3f(v_ref_3221_, v___x_3224_);
if (lean_obj_tag(v___x_3302_) == 0)
{
if (v___x_3223_ == 0)
{
lean_object* v___x_3303_; lean_object* v___x_3304_; 
lean_dec(v_newName_3215_);
lean_dec(v_declName_3214_);
v___x_3303_ = lean_box(0);
v___x_3304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3303_);
return v___x_3304_;
}
else
{
goto v___jp_3225_;
}
}
else
{
lean_dec_ref_known(v___x_3302_, 1);
goto v___jp_3225_;
}
v___jp_3225_:
{
lean_object* v___x_3226_; 
lean_inc(v_val_3222_);
v___x_3226_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26(v_val_3222_, v___x_3224_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_);
if (lean_obj_tag(v___x_3226_) == 0)
{
lean_object* v_a_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3293_; 
v_a_3227_ = lean_ctor_get(v___x_3226_, 0);
v_isSharedCheck_3293_ = !lean_is_exclusive(v___x_3226_);
if (v_isSharedCheck_3293_ == 0)
{
v___x_3229_ = v___x_3226_;
v_isShared_3230_ = v_isSharedCheck_3293_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_a_3227_);
lean_dec(v___x_3226_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3293_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; uint8_t v___x_3234_; 
v___x_3231_ = lean_box(0);
v___x_3232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3232_, 0, v_declName_3214_);
lean_ctor_set(v___x_3232_, 1, v___x_3231_);
v___x_3233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3233_, 0, v___x_3232_);
lean_ctor_set(v___x_3233_, 1, v___x_3231_);
v___x_3234_ = l_List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0(v_a_3227_, v___x_3233_);
lean_dec_ref_known(v___x_3233_, 2);
lean_dec(v_a_3227_);
if (v___x_3234_ == 0)
{
lean_object* v___x_3235_; lean_object* v___x_3237_; 
lean_dec(v_newName_3215_);
v___x_3235_ = lean_box(0);
if (v_isShared_3230_ == 0)
{
lean_ctor_set(v___x_3229_, 0, v___x_3235_);
v___x_3237_ = v___x_3229_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v___x_3235_);
v___x_3237_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
return v___x_3237_;
}
}
else
{
lean_object* v___x_3239_; 
lean_del_object(v___x_3229_);
v___x_3239_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5(v_newName_3215_, v___x_3223_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_);
if (lean_obj_tag(v___x_3239_) == 0)
{
lean_object* v_a_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3284_; 
v_a_3240_ = lean_ctor_get(v___x_3239_, 0);
v_isSharedCheck_3284_ = !lean_is_exclusive(v___x_3239_);
if (v_isSharedCheck_3284_ == 0)
{
v___x_3242_ = v___x_3239_;
v_isShared_3243_ = v_isSharedCheck_3284_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_a_3240_);
lean_dec(v___x_3239_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3284_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
if (lean_obj_tag(v_a_3240_) == 1)
{
lean_object* v_val_3244_; lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3279_; 
lean_del_object(v___x_3242_);
v_val_3244_ = lean_ctor_get(v_a_3240_, 0);
v_isSharedCheck_3279_ = !lean_is_exclusive(v_a_3240_);
if (v_isSharedCheck_3279_ == 0)
{
v___x_3246_ = v_a_3240_;
v_isShared_3247_ = v_isSharedCheck_3279_;
goto v_resetjp_3245_;
}
else
{
lean_inc(v_val_3244_);
lean_dec(v_a_3240_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3279_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; uint8_t v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3259_; 
v___x_3248_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__1, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__1_once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__1);
v___x_3249_ = l_Lean_Name_toString(v_val_3244_, v___x_3224_);
v___x_3250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3250_, 0, v___x_3249_);
v___x_3251_ = lean_box(0);
v___x_3252_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3252_, 0, v___x_3250_);
lean_ctor_set(v___x_3252_, 1, v___x_3251_);
lean_ctor_set(v___x_3252_, 2, v___x_3251_);
lean_ctor_set(v___x_3252_, 3, v___x_3251_);
lean_ctor_set(v___x_3252_, 4, v___x_3251_);
lean_ctor_set(v___x_3252_, 5, v___x_3251_);
v___x_3253_ = 0;
v___x_3254_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3254_, 0, v___x_3252_);
lean_ctor_set(v___x_3254_, 1, v___x_3251_);
lean_ctor_set(v___x_3254_, 2, v___x_3251_);
lean_ctor_set_uint8(v___x_3254_, sizeof(void*)*3, v___x_3253_);
v___x_3255_ = lean_unsigned_to_nat(1u);
v___x_3256_ = lean_mk_empty_array_with_capacity(v___x_3255_);
v___x_3257_ = lean_array_push(v___x_3256_, v___x_3254_);
lean_inc_ref(v_ref_3221_);
if (v_isShared_3247_ == 0)
{
lean_ctor_set(v___x_3246_, 0, v_ref_3221_);
v___x_3259_ = v___x_3246_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3278_; 
v_reuseFailAlloc_3278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3278_, 0, v_ref_3221_);
v___x_3259_ = v_reuseFailAlloc_3278_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
lean_object* v___x_3260_; 
v___x_3260_ = l_Lean_MessageData_hint(v___x_3248_, v___x_3257_, v___x_3259_, v___x_3251_, v___x_3223_, v_a_3218_, v_a_3219_);
lean_dec_ref(v___x_3257_);
if (lean_obj_tag(v___x_3260_) == 0)
{
lean_object* v_a_3261_; lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3269_; 
v_a_3261_ = lean_ctor_get(v___x_3260_, 0);
v_isSharedCheck_3269_ = !lean_is_exclusive(v___x_3260_);
if (v_isSharedCheck_3269_ == 0)
{
v___x_3263_ = v___x_3260_;
v_isShared_3264_ = v_isSharedCheck_3269_;
goto v_resetjp_3262_;
}
else
{
lean_inc(v_a_3261_);
lean_dec(v___x_3260_);
v___x_3263_ = lean_box(0);
v_isShared_3264_ = v_isSharedCheck_3269_;
goto v_resetjp_3262_;
}
v_resetjp_3262_:
{
lean_object* v___x_3265_; lean_object* v___x_3267_; 
v___x_3265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3265_, 0, v_a_3261_);
if (v_isShared_3264_ == 0)
{
lean_ctor_set(v___x_3263_, 0, v___x_3265_);
v___x_3267_ = v___x_3263_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v___x_3265_);
v___x_3267_ = v_reuseFailAlloc_3268_;
goto v_reusejp_3266_;
}
v_reusejp_3266_:
{
return v___x_3267_;
}
}
}
else
{
lean_object* v_a_3270_; lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3277_; 
v_a_3270_ = lean_ctor_get(v___x_3260_, 0);
v_isSharedCheck_3277_ = !lean_is_exclusive(v___x_3260_);
if (v_isSharedCheck_3277_ == 0)
{
v___x_3272_ = v___x_3260_;
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
else
{
lean_inc(v_a_3270_);
lean_dec(v___x_3260_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
lean_object* v___x_3275_; 
if (v_isShared_3273_ == 0)
{
v___x_3275_ = v___x_3272_;
goto v_reusejp_3274_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v_a_3270_);
v___x_3275_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3274_;
}
v_reusejp_3274_:
{
return v___x_3275_;
}
}
}
}
}
}
else
{
lean_object* v___x_3280_; lean_object* v___x_3282_; 
lean_dec(v_a_3240_);
v___x_3280_ = lean_box(0);
if (v_isShared_3243_ == 0)
{
lean_ctor_set(v___x_3242_, 0, v___x_3280_);
v___x_3282_ = v___x_3242_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3283_; 
v_reuseFailAlloc_3283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3283_, 0, v___x_3280_);
v___x_3282_ = v_reuseFailAlloc_3283_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
return v___x_3282_;
}
}
}
}
else
{
lean_object* v_a_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3292_; 
v_a_3285_ = lean_ctor_get(v___x_3239_, 0);
v_isSharedCheck_3292_ = !lean_is_exclusive(v___x_3239_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3287_ = v___x_3239_;
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
else
{
lean_inc(v_a_3285_);
lean_dec(v___x_3239_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
lean_object* v___x_3290_; 
if (v_isShared_3288_ == 0)
{
v___x_3290_ = v___x_3287_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_a_3285_);
v___x_3290_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
return v___x_3290_;
}
}
}
}
}
}
else
{
lean_object* v_a_3294_; lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3301_; 
lean_dec(v_newName_3215_);
lean_dec(v_declName_3214_);
v_a_3294_ = lean_ctor_get(v___x_3226_, 0);
v_isSharedCheck_3301_ = !lean_is_exclusive(v___x_3226_);
if (v_isSharedCheck_3301_ == 0)
{
v___x_3296_ = v___x_3226_;
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
else
{
lean_inc(v_a_3294_);
lean_dec(v___x_3226_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
lean_object* v___x_3299_; 
if (v_isShared_3297_ == 0)
{
v___x_3299_ = v___x_3296_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v_a_3294_);
v___x_3299_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
return v___x_3299_;
}
}
}
}
}
else
{
lean_object* v___x_3305_; lean_object* v___x_3306_; 
lean_dec(v_newName_3215_);
lean_dec(v_declName_3214_);
v___x_3305_ = lean_box(0);
v___x_3306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3306_, 0, v___x_3305_);
return v___x_3306_;
}
}
else
{
lean_object* v___x_3307_; lean_object* v___x_3308_; 
lean_dec(v_newName_3215_);
lean_dec(v_declName_3214_);
v___x_3307_ = lean_box(0);
v___x_3308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3308_, 0, v___x_3307_);
return v___x_3308_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___boxed(lean_object* v_declName_3309_, lean_object* v_newName_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_){
_start:
{
lean_object* v_res_3316_; 
v_res_3316_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f(v_declName_3309_, v_newName_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_);
lean_dec(v_a_3314_);
lean_dec_ref(v_a_3313_);
lean_dec(v_a_3312_);
lean_dec_ref(v_a_3311_);
return v_res_3316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(lean_object* v_o_3317_, lean_object* v___y_3318_){
_start:
{
lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v_env_3322_; lean_object* v___x_3323_; lean_object* v_toEnvExtension_3324_; lean_object* v_asyncMode_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v_merged_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3336_; 
v___x_3320_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_3321_ = lean_st_ref_get(v___y_3318_);
v_env_3322_ = lean_ctor_get(v___x_3321_, 0);
lean_inc_ref(v_env_3322_);
lean_dec(v___x_3321_);
v___x_3323_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_3324_ = lean_ctor_get(v___x_3323_, 0);
v_asyncMode_3325_ = lean_ctor_get(v_toEnvExtension_3324_, 2);
v___x_3326_ = lean_box(0);
v___x_3327_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3320_, v___x_3323_, v_env_3322_, v_asyncMode_3325_, v___x_3326_);
v_merged_3328_ = lean_ctor_get(v___x_3327_, 0);
v_isSharedCheck_3336_ = !lean_is_exclusive(v___x_3327_);
if (v_isSharedCheck_3336_ == 0)
{
lean_object* v_unused_3337_; 
v_unused_3337_ = lean_ctor_get(v___x_3327_, 1);
lean_dec(v_unused_3337_);
v___x_3330_ = v___x_3327_;
v_isShared_3331_ = v_isSharedCheck_3336_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_merged_3328_);
lean_dec(v___x_3327_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3336_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
lean_object* v___x_3333_; 
if (v_isShared_3331_ == 0)
{
lean_ctor_set(v___x_3330_, 1, v_merged_3328_);
lean_ctor_set(v___x_3330_, 0, v_o_3317_);
v___x_3333_ = v___x_3330_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v_o_3317_);
lean_ctor_set(v_reuseFailAlloc_3335_, 1, v_merged_3328_);
v___x_3333_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
lean_object* v___x_3334_; 
v___x_3334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3334_, 0, v___x_3333_);
return v___x_3334_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg___boxed(lean_object* v_o_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_){
_start:
{
lean_object* v_res_3341_; 
v_res_3341_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(v_o_3338_, v___y_3339_);
lean_dec(v___y_3339_);
return v_res_3341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0(lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_){
_start:
{
lean_object* v___x_3347_; lean_object* v___x_3348_; 
v___x_3347_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3344_);
v___x_3348_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(v___x_3347_, v___y_3345_);
return v___x_3348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0___boxed(lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_){
_start:
{
lean_object* v_res_3354_; 
v_res_3354_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0(v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_);
lean_dec(v___y_3352_);
lean_dec_ref(v___y_3351_);
lean_dec(v___y_3350_);
lean_dec_ref(v___y_3349_);
return v_res_3354_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__1(void){
_start:
{
lean_object* v___x_3356_; lean_object* v___x_3357_; 
v___x_3356_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__0));
v___x_3357_ = l_Lean_stringToMessageData(v___x_3356_);
return v___x_3357_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__3(void){
_start:
{
lean_object* v___x_3359_; lean_object* v___x_3360_; 
v___x_3359_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__2));
v___x_3360_ = l_Lean_stringToMessageData(v___x_3359_);
return v___x_3360_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__5(void){
_start:
{
lean_object* v___x_3362_; lean_object* v___x_3363_; 
v___x_3362_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__4));
v___x_3363_ = l_Lean_stringToMessageData(v___x_3362_);
return v___x_3363_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__7(void){
_start:
{
lean_object* v___x_3365_; lean_object* v___x_3366_; 
v___x_3365_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__6));
v___x_3366_ = l_Lean_stringToMessageData(v___x_3365_);
return v___x_3366_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__9(void){
_start:
{
lean_object* v___x_3368_; lean_object* v___x_3369_; 
v___x_3368_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__8));
v___x_3369_ = l_Lean_stringToMessageData(v___x_3368_);
return v___x_3369_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__11(void){
_start:
{
lean_object* v___x_3371_; lean_object* v___x_3372_; 
v___x_3371_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__10));
v___x_3372_ = l_Lean_stringToMessageData(v___x_3371_);
return v___x_3372_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__13(void){
_start:
{
lean_object* v___x_3374_; lean_object* v___x_3375_; 
v___x_3374_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__12));
v___x_3375_ = l_Lean_stringToMessageData(v___x_3374_);
return v___x_3375_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__15(void){
_start:
{
lean_object* v___x_3378_; lean_object* v___x_3379_; 
v___x_3378_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__14));
v___x_3379_ = l_Lean_MessageData_ofFormat(v___x_3378_);
return v___x_3379_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__17(void){
_start:
{
lean_object* v___x_3381_; lean_object* v___x_3382_; 
v___x_3381_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__16));
v___x_3382_ = l_Lean_stringToMessageData(v___x_3381_);
return v___x_3382_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__19(void){
_start:
{
lean_object* v___x_3384_; lean_object* v___x_3385_; 
v___x_3384_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__18));
v___x_3385_ = l_Lean_stringToMessageData(v___x_3384_);
return v___x_3385_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__21(void){
_start:
{
lean_object* v___x_3387_; lean_object* v___x_3388_; 
v___x_3387_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__20));
v___x_3388_ = l_Lean_stringToMessageData(v___x_3387_);
return v___x_3388_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__23(void){
_start:
{
lean_object* v___x_3390_; lean_object* v___x_3391_; 
v___x_3390_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__22));
v___x_3391_ = l_Lean_stringToMessageData(v___x_3390_);
return v___x_3391_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__25(void){
_start:
{
lean_object* v___x_3393_; lean_object* v___x_3394_; 
v___x_3393_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__24));
v___x_3394_ = l_Lean_stringToMessageData(v___x_3393_);
return v___x_3394_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__27(void){
_start:
{
lean_object* v___x_3396_; lean_object* v___x_3397_; 
v___x_3396_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__26));
v___x_3397_ = l_Lean_stringToMessageData(v___x_3396_);
return v___x_3397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkDeprecated(lean_object* v_declName_3398_, uint8_t v_allowSuggestion_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_){
_start:
{
lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v_a_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3578_; 
v___x_3405_ = ((lean_object*)(l_Lean_Linter_instInhabitedDeprecationEntry_default));
v___x_3406_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0(v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_);
v_a_3407_ = lean_ctor_get(v___x_3406_, 0);
v_isSharedCheck_3578_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3578_ == 0)
{
v___x_3409_ = v___x_3406_;
v_isShared_3410_ = v_isSharedCheck_3578_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_a_3407_);
lean_dec(v___x_3406_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3578_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v___x_3411_; uint8_t v___x_3412_; lean_object* v_extraMsg_3414_; lean_object* v___y_3415_; lean_object* v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3418_; 
v___x_3411_ = l_Lean_Linter_linter_deprecated;
v___x_3412_ = l_Lean_Linter_getLinterValue(v___x_3411_, v_a_3407_);
lean_dec(v_a_3407_);
if (v___x_3412_ == 0)
{
lean_object* v___x_3428_; lean_object* v___x_3430_; 
lean_dec(v_declName_3398_);
v___x_3428_ = lean_box(0);
if (v_isShared_3410_ == 0)
{
lean_ctor_set(v___x_3409_, 0, v___x_3428_);
v___x_3430_ = v___x_3409_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v___x_3428_);
v___x_3430_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
return v___x_3430_;
}
}
else
{
lean_object* v___x_3432_; lean_object* v_env_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; 
v___x_3432_ = lean_st_ref_get(v_a_3403_);
v_env_3433_ = lean_ctor_get(v___x_3432_, 0);
lean_inc_ref(v_env_3433_);
lean_dec(v___x_3432_);
v___x_3434_ = l_Lean_Linter_deprecatedAttr;
lean_inc(v_declName_3398_);
v___x_3435_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_3405_, v___x_3434_, v_env_3433_, v_declName_3398_);
if (lean_obj_tag(v___x_3435_) == 1)
{
lean_object* v_val_3436_; lean_object* v_text_x3f_3437_; 
lean_del_object(v___x_3409_);
v_val_3436_ = lean_ctor_get(v___x_3435_, 0);
lean_inc(v_val_3436_);
lean_dec_ref_known(v___x_3435_, 1);
v_text_x3f_3437_ = lean_ctor_get(v_val_3436_, 1);
if (lean_obj_tag(v_text_x3f_3437_) == 0)
{
lean_object* v_newName_x3f_3438_; 
v_newName_x3f_3438_ = lean_ctor_get(v_val_3436_, 0);
lean_inc(v_newName_x3f_3438_);
lean_dec(v_val_3436_);
if (lean_obj_tag(v_newName_x3f_3438_) == 0)
{
lean_object* v___x_3439_; 
v___x_3439_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__9);
v_extraMsg_3414_ = v___x_3439_;
v___y_3415_ = v_a_3400_;
v___y_3416_ = v_a_3401_;
v___y_3417_ = v_a_3402_;
v___y_3418_ = v_a_3403_;
goto v___jp_3413_;
}
else
{
lean_object* v_val_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v_env_3447_; lean_object* v___x_3448_; uint8_t v___x_3449_; lean_object* v___x_3450_; 
v_val_3440_ = lean_ctor_get(v_newName_x3f_3438_, 0);
lean_inc_n(v_val_3440_, 2);
lean_dec_ref_known(v_newName_x3f_3438_, 1);
v___x_3441_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__3, &l_Lean_Linter_checkDeprecated___closed__3_once, _init_l_Lean_Linter_checkDeprecated___closed__3);
v___x_3442_ = l_Lean_MessageData_ofConstName(v_val_3440_, v___x_3412_);
lean_inc_ref(v___x_3442_);
v___x_3443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3443_, 0, v___x_3441_);
lean_ctor_set(v___x_3443_, 1, v___x_3442_);
v___x_3444_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__57_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__57_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__57_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_3445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3445_, 0, v___x_3443_);
lean_ctor_set(v___x_3445_, 1, v___x_3444_);
v___x_3446_ = lean_st_ref_get(v_a_3403_);
v_env_3447_ = lean_ctor_get(v___x_3446_, 0);
lean_inc_ref_n(v_env_3447_, 2);
lean_dec(v___x_3446_);
v___x_3448_ = l_Lean_Name_getPrefix(v_declName_3398_);
v___x_3449_ = 0;
lean_inc(v_declName_3398_);
v___x_3450_ = l_Lean_Environment_find_x3f(v_env_3447_, v_declName_3398_, v___x_3449_);
if (lean_obj_tag(v___x_3450_) == 1)
{
lean_object* v_val_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; 
v_val_3451_ = lean_ctor_get(v___x_3450_, 0);
lean_inc(v_val_3451_);
lean_dec_ref_known(v___x_3450_, 1);
v___x_3452_ = l_Lean_Name_getPrefix(v_val_3440_);
lean_inc(v_val_3440_);
lean_inc_ref(v_env_3447_);
v___x_3453_ = l_Lean_Environment_find_x3f(v_env_3447_, v_val_3440_, v___x_3449_);
if (lean_obj_tag(v___x_3453_) == 1)
{
lean_object* v_val_3454_; lean_object* v___x_3455_; 
v_val_3454_ = lean_ctor_get(v___x_3453_, 0);
lean_inc(v_val_3454_);
lean_dec_ref_known(v___x_3453_, 1);
v___x_3455_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq(v_val_3451_, v_val_3454_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_);
if (lean_obj_tag(v___x_3455_) == 0)
{
lean_object* v_a_3456_; lean_object* v_msg_3458_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v___y_3461_; lean_object* v___y_3462_; lean_object* v___y_3477_; lean_object* v___y_3478_; lean_object* v___y_3479_; lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v___y_3497_; lean_object* v___y_3498_; lean_object* v___y_3499_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3510_; lean_object* v___y_3511_; uint8_t v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; uint8_t v___y_3516_; lean_object* v_msg_3543_; lean_object* v___y_3544_; lean_object* v___y_3545_; lean_object* v___y_3546_; lean_object* v___y_3547_; uint8_t v___x_3550_; 
v_a_3456_ = lean_ctor_get(v___x_3455_, 0);
lean_inc(v_a_3456_);
lean_dec_ref_known(v___x_3455_, 1);
v___x_3550_ = lean_unbox(v_a_3456_);
if (v___x_3550_ == 0)
{
if (v___x_3412_ == 0)
{
lean_dec(v_val_3454_);
lean_dec(v_val_3451_);
v_msg_3543_ = v___x_3445_;
v___y_3544_ = v_a_3400_;
v___y_3545_ = v_a_3401_;
v___y_3546_ = v_a_3402_;
v___y_3547_ = v_a_3403_;
goto v___jp_3542_;
}
else
{
lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; 
v___x_3551_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_3552_ = l_Lean_ConstantInfo_type(v_val_3454_);
lean_dec(v_val_3454_);
v___x_3553_ = l_Lean_indentExpr(v___x_3552_);
v___x_3554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3554_, 0, v___x_3551_);
lean_ctor_set(v___x_3554_, 1, v___x_3553_);
v___x_3555_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_3556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3556_, 0, v___x_3554_);
lean_ctor_set(v___x_3556_, 1, v___x_3555_);
v___x_3557_ = l_Lean_ConstantInfo_type(v_val_3451_);
lean_dec(v_val_3451_);
v___x_3558_ = l_Lean_indentExpr(v___x_3557_);
v___x_3559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3559_, 0, v___x_3556_);
lean_ctor_set(v___x_3559_, 1, v___x_3558_);
v___x_3560_ = l_Lean_MessageData_note(v___x_3559_);
v___x_3561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3561_, 0, v___x_3445_);
lean_ctor_set(v___x_3561_, 1, v___x_3560_);
v_msg_3543_ = v___x_3561_;
v___y_3544_ = v_a_3400_;
v___y_3545_ = v_a_3401_;
v___y_3546_ = v_a_3402_;
v___y_3547_ = v_a_3403_;
goto v___jp_3542_;
}
}
else
{
lean_dec(v_val_3454_);
lean_dec(v_val_3451_);
v_msg_3543_ = v___x_3445_;
v___y_3544_ = v_a_3400_;
v___y_3545_ = v_a_3401_;
v___y_3546_ = v_a_3402_;
v___y_3547_ = v_a_3403_;
goto v___jp_3542_;
}
v___jp_3457_:
{
if (v_allowSuggestion_3399_ == 0)
{
lean_dec(v_a_3456_);
lean_dec(v_val_3440_);
v_extraMsg_3414_ = v_msg_3458_;
v___y_3415_ = v___y_3459_;
v___y_3416_ = v___y_3460_;
v___y_3417_ = v___y_3461_;
v___y_3418_ = v___y_3462_;
goto v___jp_3413_;
}
else
{
uint8_t v___x_3463_; 
v___x_3463_ = lean_unbox(v_a_3456_);
lean_dec(v_a_3456_);
if (v___x_3463_ == 0)
{
lean_dec(v_val_3440_);
v_extraMsg_3414_ = v_msg_3458_;
v___y_3415_ = v___y_3459_;
v___y_3416_ = v___y_3460_;
v___y_3417_ = v___y_3461_;
v___y_3418_ = v___y_3462_;
goto v___jp_3413_;
}
else
{
lean_object* v___x_3464_; 
lean_inc(v_declName_3398_);
v___x_3464_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f(v_declName_3398_, v_val_3440_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_);
if (lean_obj_tag(v___x_3464_) == 0)
{
lean_object* v_a_3465_; 
v_a_3465_ = lean_ctor_get(v___x_3464_, 0);
lean_inc(v_a_3465_);
lean_dec_ref_known(v___x_3464_, 1);
if (lean_obj_tag(v_a_3465_) == 1)
{
lean_object* v_val_3466_; lean_object* v___x_3467_; 
v_val_3466_ = lean_ctor_get(v_a_3465_, 0);
lean_inc(v_val_3466_);
lean_dec_ref_known(v_a_3465_, 1);
v___x_3467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3467_, 0, v_msg_3458_);
lean_ctor_set(v___x_3467_, 1, v_val_3466_);
v_extraMsg_3414_ = v___x_3467_;
v___y_3415_ = v___y_3459_;
v___y_3416_ = v___y_3460_;
v___y_3417_ = v___y_3461_;
v___y_3418_ = v___y_3462_;
goto v___jp_3413_;
}
else
{
lean_dec(v_a_3465_);
v_extraMsg_3414_ = v_msg_3458_;
v___y_3415_ = v___y_3459_;
v___y_3416_ = v___y_3460_;
v___y_3417_ = v___y_3461_;
v___y_3418_ = v___y_3462_;
goto v___jp_3413_;
}
}
else
{
lean_object* v_a_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3475_; 
lean_dec_ref(v_msg_3458_);
lean_dec(v_declName_3398_);
v_a_3468_ = lean_ctor_get(v___x_3464_, 0);
v_isSharedCheck_3475_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3475_ == 0)
{
v___x_3470_ = v___x_3464_;
v_isShared_3471_ = v_isSharedCheck_3475_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_a_3468_);
lean_dec(v___x_3464_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3475_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
lean_object* v___x_3473_; 
if (v_isShared_3471_ == 0)
{
v___x_3473_ = v___x_3470_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v_a_3468_);
v___x_3473_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
return v___x_3473_;
}
}
}
}
}
}
v___jp_3476_:
{
lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; 
v___x_3483_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_3484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3484_, 0, v___x_3483_);
lean_ctor_set(v___x_3484_, 1, v___x_3442_);
v___x_3485_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__5, &l_Lean_Linter_checkDeprecated___closed__5_once, _init_l_Lean_Linter_checkDeprecated___closed__5);
v___x_3486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3486_, 0, v___x_3484_);
lean_ctor_set(v___x_3486_, 1, v___x_3485_);
v___x_3487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3487_, 0, v___x_3486_);
lean_ctor_set(v___x_3487_, 1, v___y_3482_);
v___x_3488_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__7, &l_Lean_Linter_checkDeprecated___closed__7_once, _init_l_Lean_Linter_checkDeprecated___closed__7);
v___x_3489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3489_, 0, v___x_3487_);
lean_ctor_set(v___x_3489_, 1, v___x_3488_);
v___x_3490_ = l_Lean_MessageData_ofName(v___x_3452_);
v___x_3491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3491_, 0, v___x_3489_);
lean_ctor_set(v___x_3491_, 1, v___x_3490_);
v___x_3492_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__9, &l_Lean_Linter_checkDeprecated___closed__9_once, _init_l_Lean_Linter_checkDeprecated___closed__9);
v___x_3493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3493_, 0, v___x_3491_);
lean_ctor_set(v___x_3493_, 1, v___x_3492_);
v___x_3494_ = l_Lean_MessageData_note(v___x_3493_);
v___x_3495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3495_, 0, v___y_3478_);
lean_ctor_set(v___x_3495_, 1, v___x_3494_);
v_msg_3458_ = v___x_3495_;
v___y_3459_ = v___y_3477_;
v___y_3460_ = v___y_3481_;
v___y_3461_ = v___y_3479_;
v___y_3462_ = v___y_3480_;
goto v___jp_3457_;
}
v___jp_3496_:
{
lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; 
v___x_3503_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__11, &l_Lean_Linter_checkDeprecated___closed__11_once, _init_l_Lean_Linter_checkDeprecated___closed__11);
v___x_3504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3504_, 0, v___x_3503_);
lean_ctor_set(v___x_3504_, 1, v___y_3502_);
v___x_3505_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__13, &l_Lean_Linter_checkDeprecated___closed__13_once, _init_l_Lean_Linter_checkDeprecated___closed__13);
v___x_3506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3506_, 0, v___x_3504_);
lean_ctor_set(v___x_3506_, 1, v___x_3505_);
v___x_3507_ = l_Lean_MessageData_note(v___x_3506_);
v___x_3508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3508_, 0, v___y_3498_);
lean_ctor_set(v___x_3508_, 1, v___x_3507_);
v_msg_3458_ = v___x_3508_;
v___y_3459_ = v___y_3497_;
v___y_3460_ = v___y_3501_;
v___y_3461_ = v___y_3499_;
v___y_3462_ = v___y_3500_;
goto v___jp_3457_;
}
v___jp_3509_:
{
if (v___y_3516_ == 0)
{
uint8_t v___x_3517_; 
lean_inc(v_declName_3398_);
lean_inc_ref(v_env_3447_);
v___x_3517_ = l_Lean_isProtected(v_env_3447_, v_declName_3398_);
if (v___x_3517_ == 0)
{
if (v___x_3412_ == 0)
{
lean_dec(v___x_3452_);
lean_dec_ref(v_env_3447_);
lean_dec_ref(v___x_3442_);
v_msg_3458_ = v___y_3511_;
v___y_3459_ = v___y_3510_;
v___y_3460_ = v___y_3515_;
v___y_3461_ = v___y_3513_;
v___y_3462_ = v___y_3514_;
goto v___jp_3457_;
}
else
{
uint8_t v___x_3518_; 
lean_inc(v_val_3440_);
v___x_3518_ = l_Lean_isProtected(v_env_3447_, v_val_3440_);
if (v___x_3518_ == 0)
{
lean_dec(v___x_3452_);
lean_dec_ref(v___x_3442_);
v_msg_3458_ = v___y_3511_;
v___y_3459_ = v___y_3510_;
v___y_3460_ = v___y_3515_;
v___y_3461_ = v___y_3513_;
v___y_3462_ = v___y_3514_;
goto v___jp_3457_;
}
else
{
lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; uint8_t v___x_3522_; 
lean_inc(v___x_3452_);
v___x_3519_ = l_Lean_Name_componentsRev(v___x_3452_);
v___x_3520_ = lean_unsigned_to_nat(1u);
v___x_3521_ = l_List_lengthTR___redArg(v___x_3519_);
v___x_3522_ = lean_nat_dec_lt(v___x_3520_, v___x_3521_);
lean_dec(v___x_3521_);
if (v___x_3522_ == 0)
{
lean_object* v___x_3523_; 
lean_dec(v___x_3519_);
v___x_3523_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__15, &l_Lean_Linter_checkDeprecated___closed__15_once, _init_l_Lean_Linter_checkDeprecated___closed__15);
v___y_3477_ = v___y_3510_;
v___y_3478_ = v___y_3511_;
v___y_3479_ = v___y_3513_;
v___y_3480_ = v___y_3514_;
v___y_3481_ = v___y_3515_;
v___y_3482_ = v___x_3523_;
goto v___jp_3476_;
}
else
{
lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; 
v___x_3524_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__17, &l_Lean_Linter_checkDeprecated___closed__17_once, _init_l_Lean_Linter_checkDeprecated___closed__17);
v___x_3525_ = lean_unsigned_to_nat(0u);
v___x_3526_ = l_List_get___redArg(v___x_3519_, v___x_3525_);
lean_dec(v___x_3519_);
v___x_3527_ = l_Lean_MessageData_ofName(v___x_3526_);
v___x_3528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3528_, 0, v___x_3524_);
lean_ctor_set(v___x_3528_, 1, v___x_3527_);
v___x_3529_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__19, &l_Lean_Linter_checkDeprecated___closed__19_once, _init_l_Lean_Linter_checkDeprecated___closed__19);
v___x_3530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3530_, 0, v___x_3528_);
lean_ctor_set(v___x_3530_, 1, v___x_3529_);
v___y_3477_ = v___y_3510_;
v___y_3478_ = v___y_3511_;
v___y_3479_ = v___y_3513_;
v___y_3480_ = v___y_3514_;
v___y_3481_ = v___y_3515_;
v___y_3482_ = v___x_3530_;
goto v___jp_3476_;
}
}
}
}
else
{
lean_dec(v___x_3452_);
lean_dec_ref(v_env_3447_);
lean_dec_ref(v___x_3442_);
v_msg_3458_ = v___y_3511_;
v___y_3459_ = v___y_3510_;
v___y_3460_ = v___y_3515_;
v___y_3461_ = v___y_3513_;
v___y_3462_ = v___y_3514_;
goto v___jp_3457_;
}
}
else
{
lean_dec(v___x_3452_);
lean_dec_ref(v_env_3447_);
lean_dec_ref(v___x_3442_);
if (lean_obj_tag(v_declName_3398_) == 1)
{
lean_object* v_str_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; 
v_str_3531_ = lean_ctor_get(v_declName_3398_, 1);
v___x_3532_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__21, &l_Lean_Linter_checkDeprecated___closed__21_once, _init_l_Lean_Linter_checkDeprecated___closed__21);
lean_inc_ref(v_str_3531_);
v___x_3533_ = l_Lean_stringToMessageData(v_str_3531_);
v___x_3534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3534_, 0, v___x_3532_);
lean_ctor_set(v___x_3534_, 1, v___x_3533_);
v___x_3535_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__23, &l_Lean_Linter_checkDeprecated___closed__23_once, _init_l_Lean_Linter_checkDeprecated___closed__23);
v___x_3536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3536_, 0, v___x_3534_);
lean_ctor_set(v___x_3536_, 1, v___x_3535_);
lean_inc(v_val_3440_);
v___x_3537_ = l_Lean_MessageData_ofConstName(v_val_3440_, v___y_3512_);
v___x_3538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3538_, 0, v___x_3536_);
lean_ctor_set(v___x_3538_, 1, v___x_3537_);
v___x_3539_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__25, &l_Lean_Linter_checkDeprecated___closed__25_once, _init_l_Lean_Linter_checkDeprecated___closed__25);
v___x_3540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3540_, 0, v___x_3538_);
lean_ctor_set(v___x_3540_, 1, v___x_3539_);
v___y_3497_ = v___y_3510_;
v___y_3498_ = v___y_3511_;
v___y_3499_ = v___y_3513_;
v___y_3500_ = v___y_3514_;
v___y_3501_ = v___y_3515_;
v___y_3502_ = v___x_3540_;
goto v___jp_3496_;
}
else
{
lean_object* v___x_3541_; 
v___x_3541_ = l_Lean_MessageData_nil;
v___y_3497_ = v___y_3510_;
v___y_3498_ = v___y_3511_;
v___y_3499_ = v___y_3513_;
v___y_3500_ = v___y_3514_;
v___y_3501_ = v___y_3515_;
v___y_3502_ = v___x_3541_;
goto v___jp_3496_;
}
}
}
v___jp_3542_:
{
uint8_t v___x_3548_; 
v___x_3548_ = l_Lean_Name_isAnonymous(v___x_3448_);
if (v___x_3548_ == 0)
{
uint8_t v___x_3549_; 
v___x_3549_ = lean_name_eq(v___x_3448_, v___x_3452_);
lean_dec(v___x_3448_);
if (v___x_3549_ == 0)
{
v___y_3510_ = v___y_3544_;
v___y_3511_ = v_msg_3543_;
v___y_3512_ = v___x_3548_;
v___y_3513_ = v___y_3546_;
v___y_3514_ = v___y_3547_;
v___y_3515_ = v___y_3545_;
v___y_3516_ = v___x_3412_;
goto v___jp_3509_;
}
else
{
v___y_3510_ = v___y_3544_;
v___y_3511_ = v_msg_3543_;
v___y_3512_ = v___x_3548_;
v___y_3513_ = v___y_3546_;
v___y_3514_ = v___y_3547_;
v___y_3515_ = v___y_3545_;
v___y_3516_ = v___x_3548_;
goto v___jp_3509_;
}
}
else
{
lean_dec(v___x_3452_);
lean_dec(v___x_3448_);
lean_dec_ref(v_env_3447_);
lean_dec_ref(v___x_3442_);
v_msg_3458_ = v_msg_3543_;
v___y_3459_ = v___y_3544_;
v___y_3460_ = v___y_3545_;
v___y_3461_ = v___y_3546_;
v___y_3462_ = v___y_3547_;
goto v___jp_3457_;
}
}
}
else
{
lean_object* v_a_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3569_; 
lean_dec(v_val_3454_);
lean_dec(v___x_3452_);
lean_dec(v_val_3451_);
lean_dec(v___x_3448_);
lean_dec_ref(v_env_3447_);
lean_dec_ref_known(v___x_3445_, 2);
lean_dec_ref(v___x_3442_);
lean_dec(v_val_3440_);
lean_dec(v_declName_3398_);
v_a_3562_ = lean_ctor_get(v___x_3455_, 0);
v_isSharedCheck_3569_ = !lean_is_exclusive(v___x_3455_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3564_ = v___x_3455_;
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_a_3562_);
lean_dec(v___x_3455_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v___x_3567_; 
if (v_isShared_3565_ == 0)
{
v___x_3567_ = v___x_3564_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_a_3562_);
v___x_3567_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
return v___x_3567_;
}
}
}
}
else
{
lean_dec(v___x_3453_);
lean_dec(v___x_3452_);
lean_dec(v_val_3451_);
lean_dec(v___x_3448_);
lean_dec_ref(v_env_3447_);
lean_dec_ref(v___x_3442_);
lean_dec(v_val_3440_);
v_extraMsg_3414_ = v___x_3445_;
v___y_3415_ = v_a_3400_;
v___y_3416_ = v_a_3401_;
v___y_3417_ = v_a_3402_;
v___y_3418_ = v_a_3403_;
goto v___jp_3413_;
}
}
else
{
lean_dec(v___x_3450_);
lean_dec(v___x_3448_);
lean_dec_ref(v_env_3447_);
lean_dec_ref(v___x_3442_);
lean_dec(v_val_3440_);
v_extraMsg_3414_ = v___x_3445_;
v___y_3415_ = v_a_3400_;
v___y_3416_ = v_a_3401_;
v___y_3417_ = v_a_3402_;
v___y_3418_ = v_a_3403_;
goto v___jp_3413_;
}
}
}
else
{
lean_object* v_val_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; 
lean_inc_ref(v_text_x3f_3437_);
lean_dec(v_val_3436_);
v_val_3570_ = lean_ctor_get(v_text_x3f_3437_, 0);
lean_inc(v_val_3570_);
lean_dec_ref_known(v_text_x3f_3437_, 1);
v___x_3571_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__27, &l_Lean_Linter_checkDeprecated___closed__27_once, _init_l_Lean_Linter_checkDeprecated___closed__27);
v___x_3572_ = l_Lean_stringToMessageData(v_val_3570_);
v___x_3573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3573_, 0, v___x_3571_);
lean_ctor_set(v___x_3573_, 1, v___x_3572_);
v_extraMsg_3414_ = v___x_3573_;
v___y_3415_ = v_a_3400_;
v___y_3416_ = v_a_3401_;
v___y_3417_ = v_a_3402_;
v___y_3418_ = v_a_3403_;
goto v___jp_3413_;
}
}
else
{
lean_object* v___x_3574_; lean_object* v___x_3576_; 
lean_dec(v___x_3435_);
lean_dec(v_declName_3398_);
v___x_3574_ = lean_box(0);
if (v_isShared_3410_ == 0)
{
lean_ctor_set(v___x_3409_, 0, v___x_3574_);
v___x_3576_ = v___x_3409_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v___x_3574_);
v___x_3576_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
return v___x_3576_;
}
}
}
v___jp_3413_:
{
lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; 
v___x_3419_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_3420_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_3421_ = l_Lean_MessageData_ofConstName(v_declName_3398_, v___x_3412_);
v___x_3422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3422_, 0, v___x_3420_);
lean_ctor_set(v___x_3422_, 1, v___x_3421_);
v___x_3423_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__1, &l_Lean_Linter_checkDeprecated___closed__1_once, _init_l_Lean_Linter_checkDeprecated___closed__1);
v___x_3424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3424_, 0, v___x_3422_);
lean_ctor_set(v___x_3424_, 1, v___x_3423_);
v___x_3425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3425_, 0, v___x_3424_);
lean_ctor_set(v___x_3425_, 1, v_extraMsg_3414_);
v___x_3426_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3426_, 0, v___x_3419_);
lean_ctor_set(v___x_3426_, 1, v___x_3425_);
v___x_3427_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38(v___x_3426_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_);
return v___x_3427_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkDeprecated___boxed(lean_object* v_declName_3579_, lean_object* v_allowSuggestion_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_, lean_object* v_a_3585_){
_start:
{
uint8_t v_allowSuggestion_boxed_3586_; lean_object* v_res_3587_; 
v_allowSuggestion_boxed_3586_ = lean_unbox(v_allowSuggestion_3580_);
v_res_3587_ = l_Lean_Linter_checkDeprecated(v_declName_3579_, v_allowSuggestion_boxed_3586_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_);
lean_dec(v_a_3584_);
lean_dec_ref(v_a_3583_);
lean_dec(v_a_3582_);
lean_dec_ref(v_a_3581_);
return v_res_3587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0(lean_object* v_o_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_){
_start:
{
lean_object* v___x_3594_; 
v___x_3594_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(v_o_3588_, v___y_3592_);
return v___x_3594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___boxed(lean_object* v_o_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_){
_start:
{
lean_object* v_res_3601_; 
v_res_3601_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0(v_o_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_);
lean_dec(v___y_3599_);
lean_dec_ref(v___y_3598_);
lean_dec(v___y_3597_);
lean_dec_ref(v___y_3596_);
return v_res_3601_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Init(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_InfoTree_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_ExtraModUses(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Hint(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_MapIdx(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_Deprecated(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_InfoTree_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ExtraModUses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Hint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_MapIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_linter_deprecated = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_linter_deprecated);
lean_dec_ref(res);
res = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_linter_deprecated_deprecatedTarget = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_linter_deprecated_deprecatedTarget);
lean_dec_ref(res);
res = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_deprecatedAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_deprecatedAttr);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Linter_Deprecated(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_Linter_Init(uint8_t builtin);
lean_object* initialize_Lean_Elab_InfoTree_Main(uint8_t builtin);
lean_object* initialize_Lean_ExtraModUses(uint8_t builtin);
lean_object* initialize_Lean_Meta_Hint(uint8_t builtin);
lean_object* initialize_Init_Data_List_MapIdx(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Linter_Deprecated(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_InfoTree_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ExtraModUses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Hint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_MapIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Deprecated(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Linter_Deprecated(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Linter_Deprecated(builtin);
}
#ifdef __cplusplus
}
#endif
