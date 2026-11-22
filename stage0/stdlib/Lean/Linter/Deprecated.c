// Lean compiler output
// Module: Lean.Linter.Deprecated
// Imports: public import Lean.Meta.Basic import Lean.Linter.Init import Lean.Elab.InfoTree.Main import Lean.ExtraModUses public import Lean.Meta.Hint import Init.Data.List.MapIdx import Init.Omega import Std.Time.Format import Std.Time.Zoned
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getSubstring_x3f(lean_object*, uint8_t, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_Syntax_instInhabitedRange_default;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Core_shouldCheckDeprecated___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
extern lean_object* l_Lean_Linter_linterSetsExt;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_registerParametricAttributeExt___redArg(lean_object*, uint8_t, lean_object*, uint8_t);
lean_object* lean_get_current_time();
lean_object* l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_TimeZone_ZoneRules_timezoneAt(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Std_Time_Duration_ofNanoseconds(lean_object*);
lean_object* l_Std_Time_PlainDateTime_ofWallTime(lean_object*);
lean_object* lean_mk_thunk(lean_object*);
lean_object* lean_thunk_get_own(lean_object*);
lean_object* l_Std_Time_Database_defaultGetLocalZoneRules();
lean_object* l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForTimestamp(lean_object*, lean_object*);
lean_object* l_Std_Time_TimeZone_LocalTimeType_getTimeZone(lean_object*);
lean_object* l_Std_Time_PlainDate_toLeanDateString(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Syntax_ofRange(lean_object*, uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_hint(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_TSyntax_getString(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_MessageData_hint_x27(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_ConstantVal_instantiateTypeLevelParams(lean_object*, lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited___redArg();
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
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
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_extractMacroScopes(lean_object*);
lean_object* l_Lean_MacroScopesView_review(lean_object*);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MacroScopesView_isSuffixOf(lean_object*, lean_object*);
lean_object* l_Lean_privateToUserName_x3f(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
extern lean_object* l_Lean_ResolveName_backward_privateInPublic_warn;
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_Name_revIter(lean_object*);
lean_object* l_Lean_Name_appendCore(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
extern lean_object* l_Lean_rootNamespace;
lean_object* l_Lean_getRevAliases(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Name_getPrefix(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_registerParametricAttributeForExt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isProtected(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_ParametricAttribute_setParam___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___redArg(lean_object*, lean_object*);
lean_object* l_Lean_getStructureInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqConstantKind_beq(uint8_t, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_Lean_Environment_getProjectionFnInfo_x3f(lean_object*, lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
lean_object* l_Lean_isAutomationAttrGuardedBy(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
extern lean_object* l_Lean_Core_checkDeprecatedAtRef;
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_448960154____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "automationAttr"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_448960154____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_448960154____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_448960154____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_448960154____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_448960154____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(227, 99, 57, 49, 46, 156, 253, 187)}};
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_448960154____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_448960154____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_448960154____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(217, 84, 237, 209, 188, 30, 211, 88)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_448960154____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_448960154____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_448960154____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 156, .m_capacity = 156, .m_length = 155, .m_data = "if true, warn when a deprecated declaration is tagged with an attribute such as `simp` or `grind` that lets automation use it without a deprecation warning"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_448960154____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_448960154____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_448960154____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_448960154____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_448960154____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_448960154____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_448960154____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_448960154____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_448960154____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_448960154____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_448960154____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(53, 243, 121, 207, 53, 172, 203, 87)}};
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_448960154____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_448960154____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(248, 165, 85, 201, 27, 48, 185, 203)}};
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_448960154____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_448960154____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_448960154____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(198, 7, 73, 175, 190, 222, 124, 201)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_448960154____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_448960154____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_448960154____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_448960154____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_linter_deprecated_automationAttr;
static const lean_ctor_object l_Lean_Linter_instInhabitedDeprecationEntry_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Linter_instInhabitedDeprecationEntry_default___closed__0 = (const lean_object*)&l_Lean_Linter_instInhabitedDeprecationEntry_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_instInhabitedDeprecationEntry_default = (const lean_object*)&l_Lean_Linter_instInhabitedDeprecationEntry_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_instInhabitedDeprecationEntry = (const lean_object*)&l_Lean_Linter_instInhabitedDeprecationEntry_default___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate_spec__2(lean_object*);
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___lam__0___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__0;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "UTC"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__1 = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__1_value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__1_value)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__2 = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__2_value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate_spec__0(lean_object*);
static const lean_string_object l_Lean_Linter_mkSinceHint___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Try this: "};
static const lean_object* l_Lean_Linter_mkSinceHint___lam__0___closed__0 = (const lean_object*)&l_Lean_Linter_mkSinceHint___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Linter_mkSinceHint___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_mkSinceHint___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_mkSinceHint___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "(since := \""};
static const lean_object* l_Lean_Linter_mkSinceHint___closed__0 = (const lean_object*)&l_Lean_Linter_mkSinceHint___closed__0_value;
static const lean_string_object l_Lean_Linter_mkSinceHint___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\")"};
static const lean_object* l_Lean_Linter_mkSinceHint___closed__1 = (const lean_object*)&l_Lean_Linter_mkSinceHint___closed__1_value;
static const lean_string_object l_Lean_Linter_mkSinceHint___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Add the current date:"};
static const lean_object* l_Lean_Linter_mkSinceHint___closed__2 = (const lean_object*)&l_Lean_Linter_mkSinceHint___closed__2_value;
static const lean_ctor_object l_Lean_Linter_mkSinceHint___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Linter_mkSinceHint___closed__2_value)}};
static const lean_object* l_Lean_Linter_mkSinceHint___closed__3 = (const lean_object*)&l_Lean_Linter_mkSinceHint___closed__3_value;
static lean_once_cell_t l_Lean_Linter_mkSinceHint___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_mkSinceHint___closed__4;
static const lean_string_object l_Lean_Linter_mkSinceHint___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_Linter_mkSinceHint___closed__5 = (const lean_object*)&l_Lean_Linter_mkSinceHint___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Linter_mkSinceHint(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_mkSinceHint___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__0_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Try this: +typeChanged"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__0_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__0_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__3_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__3_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14_spec__19___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__0;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__1;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__2;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__3_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__4 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__4_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__7_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__8;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__9;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__10 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__10_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__10_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__13_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__14;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__15;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__16_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__18_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__19_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__6___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2___closed__0;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__4_spec__10___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__4_spec__10___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__4_spec__10___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__4_spec__10___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__33(lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__33___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44_spec__46_spec__49(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44_spec__46_spec__49___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46_spec__48_spec__50___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46_spec__48_spec__50___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46_spec__48_spec__50___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46_spec__48_spec__50(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46_spec__48_spec__50___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46_spec__48(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46_spec__48___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__45___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__45___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Private declaration `"};
static const lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___closed__0 = (const lean_object*)&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___closed__0_value;
static lean_once_cell_t l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___closed__1;
static const lean_string_object l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 167, .m_capacity = 167, .m_length = 166, .m_data = "` accessed publicly; this is allowed only because the `backward.privateInPublic` option is enabled. \n\nDisable `backward.privateInPublic.warn` to silence this warning."};
static const lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___closed__2 = (const lean_object*)&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___closed__2_value;
static lean_once_cell_t l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___closed__3;
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24___lam__0___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27___closed__0 = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27___closed__0_value;
static const lean_closure_object l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24___lam__0___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46_spec__48_spec__50___closed__0_value)} };
static const lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27___closed__1 = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24_spec__32___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24_spec__32___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24___closed__0 = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__26(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14___closed__0 = (const lean_object*)&l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_any___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__29(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__29___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__39___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__39___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44_spec__46(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44_spec__46___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__25___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__25___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26_spec__30___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26_spec__30___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__19___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__19___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23_spec__26___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23_spec__26___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6___lam__0___boxed, .m_arity = 7, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6___closed__0 = (const lean_object*)&l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__0_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 134, .m_capacity = 134, .m_length = 133, .m_data = "`[deprecated]` attribute should specify the date or library version at which the deprecation was introduced, using `(since := \"...\")`"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__0_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__0_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__1_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__1_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__2_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 83, .m_capacity = 83, .m_length = 82, .m_data = "`[deprecated]` attribute should specify either a new name or a deprecation message"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__2_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__2_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__3_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__2_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__3_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__3_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__4_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__4_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__5_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "The updated constant has a different type:"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__5_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__5_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "\ninstead of"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 372, .m_capacity = 372, .m_length = 371, .m_data = "\n\nThis suggests that addressing the deprecation might be more involved than simply replacing the old name with the new name. This is often expected, but sometimes it indicates that the deprecation is in favor of the wrong declaration, or that there is a mistake in one of the statements.\n\nIf the type difference is intentional, use `+typeChanged` to silence this warning."};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__10_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__10_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__11_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Add `+typeChanged` to silence this warning."};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__11_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__11_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__12_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__11_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__12_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__12_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__13_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__13_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__14_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__14_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__15_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Invalid `[deprecated]` attribute syntax"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__15_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__15_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Add `+typeChanged`:"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__18_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__18_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__18_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__19_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__19_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__20_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " +typeChanged"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__20_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__20_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__21_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__20_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__21_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__21_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__22_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "+typeChanged"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__22_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__22_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__23_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__22_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__23_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__23_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__24_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__24_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__25_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__25_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__27_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__27_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_;
static const lean_array_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__28_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__28_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__28_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 88, .m_capacity = 88, .m_length = 87, .m_data = "The `+typeChanged` marker is not needed because the updated constant has the same type."};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__36_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__36_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__36_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__37_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__37_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__38_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "This warning can be disabled with `set_option "};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__38_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__38_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__39_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__39_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__40_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " false`"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__40_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__40_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = "` is itself deprecated, but without an explicit replacement; `"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "` is being deprecated in favor of a deprecated declaration"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__47_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__47_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__48_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "` is itself deprecated in favor of `"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__48_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__48_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__49_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__49_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__50_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "`; consider deprecating `"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__50_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__50_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__51_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__51_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__52_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "` in favor of `"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__52_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__52_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__53_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__53_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__54_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` instead"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__54_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__54_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__55_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__55_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__56_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Deprecate in favor of `"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__56_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__56_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__57_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__57_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__58_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "` instead:"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__58_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__58_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__59_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__59_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__60_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Invalid `[deprecated]` attribute: `"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__60_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__60_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__61_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__61_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__62_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "` cannot be deprecated in favor of itself"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__62_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__62_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__63_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__63_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "deprecatedAttr"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(85, 246, 23, 143, 159, 138, 155, 162)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(78, 182, 79, 155, 204, 118, 39, 140)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "mark declaration as deprecated"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__3_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__4_spec__10(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__4___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__4___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__6_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__6_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__19(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__19___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24_spec__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24_spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23_spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26_spec__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26_spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__39(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__39___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__45(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__45___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Linter_DeprecationHint_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_DeprecationHint_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_DeprecationHint_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_DeprecationHint_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_DeprecationHint_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_DeprecationHint_none_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_DeprecationHint_none_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_DeprecationHint_ident_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_DeprecationHint_ident_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_DeprecationHint_custom_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_DeprecationHint_custom_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_mkReplacementHint___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Replace the deprecated name:"};
static const lean_object* l_Lean_Linter_mkReplacementHint___redArg___closed__0 = (const lean_object*)&l_Lean_Linter_mkReplacementHint___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Linter_mkReplacementHint___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_mkReplacementHint___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Linter_mkReplacementHint___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_mkReplacementHint___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_mkReplacementHint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_mkReplacementHint___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___00List_beq___at___00Lean_Linter_mkIdentHint_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00List_beq___at___00Lean_Linter_mkIdentHint_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Linter_mkIdentHint_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Linter_mkIdentHint_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_mkIdentHint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_mkIdentHint___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Linter_checkDeprecated_spec__1___redArg(lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Linter_checkDeprecated___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__1_value)}};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__10 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__10_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__11;
static const lean_string_object l_Lean_Linter_checkDeprecated___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 86, .m_capacity = 86, .m_length = 85, .m_data = "The updated constant is in a different namespace. Dot notation may need to be changed"};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__12 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__12_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__13;
static const lean_string_object l_Lean_Linter_checkDeprecated___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__14 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__14_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__15;
static const lean_string_object l_Lean_Linter_checkDeprecated___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = " (e.g., from `x."};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__16 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__16_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__17;
static const lean_string_object l_Lean_Linter_checkDeprecated___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "` to `"};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__18 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__18_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__19;
static const lean_string_object l_Lean_Linter_checkDeprecated___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " x`)"};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__20 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__20_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__21;
static const lean_string_object l_Lean_Linter_checkDeprecated___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "at least the last component `"};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__22 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__22_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__23;
static const lean_string_object l_Lean_Linter_checkDeprecated___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "` of "};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__24 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__24_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__25;
static const lean_string_object l_Lean_Linter_checkDeprecated___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__26 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__26_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__27;
LEAN_EXPORT lean_object* l_Lean_Linter_checkDeprecated(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_checkDeprecated___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Linter_checkDeprecated_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_checkDeprecatedAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_checkDeprecatedAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_mkListRemovalSuggestion_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_mkListRemovalSuggestion_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Linter_mkListRemovalSuggestion___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__1_value)}};
static const lean_object* l_Lean_Linter_mkListRemovalSuggestion___redArg___closed__0 = (const lean_object*)&l_Lean_Linter_mkListRemovalSuggestion___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Linter_mkListRemovalSuggestion___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Linter_mkListRemovalSuggestion___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Linter_mkListRemovalSuggestion___redArg___closed__1 = (const lean_object*)&l_Lean_Linter_mkListRemovalSuggestion___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Linter_mkListRemovalSuggestion___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_mkListRemovalSuggestion___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_mkListRemovalSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_mkListRemovalSuggestion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_ownerType_x3f_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_ownerType_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_ownerType_x3f(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Linter_checkDeprecatedAutomationAttr___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_checkDeprecatedAutomationAttr___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_checkDeprecatedAutomationAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "` is deprecated, but the `["};
static const lean_object* l_Lean_Linter_checkDeprecatedAutomationAttr___closed__0 = (const lean_object*)&l_Lean_Linter_checkDeprecatedAutomationAttr___closed__0_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecatedAutomationAttr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecatedAutomationAttr___closed__1;
static const lean_string_object l_Lean_Linter_checkDeprecatedAutomationAttr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "]` attribute lets automation use it without a deprecation warning"};
static const lean_object* l_Lean_Linter_checkDeprecatedAutomationAttr___closed__2 = (const lean_object*)&l_Lean_Linter_checkDeprecatedAutomationAttr___closed__2_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecatedAutomationAttr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecatedAutomationAttr___closed__3;
static const lean_string_object l_Lean_Linter_checkDeprecatedAutomationAttr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 136, .m_capacity = 136, .m_length = 135, .m_data = "Removing the attribute may break proofs that rely on it. If it needs to be kept for now, this warning can be disabled with `set_option "};
static const lean_object* l_Lean_Linter_checkDeprecatedAutomationAttr___closed__4 = (const lean_object*)&l_Lean_Linter_checkDeprecatedAutomationAttr___closed__4_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecatedAutomationAttr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecatedAutomationAttr___closed__5;
static const lean_string_object l_Lean_Linter_checkDeprecatedAutomationAttr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " false in`"};
static const lean_object* l_Lean_Linter_checkDeprecatedAutomationAttr___closed__6 = (const lean_object*)&l_Lean_Linter_checkDeprecatedAutomationAttr___closed__6_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecatedAutomationAttr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecatedAutomationAttr___closed__7;
static const lean_string_object l_Lean_Linter_checkDeprecatedAutomationAttr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Remove the attribute:"};
static const lean_object* l_Lean_Linter_checkDeprecatedAutomationAttr___closed__8 = (const lean_object*)&l_Lean_Linter_checkDeprecatedAutomationAttr___closed__8_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecatedAutomationAttr___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecatedAutomationAttr___closed__9;
LEAN_EXPORT lean_object* l_Lean_Linter_checkDeprecatedAutomationAttr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_checkDeprecatedAutomationAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 1, 0, 0, 0)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2____boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_448960154____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_101_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_448960154____hygCtx___hyg_4_));
v___x_102_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_448960154____hygCtx___hyg_4_));
v___x_103_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_448960154____hygCtx___hyg_4_));
v___x_104_ = l_Lean_Option_register___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__spec__0(v___x_101_, v___x_102_, v___x_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_448960154____hygCtx___hyg_4____boxed(lean_object* v_a_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_448960154____hygCtx___hyg_4_();
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate_spec__1(lean_object* v_a_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = lean_nat_to_int(v_a_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate_spec__2(lean_object* v_a_113_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Rat_ofInt(v_a_113_);
return v___x_114_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___lam__0___closed__0(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = lean_unsigned_to_nat(1000000000u);
v___x_116_ = lean_nat_to_int(v___x_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___lam__0(lean_object* v_tz_117_, lean_object* v_a_118_, lean_object* v___x_119_, lean_object* v_x_120_){
_start:
{
lean_object* v_offset_121_; lean_object* v_second_122_; lean_object* v_nano_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v_nanos_127_; lean_object* v___x_128_; lean_object* v_nanos_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v_offset_121_ = lean_ctor_get(v_tz_117_, 0);
v_second_122_ = lean_ctor_get(v_a_118_, 0);
v_nano_123_ = lean_ctor_get(v_a_118_, 1);
v___x_124_ = lean_nat_to_int(v___x_119_);
v___x_125_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___lam__0___closed__0, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___lam__0___closed__0_once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___lam__0___closed__0);
v___x_126_ = lean_int_mul(v_second_122_, v___x_125_);
v_nanos_127_ = lean_int_add(v___x_126_, v_nano_123_);
lean_dec(v___x_126_);
v___x_128_ = lean_int_mul(v_offset_121_, v___x_125_);
v_nanos_129_ = lean_int_add(v___x_128_, v___x_124_);
lean_dec(v___x_124_);
lean_dec(v___x_128_);
v___x_130_ = lean_int_add(v_nanos_127_, v_nanos_129_);
lean_dec(v_nanos_129_);
lean_dec(v_nanos_127_);
v___x_131_ = l_Std_Time_Duration_ofNanoseconds(v___x_130_);
lean_dec(v___x_130_);
v___x_132_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___lam__0___boxed(lean_object* v_tz_133_, lean_object* v_a_134_, lean_object* v___x_135_, lean_object* v_x_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___lam__0(v_tz_133_, v_a_134_, v___x_135_, v_x_136_);
lean_dec_ref(v_a_134_);
lean_dec_ref(v_tz_133_);
return v_res_137_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__0(void){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = lean_unsigned_to_nat(0u);
v___x_139_ = lean_nat_to_int(v___x_138_);
return v___x_139_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__3(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_143_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__2));
v___x_144_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__0, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__0_once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__0);
v___x_145_ = l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone(v___x_144_, v___x_143_, v___x_143_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate(){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = lean_get_current_time();
if (lean_obj_tag(v___x_172_) == 0)
{
lean_object* v_a_173_; lean_object* v___x_174_; 
v_a_173_ = lean_ctor_get(v___x_172_, 0);
lean_inc(v_a_173_);
lean_dec_ref_known(v___x_172_, 1);
v___x_174_ = l_Std_Time_Database_defaultGetLocalZoneRules();
if (lean_obj_tag(v___x_174_) == 0)
{
lean_object* v_a_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_197_; 
v_a_175_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_197_ == 0)
{
v___x_177_ = v___x_174_;
v_isShared_178_ = v_isSharedCheck_197_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_a_175_);
lean_dec(v___x_174_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_197_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v_offset_181_; lean_object* v_second_182_; lean_object* v_nano_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v_nanos_187_; lean_object* v___x_188_; lean_object* v_nanos_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v_date_193_; lean_object* v___x_195_; 
v___x_179_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForTimestamp(v_a_175_, v_a_173_);
v___x_180_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v___x_179_);
lean_dec_ref(v___x_179_);
v_offset_181_ = lean_ctor_get(v___x_180_, 0);
lean_inc(v_offset_181_);
lean_dec_ref(v___x_180_);
v_second_182_ = lean_ctor_get(v_a_173_, 0);
lean_inc(v_second_182_);
v_nano_183_ = lean_ctor_get(v_a_173_, 1);
lean_inc(v_nano_183_);
lean_dec(v_a_173_);
v___x_184_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__0, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__0_once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__0);
v___x_185_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___lam__0___closed__0, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___lam__0___closed__0_once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___lam__0___closed__0);
v___x_186_ = lean_int_mul(v_second_182_, v___x_185_);
lean_dec(v_second_182_);
v_nanos_187_ = lean_int_add(v___x_186_, v_nano_183_);
lean_dec(v_nano_183_);
lean_dec(v___x_186_);
v___x_188_ = lean_int_mul(v_offset_181_, v___x_185_);
lean_dec(v_offset_181_);
v_nanos_189_ = lean_int_add(v___x_188_, v___x_184_);
lean_dec(v___x_188_);
v___x_190_ = lean_int_add(v_nanos_187_, v_nanos_189_);
lean_dec(v_nanos_189_);
lean_dec(v_nanos_187_);
v___x_191_ = l_Std_Time_Duration_ofNanoseconds(v___x_190_);
lean_dec(v___x_190_);
v___x_192_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_191_);
v_date_193_ = lean_ctor_get(v___x_192_, 0);
lean_inc_ref(v_date_193_);
lean_dec_ref(v___x_192_);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 0, v_date_193_);
v___x_195_ = v___x_177_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_date_193_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
else
{
lean_dec_ref_known(v___x_174_, 1);
lean_dec(v_a_173_);
goto v___jp_147_;
}
}
else
{
lean_dec_ref_known(v___x_172_, 1);
goto v___jp_147_;
}
v___jp_147_:
{
lean_object* v___x_148_; 
v___x_148_ = lean_get_current_time();
if (lean_obj_tag(v___x_148_) == 0)
{
lean_object* v_a_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_163_; 
v_a_149_ = lean_ctor_get(v___x_148_, 0);
v_isSharedCheck_163_ = !lean_is_exclusive(v___x_148_);
if (v_isSharedCheck_163_ == 0)
{
v___x_151_ = v___x_148_;
v_isShared_152_ = v_isSharedCheck_163_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_a_149_);
lean_dec(v___x_148_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_163_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v_tz_155_; lean_object* v___f_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v_date_159_; lean_object* v___x_161_; 
v___x_153_ = lean_unsigned_to_nat(0u);
v___x_154_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__3, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__3_once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__3);
v_tz_155_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v___x_154_, v_a_149_);
v___f_156_ = lean_alloc_closure((void*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___lam__0___boxed), 4, 3);
lean_closure_set(v___f_156_, 0, v_tz_155_);
lean_closure_set(v___f_156_, 1, v_a_149_);
lean_closure_set(v___f_156_, 2, v___x_153_);
v___x_157_ = lean_mk_thunk(v___f_156_);
v___x_158_ = lean_thunk_get_own(v___x_157_);
lean_dec_ref(v___x_157_);
v_date_159_ = lean_ctor_get(v___x_158_, 0);
lean_inc_ref(v_date_159_);
lean_dec(v___x_158_);
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 0, v_date_159_);
v___x_161_ = v___x_151_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_date_159_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
}
else
{
lean_object* v_a_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_171_; 
v_a_164_ = lean_ctor_get(v___x_148_, 0);
v_isSharedCheck_171_ = !lean_is_exclusive(v___x_148_);
if (v_isSharedCheck_171_ == 0)
{
v___x_166_ = v___x_148_;
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_a_164_);
lean_dec(v___x_148_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_169_; 
if (v_isShared_167_ == 0)
{
v___x_169_ = v___x_166_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_a_164_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___boxed(lean_object* v_a_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate();
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate_spec__0(lean_object* v_a_200_){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = lean_nat_to_int(v_a_200_);
v___x_202_ = l_Rat_ofInt(v___x_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_mkSinceHint___lam__0(lean_object* v___x_204_, lean_object* v_x_205_){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = ((lean_object*)(l_Lean_Linter_mkSinceHint___lam__0___closed__0));
v___x_207_ = lean_string_append(v___x_206_, v___x_204_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_mkSinceHint___lam__0___boxed(lean_object* v___x_208_, lean_object* v_x_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lean_Linter_mkSinceHint___lam__0(v___x_208_, v_x_209_);
lean_dec_ref(v_x_209_);
lean_dec_ref(v___x_208_);
return v_res_210_;
}
}
static lean_object* _init_l_Lean_Linter_mkSinceHint___closed__4(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = ((lean_object*)(l_Lean_Linter_mkSinceHint___closed__3));
v___x_217_ = l_Lean_MessageData_ofFormat(v___x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_mkSinceHint(lean_object* v_stx_219_, lean_object* v_a_220_, lean_object* v_a_221_){
_start:
{
uint8_t v___x_223_; lean_object* v___x_224_; 
v___x_223_ = 1;
v___x_224_ = l_Lean_Syntax_getTailPos_x3f(v_stx_219_, v___x_223_);
if (lean_obj_tag(v___x_224_) == 1)
{
lean_object* v_val_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_273_; 
v_val_225_ = lean_ctor_get(v___x_224_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_273_ == 0)
{
v___x_227_ = v___x_224_;
v_isShared_228_ = v_isSharedCheck_273_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_val_225_);
lean_dec(v___x_224_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_273_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v_ref_229_; lean_object* v___x_230_; 
v_ref_229_ = lean_ctor_get(v_a_220_, 2);
v___x_230_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate();
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_a_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___f_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_246_; 
v_a_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_a_231_);
lean_dec_ref_known(v___x_230_, 1);
v___x_232_ = ((lean_object*)(l_Lean_Linter_mkSinceHint___closed__0));
v___x_233_ = l_Std_Time_PlainDate_toLeanDateString(v_a_231_);
v___x_234_ = lean_string_append(v___x_232_, v___x_233_);
lean_dec_ref(v___x_233_);
v___x_235_ = ((lean_object*)(l_Lean_Linter_mkSinceHint___closed__1));
v___x_236_ = lean_string_append(v___x_234_, v___x_235_);
lean_inc_ref(v___x_236_);
v___f_237_ = lean_alloc_closure((void*)(l_Lean_Linter_mkSinceHint___lam__0___boxed), 2, 1);
lean_closure_set(v___f_237_, 0, v___x_236_);
v___x_238_ = lean_obj_once(&l_Lean_Linter_mkSinceHint___closed__4, &l_Lean_Linter_mkSinceHint___closed__4_once, _init_l_Lean_Linter_mkSinceHint___closed__4);
v___x_239_ = ((lean_object*)(l_Lean_Linter_mkSinceHint___closed__5));
v___x_240_ = lean_string_append(v___x_239_, v___x_236_);
v___x_241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
v___x_242_ = lean_box(0);
v___x_243_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_243_, 0, v___x_236_);
v___x_244_ = l_Lean_MessageData_ofFormat(v___x_243_);
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 0, v___x_244_);
v___x_246_ = v___x_227_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_244_);
v___x_246_ = v_reuseFailAlloc_260_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; uint8_t v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; uint8_t v___x_258_; lean_object* v___x_259_; 
v___x_247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_247_, 0, v___f_237_);
v___x_248_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_248_, 0, v___x_241_);
lean_ctor_set(v___x_248_, 1, v___x_242_);
lean_ctor_set(v___x_248_, 2, v___x_242_);
lean_ctor_set(v___x_248_, 3, v___x_242_);
lean_ctor_set(v___x_248_, 4, v___x_246_);
lean_ctor_set(v___x_248_, 5, v___x_247_);
lean_inc(v_val_225_);
v___x_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_249_, 0, v_val_225_);
lean_ctor_set(v___x_249_, 1, v_val_225_);
v___x_250_ = l_Lean_Syntax_ofRange(v___x_249_, v___x_223_);
v___x_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
v___x_252_ = 4;
v___x_253_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_253_, 0, v___x_248_);
lean_ctor_set(v___x_253_, 1, v___x_251_);
lean_ctor_set(v___x_253_, 2, v___x_242_);
lean_ctor_set_uint8(v___x_253_, sizeof(void*)*3, v___x_252_);
v___x_254_ = lean_unsigned_to_nat(1u);
v___x_255_ = lean_mk_empty_array_with_capacity(v___x_254_);
v___x_256_ = lean_array_push(v___x_255_, v___x_253_);
v___x_257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_257_, 0, v_stx_219_);
v___x_258_ = 0;
v___x_259_ = l_Lean_MessageData_hint(v___x_238_, v___x_256_, v___x_257_, v___x_242_, v___x_258_, v_a_220_, v_a_221_);
lean_dec_ref(v___x_256_);
return v___x_259_;
}
}
else
{
lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_272_; 
lean_del_object(v___x_227_);
lean_dec(v_val_225_);
lean_dec(v_stx_219_);
v_a_261_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_272_ == 0)
{
v___x_263_ = v___x_230_;
v_isShared_264_ = v_isSharedCheck_272_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v___x_230_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_272_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_270_; 
v___x_265_ = lean_io_error_to_string(v_a_261_);
v___x_266_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
v___x_267_ = l_Lean_MessageData_ofFormat(v___x_266_);
lean_inc(v_ref_229_);
v___x_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_268_, 0, v_ref_229_);
lean_ctor_set(v___x_268_, 1, v___x_267_);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 0, v___x_268_);
v___x_270_ = v___x_263_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v___x_268_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
}
else
{
lean_object* v___x_274_; lean_object* v___x_275_; 
lean_dec(v___x_224_);
lean_dec(v_stx_219_);
v___x_274_ = l_Lean_MessageData_nil;
v___x_275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_275_, 0, v___x_274_);
return v___x_275_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_mkSinceHint___boxed(lean_object* v_stx_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_Linter_mkSinceHint(v_stx_276_, v_a_277_, v_a_278_);
lean_dec(v_a_278_);
lean_dec_ref(v_a_277_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq_spec__0(lean_object* v_a_284_, lean_object* v_a_285_){
_start:
{
if (lean_obj_tag(v_a_284_) == 0)
{
lean_object* v___x_286_; 
v___x_286_ = lean_array_to_list(v_a_285_);
return v___x_286_;
}
else
{
lean_object* v_tail_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v_tail_287_ = lean_ctor_get(v_a_284_, 1);
v___x_288_ = lean_array_get_size(v_a_285_);
v___x_289_ = ((lean_object*)(l_List_mapIdx_go___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq_spec__0___closed__1));
v___x_290_ = l_Lean_Name_num___override(v___x_289_, v___x_288_);
v___x_291_ = l_Lean_mkLevelParam(v___x_290_);
v___x_292_ = lean_array_push(v_a_285_, v___x_291_);
v_a_284_ = v_tail_287_;
v_a_285_ = v___x_292_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq_spec__0___boxed(lean_object* v_a_294_, lean_object* v_a_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_List_mapIdx_go___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq_spec__0(v_a_294_, v_a_295_);
lean_dec(v_a_294_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq(lean_object* v_decl_u2081_299_, lean_object* v_decl_u2082_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_){
_start:
{
lean_object* v___y_307_; lean_object* v_levelParams_324_; lean_object* v_levelParams_325_; lean_object* v___x_326_; lean_object* v___x_327_; uint8_t v___x_328_; 
v_levelParams_324_ = lean_ctor_get(v_decl_u2081_299_, 1);
v_levelParams_325_ = lean_ctor_get(v_decl_u2082_300_, 1);
v___x_326_ = l_List_lengthTR___redArg(v_levelParams_324_);
v___x_327_ = l_List_lengthTR___redArg(v_levelParams_325_);
v___x_328_ = lean_nat_dec_eq(v___x_326_, v___x_327_);
lean_dec(v___x_327_);
lean_dec(v___x_326_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = lean_box(v___x_328_);
v___x_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
return v___x_330_;
}
else
{
lean_object* v___x_331_; uint8_t v_transparency_332_; lean_object* v___x_333_; lean_object* v_levels_334_; lean_object* v_type_u2081_335_; lean_object* v_type_u2082_336_; uint8_t v___x_337_; uint8_t v___x_338_; 
v___x_331_ = l_Lean_Meta_Context_config(v_a_301_);
v_transparency_332_ = lean_ctor_get_uint8(v___x_331_, 9);
lean_dec_ref(v___x_331_);
v___x_333_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq___closed__0));
v_levels_334_ = l_List_mapIdx_go___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq_spec__0(v_levelParams_324_, v___x_333_);
v_type_u2081_335_ = l_Lean_ConstantVal_instantiateTypeLevelParams(v_decl_u2081_299_, v_levels_334_);
v_type_u2082_336_ = l_Lean_ConstantVal_instantiateTypeLevelParams(v_decl_u2082_300_, v_levels_334_);
lean_dec(v_levels_334_);
v___x_337_ = 2;
v___x_338_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_332_, v___x_337_);
if (v___x_338_ == 0)
{
lean_object* v_keyedConfig_339_; uint8_t v_trackZetaDelta_340_; lean_object* v_zetaDeltaSet_341_; lean_object* v_lctx_342_; lean_object* v_localInstances_343_; lean_object* v_defEqCtx_x3f_344_; lean_object* v_synthPendingDepth_345_; lean_object* v_customCanUnfoldPredicate_x3f_346_; uint8_t v_univApprox_347_; uint8_t v_inTypeClassResolution_348_; uint8_t v_cacheInferType_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v_keyedConfig_339_ = lean_ctor_get(v_a_301_, 0);
v_trackZetaDelta_340_ = lean_ctor_get_uint8(v_a_301_, sizeof(void*)*7);
v_zetaDeltaSet_341_ = lean_ctor_get(v_a_301_, 1);
v_lctx_342_ = lean_ctor_get(v_a_301_, 2);
v_localInstances_343_ = lean_ctor_get(v_a_301_, 3);
v_defEqCtx_x3f_344_ = lean_ctor_get(v_a_301_, 4);
v_synthPendingDepth_345_ = lean_ctor_get(v_a_301_, 5);
v_customCanUnfoldPredicate_x3f_346_ = lean_ctor_get(v_a_301_, 6);
v_univApprox_347_ = lean_ctor_get_uint8(v_a_301_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_348_ = lean_ctor_get_uint8(v_a_301_, sizeof(void*)*7 + 2);
v_cacheInferType_349_ = lean_ctor_get_uint8(v_a_301_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_339_);
v___x_350_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_337_, v_keyedConfig_339_);
lean_inc(v_customCanUnfoldPredicate_x3f_346_);
lean_inc(v_synthPendingDepth_345_);
lean_inc(v_defEqCtx_x3f_344_);
lean_inc_ref(v_localInstances_343_);
lean_inc_ref(v_lctx_342_);
lean_inc(v_zetaDeltaSet_341_);
v___x_351_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_351_, 0, v___x_350_);
lean_ctor_set(v___x_351_, 1, v_zetaDeltaSet_341_);
lean_ctor_set(v___x_351_, 2, v_lctx_342_);
lean_ctor_set(v___x_351_, 3, v_localInstances_343_);
lean_ctor_set(v___x_351_, 4, v_defEqCtx_x3f_344_);
lean_ctor_set(v___x_351_, 5, v_synthPendingDepth_345_);
lean_ctor_set(v___x_351_, 6, v_customCanUnfoldPredicate_x3f_346_);
lean_ctor_set_uint8(v___x_351_, sizeof(void*)*7, v_trackZetaDelta_340_);
lean_ctor_set_uint8(v___x_351_, sizeof(void*)*7 + 1, v_univApprox_347_);
lean_ctor_set_uint8(v___x_351_, sizeof(void*)*7 + 2, v_inTypeClassResolution_348_);
lean_ctor_set_uint8(v___x_351_, sizeof(void*)*7 + 3, v_cacheInferType_349_);
v___x_352_ = l_Lean_Meta_isExprDefEqGuarded(v_type_u2081_335_, v_type_u2082_336_, v___x_351_, v_a_302_, v_a_303_, v_a_304_);
lean_dec_ref_known(v___x_351_, 7);
v___y_307_ = v___x_352_;
goto v___jp_306_;
}
else
{
lean_object* v___x_353_; 
v___x_353_ = l_Lean_Meta_isExprDefEqGuarded(v_type_u2081_335_, v_type_u2082_336_, v_a_301_, v_a_302_, v_a_303_, v_a_304_);
v___y_307_ = v___x_353_;
goto v___jp_306_;
}
}
v___jp_306_:
{
if (lean_obj_tag(v___y_307_) == 0)
{
lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_315_; 
v_a_308_ = lean_ctor_get(v___y_307_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___y_307_);
if (v_isSharedCheck_315_ == 0)
{
v___x_310_ = v___y_307_;
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___y_307_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_313_; 
if (v_isShared_311_ == 0)
{
v___x_313_ = v___x_310_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_a_308_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
else
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_323_; 
v_a_316_ = lean_ctor_get(v___y_307_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___y_307_);
if (v_isSharedCheck_323_ == 0)
{
v___x_318_ = v___y_307_;
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___y_307_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_321_; 
if (v_isShared_319_ == 0)
{
v___x_321_ = v___x_318_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_a_316_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq___boxed(lean_object* v_decl_u2081_354_, lean_object* v_decl_u2082_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq(v_decl_u2081_354_, v_decl_u2082_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_);
lean_dec(v_a_359_);
lean_dec_ref(v_a_358_);
lean_dec(v_a_357_);
lean_dec_ref(v_a_356_);
lean_dec_ref(v_decl_u2082_355_);
lean_dec_ref(v_decl_u2081_354_);
return v_res_361_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__5(lean_object* v_opts_362_, lean_object* v_opt_363_){
_start:
{
lean_object* v_name_364_; lean_object* v_defValue_365_; lean_object* v_map_366_; lean_object* v___x_367_; 
v_name_364_ = lean_ctor_get(v_opt_363_, 0);
v_defValue_365_ = lean_ctor_get(v_opt_363_, 1);
v_map_366_ = lean_ctor_get(v_opts_362_, 0);
v___x_367_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_366_, v_name_364_);
if (lean_obj_tag(v___x_367_) == 0)
{
uint8_t v___x_368_; 
v___x_368_ = lean_unbox(v_defValue_365_);
return v___x_368_;
}
else
{
lean_object* v_val_369_; 
v_val_369_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_val_369_);
lean_dec_ref_known(v___x_367_, 1);
if (lean_obj_tag(v_val_369_) == 1)
{
uint8_t v_v_370_; 
v_v_370_ = lean_ctor_get_uint8(v_val_369_, 0);
lean_dec_ref_known(v_val_369_, 0);
return v_v_370_;
}
else
{
uint8_t v___x_371_; 
lean_dec(v_val_369_);
v___x_371_ = lean_unbox(v_defValue_365_);
return v___x_371_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__5___boxed(lean_object* v_opts_372_, lean_object* v_opt_373_){
_start:
{
uint8_t v_res_374_; lean_object* v_r_375_; 
v_res_374_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__5(v_opts_372_, v_opt_373_);
lean_dec_ref(v_opt_373_);
lean_dec_ref(v_opts_372_);
v_r_375_ = lean_box(v_res_374_);
return v_r_375_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__7(lean_object* v_x_376_, lean_object* v_x_377_){
_start:
{
if (lean_obj_tag(v_x_376_) == 0)
{
if (lean_obj_tag(v_x_377_) == 0)
{
uint8_t v___x_378_; 
v___x_378_ = 1;
return v___x_378_;
}
else
{
uint8_t v___x_379_; 
v___x_379_ = 0;
return v___x_379_;
}
}
else
{
if (lean_obj_tag(v_x_377_) == 0)
{
uint8_t v___x_380_; 
v___x_380_ = 0;
return v___x_380_;
}
else
{
lean_object* v_val_381_; lean_object* v_val_382_; uint8_t v___x_383_; 
v_val_381_ = lean_ctor_get(v_x_376_, 0);
v_val_382_ = lean_ctor_get(v_x_377_, 0);
v___x_383_ = lean_name_eq(v_val_381_, v_val_382_);
return v___x_383_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__7___boxed(lean_object* v_x_384_, lean_object* v_x_385_){
_start:
{
uint8_t v_res_386_; lean_object* v_r_387_; 
v_res_386_ = l_instBEqOption_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__7(v_x_384_, v_x_385_);
lean_dec(v_x_385_);
lean_dec(v_x_384_);
v_r_387_ = lean_box(v_res_386_);
return v_r_387_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(lean_object* v_env_388_, lean_object* v_n_389_, lean_object* v_x_390_){
_start:
{
uint8_t v___x_391_; uint8_t v___x_392_; 
v___x_391_ = 1;
v___x_392_ = l_Lean_Environment_contains(v_env_388_, v_n_389_, v___x_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2____boxed(lean_object* v_env_393_, lean_object* v_n_394_, lean_object* v_x_395_){
_start:
{
uint8_t v_res_396_; lean_object* v_r_397_; 
v_res_396_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(v_env_393_, v_n_394_, v_x_395_);
lean_dec_ref(v_x_395_);
v_r_397_ = lean_box(v_res_396_);
return v_r_397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(lean_object* v_x_399_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__0_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2____boxed(lean_object* v_x_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(v_x_401_);
lean_dec_ref(v_x_401_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(lean_object* v_x_403_, lean_object* v_x_404_, lean_object* v_x_405_, lean_object* v___y_406_){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = lean_box(0);
v___x_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2____boxed(lean_object* v_x_410_, lean_object* v_x_411_, lean_object* v_x_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(v_x_410_, v_x_411_, v_x_412_, v___y_413_);
lean_dec(v___y_413_);
lean_dec_ref(v_x_412_);
lean_dec_ref(v_x_411_);
lean_dec(v_x_410_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__3_spec__8___redArg(lean_object* v_o_416_, lean_object* v___y_417_){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v_env_421_; lean_object* v___x_422_; lean_object* v_toEnvExtension_423_; lean_object* v_asyncMode_424_; lean_object* v___x_425_; uint8_t v___x_426_; lean_object* v___x_427_; lean_object* v_merged_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_436_; 
v___x_419_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_420_ = lean_st_ref_get(v___y_417_);
v_env_421_ = lean_ctor_get(v___x_420_, 0);
lean_inc_ref(v_env_421_);
lean_dec(v___x_420_);
v___x_422_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_423_ = lean_ctor_get(v___x_422_, 0);
v_asyncMode_424_ = lean_ctor_get(v_toEnvExtension_423_, 2);
v___x_425_ = lean_box(0);
v___x_426_ = 0;
v___x_427_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_419_, v___x_422_, v_env_421_, v_asyncMode_424_, v___x_425_, v___x_426_);
v_merged_428_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_436_ == 0)
{
lean_object* v_unused_437_; 
v_unused_437_ = lean_ctor_get(v___x_427_, 1);
lean_dec(v_unused_437_);
v___x_430_ = v___x_427_;
v_isShared_431_ = v_isSharedCheck_436_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_merged_428_);
lean_dec(v___x_427_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_436_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 1, v_merged_428_);
lean_ctor_set(v___x_430_, 0, v_o_416_);
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_o_416_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v_merged_428_);
v___x_433_ = v_reuseFailAlloc_435_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
lean_object* v___x_434_; 
v___x_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
return v___x_434_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__3_spec__8___redArg___boxed(lean_object* v_o_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__3_spec__8___redArg(v_o_438_, v___y_439_);
lean_dec(v___y_439_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__3(lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_442_);
v___x_446_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__3_spec__8___redArg(v___x_445_, v___y_443_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__3___boxed(lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__3(v___y_447_, v___y_448_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
return v_res_450_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_451_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_452_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
return v___x_453_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_454_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_455_ = lean_unsigned_to_nat(0u);
v___x_456_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
lean_ctor_set(v___x_456_, 1, v___x_455_);
lean_ctor_set(v___x_456_, 2, v___x_455_);
lean_ctor_set(v___x_456_, 3, v___x_455_);
lean_ctor_set(v___x_456_, 4, v___x_454_);
lean_ctor_set(v___x_456_, 5, v___x_454_);
lean_ctor_set(v___x_456_, 6, v___x_454_);
lean_ctor_set(v___x_456_, 7, v___x_454_);
lean_ctor_set(v___x_456_, 8, v___x_454_);
lean_ctor_set(v___x_456_, 9, v___x_454_);
lean_ctor_set(v___x_456_, 10, v___x_454_);
return v___x_456_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_457_ = lean_unsigned_to_nat(32u);
v___x_458_ = lean_mk_empty_array_with_capacity(v___x_457_);
v___x_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
return v___x_459_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_460_ = ((size_t)5ULL);
v___x_461_ = lean_unsigned_to_nat(0u);
v___x_462_ = lean_unsigned_to_nat(32u);
v___x_463_ = lean_mk_empty_array_with_capacity(v___x_462_);
v___x_464_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_465_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_465_, 0, v___x_464_);
lean_ctor_set(v___x_465_, 1, v___x_463_);
lean_ctor_set(v___x_465_, 2, v___x_461_);
lean_ctor_set(v___x_465_, 3, v___x_461_);
lean_ctor_set_usize(v___x_465_, 4, v___x_460_);
return v___x_465_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_466_ = lean_box(1);
v___x_467_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_468_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_469_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
lean_ctor_set(v___x_469_, 1, v___x_467_);
lean_ctor_set(v___x_469_, 2, v___x_466_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
lean_object* v___x_474_; lean_object* v_toCold_475_; lean_object* v_env_476_; lean_object* v_options_477_; uint8_t v___x_478_; lean_object* v_env_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_474_ = lean_st_ref_get(v___y_472_);
v_toCold_475_ = lean_ctor_get(v___y_471_, 0);
v_env_476_ = lean_ctor_get(v___x_474_, 0);
lean_inc_ref(v_env_476_);
lean_dec(v___x_474_);
v_options_477_ = lean_ctor_get(v_toCold_475_, 2);
v___x_478_ = 0;
v_env_479_ = l_Lean_Environment_setRecordingDeps(v_env_476_, v___x_478_);
v___x_480_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_481_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_477_);
v___x_482_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_482_, 0, v_env_479_);
lean_ctor_set(v___x_482_, 1, v___x_480_);
lean_ctor_set(v___x_482_, 2, v___x_481_);
lean_ctor_set(v___x_482_, 3, v_options_477_);
v___x_483_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
lean_ctor_set(v___x_483_, 1, v_msgData_470_);
v___x_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0(v_msgData_485_, v___y_486_, v___y_487_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
lean_object* v_ref_494_; lean_object* v___x_495_; lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_504_; 
v_ref_494_ = lean_ctor_get(v___y_491_, 2);
v___x_495_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0(v_msg_490_, v___y_491_, v___y_492_);
v_a_496_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_504_ == 0)
{
v___x_498_ = v___x_495_;
v_isShared_499_ = v_isSharedCheck_504_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_495_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_504_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_500_; lean_object* v___x_502_; 
lean_inc(v_ref_494_);
v___x_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_500_, 0, v_ref_494_);
lean_ctor_set(v___x_500_, 1, v_a_496_);
if (v_isShared_499_ == 0)
{
lean_ctor_set_tag(v___x_498_, 1);
lean_ctor_set(v___x_498_, 0, v___x_500_);
v___x_502_ = v___x_498_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0___redArg(v_msg_505_, v___y_506_, v___y_507_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___lam__0(lean_object* v___x_510_, lean_object* v_entry_511_, lean_object* v_s_512_){
_start:
{
lean_object* v_addEntryFn_513_; lean_object* v_importedEntries_514_; lean_object* v_state_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_523_; 
v_addEntryFn_513_ = lean_ctor_get(v___x_510_, 3);
lean_inc(v_addEntryFn_513_);
lean_dec_ref(v___x_510_);
v_importedEntries_514_ = lean_ctor_get(v_s_512_, 0);
v_state_515_ = lean_ctor_get(v_s_512_, 1);
v_isSharedCheck_523_ = !lean_is_exclusive(v_s_512_);
if (v_isSharedCheck_523_ == 0)
{
v___x_517_ = v_s_512_;
v_isShared_518_ = v_isSharedCheck_523_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_state_515_);
lean_inc(v_importedEntries_514_);
lean_dec(v_s_512_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_523_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v_state_519_; lean_object* v___x_521_; 
v_state_519_ = lean_apply_2(v_addEntryFn_513_, v_state_515_, v_entry_511_);
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 1, v_state_519_);
v___x_521_ = v___x_517_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_importedEntries_514_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v_state_519_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14_spec__19___redArg(lean_object* v_keys_524_, lean_object* v_i_525_, lean_object* v_k_526_){
_start:
{
lean_object* v___x_527_; uint8_t v___x_528_; 
v___x_527_ = lean_array_get_size(v_keys_524_);
v___x_528_ = lean_nat_dec_lt(v_i_525_, v___x_527_);
if (v___x_528_ == 0)
{
lean_dec(v_i_525_);
return v___x_528_;
}
else
{
lean_object* v_k_x27_529_; uint8_t v___x_530_; 
v_k_x27_529_ = lean_array_fget_borrowed(v_keys_524_, v_i_525_);
v___x_530_ = l_Lean_instBEqExtraModUse_beq(v_k_526_, v_k_x27_529_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = lean_unsigned_to_nat(1u);
v___x_532_ = lean_nat_add(v_i_525_, v___x_531_);
lean_dec(v_i_525_);
v_i_525_ = v___x_532_;
goto _start;
}
else
{
lean_dec(v_i_525_);
return v___x_528_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14_spec__19___redArg___boxed(lean_object* v_keys_534_, lean_object* v_i_535_, lean_object* v_k_536_){
_start:
{
uint8_t v_res_537_; lean_object* v_r_538_; 
v_res_537_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14_spec__19___redArg(v_keys_534_, v_i_535_, v_k_536_);
lean_dec_ref(v_k_536_);
lean_dec_ref(v_keys_534_);
v_r_538_ = lean_box(v_res_537_);
return v_r_538_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14___redArg(lean_object* v_x_539_, size_t v_x_540_, lean_object* v_x_541_){
_start:
{
if (lean_obj_tag(v_x_539_) == 0)
{
lean_object* v_es_542_; lean_object* v___x_543_; size_t v___x_544_; size_t v___x_545_; lean_object* v_j_546_; lean_object* v___x_547_; 
v_es_542_ = lean_ctor_get(v_x_539_, 0);
v___x_543_ = lean_box(2);
v___x_544_ = ((size_t)31ULL);
v___x_545_ = lean_usize_land(v_x_540_, v___x_544_);
v_j_546_ = lean_usize_to_nat(v___x_545_);
v___x_547_ = lean_array_get_borrowed(v___x_543_, v_es_542_, v_j_546_);
lean_dec(v_j_546_);
switch(lean_obj_tag(v___x_547_))
{
case 0:
{
lean_object* v_key_548_; uint8_t v___x_549_; 
v_key_548_ = lean_ctor_get(v___x_547_, 0);
v___x_549_ = l_Lean_instBEqExtraModUse_beq(v_x_541_, v_key_548_);
return v___x_549_;
}
case 1:
{
lean_object* v_node_550_; size_t v___x_551_; size_t v___x_552_; 
v_node_550_ = lean_ctor_get(v___x_547_, 0);
v___x_551_ = ((size_t)5ULL);
v___x_552_ = lean_usize_shift_right(v_x_540_, v___x_551_);
v_x_539_ = v_node_550_;
v_x_540_ = v___x_552_;
goto _start;
}
default: 
{
uint8_t v___x_554_; 
v___x_554_ = 0;
return v___x_554_;
}
}
}
else
{
lean_object* v_ks_555_; lean_object* v___x_556_; uint8_t v___x_557_; 
v_ks_555_ = lean_ctor_get(v_x_539_, 0);
v___x_556_ = lean_unsigned_to_nat(0u);
v___x_557_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14_spec__19___redArg(v_ks_555_, v___x_556_, v_x_541_);
return v___x_557_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14___redArg___boxed(lean_object* v_x_558_, lean_object* v_x_559_, lean_object* v_x_560_){
_start:
{
size_t v_x_44947__boxed_561_; uint8_t v_res_562_; lean_object* v_r_563_; 
v_x_44947__boxed_561_ = lean_unbox_usize(v_x_559_);
lean_dec(v_x_559_);
v_res_562_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14___redArg(v_x_558_, v_x_44947__boxed_561_, v_x_560_);
lean_dec_ref(v_x_560_);
lean_dec_ref(v_x_558_);
v_r_563_ = lean_box(v_res_562_);
return v_r_563_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg(lean_object* v_x_564_, lean_object* v_x_565_){
_start:
{
uint64_t v___x_566_; size_t v___x_567_; uint8_t v___x_568_; 
v___x_566_ = l_Lean_instHashableExtraModUse_hash(v_x_565_);
v___x_567_ = lean_uint64_to_usize(v___x_566_);
v___x_568_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14___redArg(v_x_564_, v___x_567_, v_x_565_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_x_569_, lean_object* v_x_570_){
_start:
{
uint8_t v_res_571_; lean_object* v_r_572_; 
v_res_571_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg(v_x_569_, v_x_570_);
lean_dec_ref(v_x_570_);
lean_dec_ref(v_x_569_);
v_r_572_ = lean_box(v_res_571_);
return v_r_572_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0(void){
_start:
{
lean_object* v___x_573_; double v___x_574_; 
v___x_573_ = lean_unsigned_to_nat(0u);
v___x_574_ = lean_float_of_nat(v___x_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__9(lean_object* v_cls_578_, lean_object* v_msg_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
lean_object* v_ref_583_; lean_object* v___x_584_; lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_630_; 
v_ref_583_ = lean_ctor_get(v___y_580_, 2);
v___x_584_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0(v_msg_579_, v___y_580_, v___y_581_);
v_a_585_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_630_ == 0)
{
v___x_587_ = v___x_584_;
v_isShared_588_ = v_isSharedCheck_630_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___x_584_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_630_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_589_; lean_object* v_traceState_590_; lean_object* v_env_591_; lean_object* v_nextMacroScope_592_; lean_object* v_ngen_593_; lean_object* v_auxDeclNGen_594_; lean_object* v_cache_595_; lean_object* v_recordedDeps_596_; lean_object* v_messages_597_; lean_object* v_infoState_598_; lean_object* v_snapshotTasks_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_629_; 
v___x_589_ = lean_st_ref_take(v___y_581_);
v_traceState_590_ = lean_ctor_get(v___x_589_, 4);
v_env_591_ = lean_ctor_get(v___x_589_, 0);
v_nextMacroScope_592_ = lean_ctor_get(v___x_589_, 1);
v_ngen_593_ = lean_ctor_get(v___x_589_, 2);
v_auxDeclNGen_594_ = lean_ctor_get(v___x_589_, 3);
v_cache_595_ = lean_ctor_get(v___x_589_, 5);
v_recordedDeps_596_ = lean_ctor_get(v___x_589_, 6);
v_messages_597_ = lean_ctor_get(v___x_589_, 7);
v_infoState_598_ = lean_ctor_get(v___x_589_, 8);
v_snapshotTasks_599_ = lean_ctor_get(v___x_589_, 9);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_629_ == 0)
{
v___x_601_ = v___x_589_;
v_isShared_602_ = v_isSharedCheck_629_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_snapshotTasks_599_);
lean_inc(v_infoState_598_);
lean_inc(v_messages_597_);
lean_inc(v_recordedDeps_596_);
lean_inc(v_cache_595_);
lean_inc(v_traceState_590_);
lean_inc(v_auxDeclNGen_594_);
lean_inc(v_ngen_593_);
lean_inc(v_nextMacroScope_592_);
lean_inc(v_env_591_);
lean_dec(v___x_589_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_629_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
uint64_t v_tid_603_; lean_object* v_traces_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_628_; 
v_tid_603_ = lean_ctor_get_uint64(v_traceState_590_, sizeof(void*)*1);
v_traces_604_ = lean_ctor_get(v_traceState_590_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v_traceState_590_);
if (v_isSharedCheck_628_ == 0)
{
v___x_606_ = v_traceState_590_;
v_isShared_607_ = v_isSharedCheck_628_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_traces_604_);
lean_dec(v_traceState_590_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_628_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_608_; lean_object* v___x_609_; double v___x_610_; uint8_t v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_619_; 
v___x_608_ = lean_box(0);
v___x_609_ = lean_box(0);
v___x_610_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0);
v___x_611_ = 0;
v___x_612_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__1));
v___x_613_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_613_, 0, v_cls_578_);
lean_ctor_set(v___x_613_, 1, v___x_609_);
lean_ctor_set(v___x_613_, 2, v___x_612_);
lean_ctor_set_float(v___x_613_, sizeof(void*)*3, v___x_610_);
lean_ctor_set_float(v___x_613_, sizeof(void*)*3 + 8, v___x_610_);
lean_ctor_set_uint8(v___x_613_, sizeof(void*)*3 + 16, v___x_611_);
v___x_614_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__2));
v___x_615_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_615_, 0, v___x_613_);
lean_ctor_set(v___x_615_, 1, v_a_585_);
lean_ctor_set(v___x_615_, 2, v___x_614_);
lean_inc(v_ref_583_);
v___x_616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_616_, 0, v_ref_583_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
v___x_617_ = l_Lean_PersistentArray_push___redArg(v_traces_604_, v___x_616_);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 0, v___x_617_);
v___x_619_ = v___x_606_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_617_);
lean_ctor_set_uint64(v_reuseFailAlloc_627_, sizeof(void*)*1, v_tid_603_);
v___x_619_ = v_reuseFailAlloc_627_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
lean_object* v___x_621_; 
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 4, v___x_619_);
v___x_621_ = v___x_601_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_env_591_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_nextMacroScope_592_);
lean_ctor_set(v_reuseFailAlloc_626_, 2, v_ngen_593_);
lean_ctor_set(v_reuseFailAlloc_626_, 3, v_auxDeclNGen_594_);
lean_ctor_set(v_reuseFailAlloc_626_, 4, v___x_619_);
lean_ctor_set(v_reuseFailAlloc_626_, 5, v_cache_595_);
lean_ctor_set(v_reuseFailAlloc_626_, 6, v_recordedDeps_596_);
lean_ctor_set(v_reuseFailAlloc_626_, 7, v_messages_597_);
lean_ctor_set(v_reuseFailAlloc_626_, 8, v_infoState_598_);
lean_ctor_set(v_reuseFailAlloc_626_, 9, v_snapshotTasks_599_);
v___x_621_ = v_reuseFailAlloc_626_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
lean_object* v___x_622_; lean_object* v___x_624_; 
v___x_622_ = lean_st_ref_put(v___y_581_, v___x_621_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 0, v___x_608_);
v___x_624_ = v___x_587_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_608_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__9___boxed(lean_object* v_cls_631_, lean_object* v_msg_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__9(v_cls_631_, v_msg_632_, v___y_633_, v___y_634_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
return v_res_636_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__0(void){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_637_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
return v___x_638_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__1(void){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__0);
v___x_640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
lean_ctor_set(v___x_640_, 1, v___x_639_);
return v___x_640_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__2(void){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_641_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__6(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__5));
v___x_647_ = l_Lean_stringToMessageData(v___x_646_);
return v___x_647_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__8(void){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__7));
v___x_650_ = l_Lean_stringToMessageData(v___x_649_);
return v___x_650_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__9(void){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__1));
v___x_652_ = l_Lean_stringToMessageData(v___x_651_);
return v___x_652_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__12(void){
_start:
{
lean_object* v_cls_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v_cls_656_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__4));
v___x_657_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__11));
v___x_658_ = l_Lean_Name_append(v___x_657_, v_cls_656_);
return v___x_658_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__14(void){
_start:
{
lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_660_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__13));
v___x_661_ = l_Lean_stringToMessageData(v___x_660_);
return v___x_661_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__15(void){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_662_ = ((lean_object*)(l_Lean_Linter_mkSinceHint___closed__5));
v___x_663_ = l_Lean_stringToMessageData(v___x_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4(lean_object* v_mod_668_, uint8_t v_isMeta_669_, lean_object* v_hint_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v_env_692_; uint8_t v_isExporting_693_; lean_object* v_entry_694_; lean_object* v___x_695_; lean_object* v_env_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; uint8_t v___x_701_; 
v___x_690_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__2);
v___x_691_ = lean_st_ref_get(v___y_672_);
v_env_692_ = lean_ctor_get(v___x_691_, 0);
lean_inc_ref(v_env_692_);
lean_dec(v___x_691_);
v_isExporting_693_ = lean_ctor_get_uint8(v_env_692_, sizeof(void*)*13);
lean_dec_ref(v_env_692_);
lean_inc(v_mod_668_);
v_entry_694_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_694_, 0, v_mod_668_);
lean_ctor_set_uint8(v_entry_694_, sizeof(void*)*1, v_isExporting_693_);
lean_ctor_set_uint8(v_entry_694_, sizeof(void*)*1 + 1, v_isMeta_669_);
v___x_695_ = lean_st_ref_get(v___y_672_);
v_env_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc_ref(v_env_696_);
lean_dec(v___x_695_);
v___x_697_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_698_ = lean_box(1);
v___x_699_ = lean_box(0);
v___x_700_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_690_, v___x_697_, v_env_696_, v___x_698_, v___x_699_);
v___x_701_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg(v___x_700_, v_entry_694_);
lean_dec(v___x_700_);
if (v___x_701_ == 0)
{
lean_object* v_toCold_702_; lean_object* v_options_703_; lean_object* v_inheritedTraceOptions_704_; uint8_t v_hasTrace_705_; lean_object* v___f_706_; uint8_t v___x_707_; lean_object* v___y_709_; 
v_toCold_702_ = lean_ctor_get(v___y_671_, 0);
v_options_703_ = lean_ctor_get(v_toCold_702_, 2);
v_inheritedTraceOptions_704_ = lean_ctor_get(v_toCold_702_, 11);
v_hasTrace_705_ = lean_ctor_get_uint8(v_options_703_, sizeof(void*)*1);
v___f_706_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___lam__0), 3, 2);
lean_closure_set(v___f_706_, 0, v___x_697_);
lean_closure_set(v___f_706_, 1, v_entry_694_);
v___x_707_ = 1;
if (v_hasTrace_705_ == 0)
{
lean_dec(v_hint_670_);
lean_dec(v_mod_668_);
v___y_709_ = v___y_672_;
goto v___jp_708_;
}
else
{
lean_object* v_cls_727_; lean_object* v___y_729_; lean_object* v___y_730_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v___x_747_; uint8_t v___x_748_; 
v_cls_727_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__4));
v___x_747_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__12);
v___x_748_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_704_, v_options_703_, v___x_747_);
if (v___x_748_ == 0)
{
lean_dec(v_hint_670_);
lean_dec(v_mod_668_);
v___y_709_ = v___y_672_;
goto v___jp_708_;
}
else
{
lean_object* v___x_749_; lean_object* v___y_751_; 
v___x_749_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__14);
if (v_isExporting_693_ == 0)
{
lean_object* v___x_758_; 
v___x_758_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__18));
v___y_751_ = v___x_758_;
goto v___jp_750_;
}
else
{
lean_object* v___x_759_; 
v___x_759_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__19));
v___y_751_ = v___x_759_;
goto v___jp_750_;
}
v___jp_750_:
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
lean_inc_ref(v___y_751_);
v___x_752_ = l_Lean_stringToMessageData(v___y_751_);
v___x_753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_749_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
v___x_754_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__15, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__15_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__15);
v___x_755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_755_, 0, v___x_753_);
lean_ctor_set(v___x_755_, 1, v___x_754_);
if (v_isMeta_669_ == 0)
{
lean_object* v___x_756_; 
v___x_756_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__16));
v___y_734_ = v___x_755_;
v___y_735_ = v___x_756_;
goto v___jp_733_;
}
else
{
lean_object* v___x_757_; 
v___x_757_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__17));
v___y_734_ = v___x_755_;
v___y_735_ = v___x_757_;
goto v___jp_733_;
}
}
}
v___jp_728_:
{
lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_731_, 0, v___y_729_);
lean_ctor_set(v___x_731_, 1, v___y_730_);
v___x_732_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__9(v_cls_727_, v___x_731_, v___y_671_, v___y_672_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_dec_ref_known(v___x_732_, 1);
v___y_709_ = v___y_672_;
goto v___jp_708_;
}
else
{
lean_dec_ref(v___f_706_);
return v___x_732_;
}
}
v___jp_733_:
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; uint8_t v___x_742_; 
lean_inc_ref(v___y_735_);
v___x_736_ = l_Lean_stringToMessageData(v___y_735_);
v___x_737_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_737_, 0, v___y_734_);
lean_ctor_set(v___x_737_, 1, v___x_736_);
v___x_738_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__6);
v___x_739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_739_, 0, v___x_737_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
v___x_740_ = l_Lean_MessageData_ofName(v_mod_668_);
v___x_741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_739_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
v___x_742_ = l_Lean_Name_isAnonymous(v_hint_670_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_743_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__8);
v___x_744_ = l_Lean_MessageData_ofName(v_hint_670_);
v___x_745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_743_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
v___y_729_ = v___x_741_;
v___y_730_ = v___x_745_;
goto v___jp_728_;
}
else
{
lean_object* v___x_746_; 
lean_dec(v_hint_670_);
v___x_746_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__9);
v___y_729_ = v___x_741_;
v___y_730_ = v___x_746_;
goto v___jp_728_;
}
}
}
v___jp_708_:
{
lean_object* v___x_710_; lean_object* v_toEnvExtension_711_; lean_object* v_env_712_; lean_object* v_nextMacroScope_713_; lean_object* v_ngen_714_; lean_object* v_auxDeclNGen_715_; lean_object* v_traceState_716_; lean_object* v_recordedDeps_717_; lean_object* v_messages_718_; lean_object* v_infoState_719_; lean_object* v_snapshotTasks_720_; lean_object* v_asyncMode_721_; uint8_t v_logWrites_722_; lean_object* v___x_723_; 
v___x_710_ = lean_st_ref_take(v___y_709_);
v_toEnvExtension_711_ = lean_ctor_get(v___x_697_, 0);
v_env_712_ = lean_ctor_get(v___x_710_, 0);
lean_inc_ref(v_env_712_);
v_nextMacroScope_713_ = lean_ctor_get(v___x_710_, 1);
lean_inc(v_nextMacroScope_713_);
v_ngen_714_ = lean_ctor_get(v___x_710_, 2);
lean_inc_ref(v_ngen_714_);
v_auxDeclNGen_715_ = lean_ctor_get(v___x_710_, 3);
lean_inc_ref(v_auxDeclNGen_715_);
v_traceState_716_ = lean_ctor_get(v___x_710_, 4);
lean_inc_ref(v_traceState_716_);
v_recordedDeps_717_ = lean_ctor_get(v___x_710_, 6);
lean_inc_ref(v_recordedDeps_717_);
v_messages_718_ = lean_ctor_get(v___x_710_, 7);
lean_inc_ref(v_messages_718_);
v_infoState_719_ = lean_ctor_get(v___x_710_, 8);
lean_inc_ref(v_infoState_719_);
v_snapshotTasks_720_ = lean_ctor_get(v___x_710_, 9);
lean_inc_ref(v_snapshotTasks_720_);
lean_dec(v___x_710_);
v_asyncMode_721_ = lean_ctor_get(v_toEnvExtension_711_, 2);
v_logWrites_722_ = lean_ctor_get_uint8(v_toEnvExtension_711_, sizeof(void*)*6);
v___x_723_ = lean_box(0);
if (v_logWrites_722_ == 0)
{
lean_object* v___x_724_; 
lean_inc_ref(v_toEnvExtension_711_);
v___x_724_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_711_, v_env_712_, v___f_706_, v_asyncMode_721_, v___x_699_, v___x_707_);
v___y_675_ = v_messages_718_;
v___y_676_ = v___x_723_;
v___y_677_ = v_snapshotTasks_720_;
v___y_678_ = v___y_709_;
v___y_679_ = v_infoState_719_;
v___y_680_ = v_recordedDeps_717_;
v___y_681_ = v_ngen_714_;
v___y_682_ = v_traceState_716_;
v___y_683_ = v_auxDeclNGen_715_;
v___y_684_ = v_nextMacroScope_713_;
v___y_685_ = v___x_724_;
goto v___jp_674_;
}
else
{
lean_object* v___x_725_; lean_object* v___x_726_; 
lean_inc_ref_n(v_toEnvExtension_711_, 2);
v___x_725_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_711_, v_env_712_);
lean_dec_ref(v_env_712_);
v___x_726_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_711_, v___x_725_, v___f_706_, v_asyncMode_721_, v___x_699_, v___x_707_);
v___y_675_ = v_messages_718_;
v___y_676_ = v___x_723_;
v___y_677_ = v_snapshotTasks_720_;
v___y_678_ = v___y_709_;
v___y_679_ = v_infoState_719_;
v___y_680_ = v_recordedDeps_717_;
v___y_681_ = v_ngen_714_;
v___y_682_ = v_traceState_716_;
v___y_683_ = v_auxDeclNGen_715_;
v___y_684_ = v_nextMacroScope_713_;
v___y_685_ = v___x_726_;
goto v___jp_674_;
}
}
}
else
{
lean_object* v___x_760_; lean_object* v___x_761_; 
lean_dec_ref_known(v_entry_694_, 1);
lean_dec(v_hint_670_);
lean_dec(v_mod_668_);
v___x_760_ = lean_box(0);
v___x_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
return v___x_761_;
}
v___jp_674_:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_686_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__1);
v___x_687_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_687_, 0, v___y_685_);
lean_ctor_set(v___x_687_, 1, v___y_684_);
lean_ctor_set(v___x_687_, 2, v___y_681_);
lean_ctor_set(v___x_687_, 3, v___y_683_);
lean_ctor_set(v___x_687_, 4, v___y_682_);
lean_ctor_set(v___x_687_, 5, v___x_686_);
lean_ctor_set(v___x_687_, 6, v___y_680_);
lean_ctor_set(v___x_687_, 7, v___y_675_);
lean_ctor_set(v___x_687_, 8, v___y_679_);
lean_ctor_set(v___x_687_, 9, v___y_677_);
v___x_688_ = lean_st_ref_put(v___y_678_, v___x_687_);
v___x_689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_689_, 0, v___y_676_);
return v___x_689_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___boxed(lean_object* v_mod_762_, lean_object* v_isMeta_763_, lean_object* v_hint_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
uint8_t v_isMeta_boxed_768_; lean_object* v_res_769_; 
v_isMeta_boxed_768_ = lean_unbox(v_isMeta_763_);
v_res_769_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4(v_mod_762_, v_isMeta_boxed_768_, v_hint_764_, v___y_765_, v___y_766_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__5(lean_object* v___x_770_, lean_object* v_declName_771_, lean_object* v_as_772_, size_t v_sz_773_, size_t v_i_774_, lean_object* v_b_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
uint8_t v___x_779_; 
v___x_779_ = lean_usize_dec_lt(v_i_774_, v_sz_773_);
if (v___x_779_ == 0)
{
lean_object* v___x_780_; 
lean_dec(v_declName_771_);
v___x_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_780_, 0, v_b_775_);
return v___x_780_;
}
else
{
lean_object* v___x_781_; lean_object* v_modules_782_; lean_object* v___x_783_; lean_object* v_a_784_; lean_object* v___x_785_; lean_object* v_toImport_786_; lean_object* v_module_787_; lean_object* v___x_788_; uint8_t v___x_789_; lean_object* v___x_790_; 
v___x_781_ = l_Lean_Environment_header(v___x_770_);
v_modules_782_ = lean_ctor_get(v___x_781_, 3);
lean_inc_ref(v_modules_782_);
lean_dec_ref(v___x_781_);
v___x_783_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_784_ = lean_array_uget_borrowed(v_as_772_, v_i_774_);
v___x_785_ = lean_array_get(v___x_783_, v_modules_782_, v_a_784_);
lean_dec_ref(v_modules_782_);
v_toImport_786_ = lean_ctor_get(v___x_785_, 0);
lean_inc_ref(v_toImport_786_);
lean_dec(v___x_785_);
v_module_787_ = lean_ctor_get(v_toImport_786_, 0);
lean_inc(v_module_787_);
lean_dec_ref(v_toImport_786_);
v___x_788_ = lean_box(0);
v___x_789_ = 0;
lean_inc(v_declName_771_);
v___x_790_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4(v_module_787_, v___x_789_, v_declName_771_, v___y_776_, v___y_777_);
if (lean_obj_tag(v___x_790_) == 0)
{
size_t v___x_791_; size_t v___x_792_; 
lean_dec_ref_known(v___x_790_, 1);
v___x_791_ = ((size_t)1ULL);
v___x_792_ = lean_usize_add(v_i_774_, v___x_791_);
v_i_774_ = v___x_792_;
v_b_775_ = v___x_788_;
goto _start;
}
else
{
lean_dec(v_declName_771_);
return v___x_790_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__5___boxed(lean_object* v___x_794_, lean_object* v_declName_795_, lean_object* v_as_796_, lean_object* v_sz_797_, lean_object* v_i_798_, lean_object* v_b_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
size_t v_sz_boxed_803_; size_t v_i_boxed_804_; lean_object* v_res_805_; 
v_sz_boxed_803_ = lean_unbox_usize(v_sz_797_);
lean_dec(v_sz_797_);
v_i_boxed_804_ = lean_unbox_usize(v_i_798_);
lean_dec(v_i_798_);
v_res_805_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__5(v___x_794_, v_declName_795_, v_as_796_, v_sz_boxed_803_, v_i_boxed_804_, v_b_799_, v___y_800_, v___y_801_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec_ref(v_as_796_);
lean_dec_ref(v___x_794_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg(lean_object* v_a_806_, lean_object* v_x_807_){
_start:
{
if (lean_obj_tag(v_x_807_) == 0)
{
lean_object* v___x_808_; 
v___x_808_ = lean_box(0);
return v___x_808_;
}
else
{
lean_object* v_key_809_; lean_object* v_value_810_; lean_object* v_tail_811_; uint8_t v___x_812_; 
v_key_809_ = lean_ctor_get(v_x_807_, 0);
v_value_810_ = lean_ctor_get(v_x_807_, 1);
v_tail_811_ = lean_ctor_get(v_x_807_, 2);
v___x_812_ = lean_name_eq(v_key_809_, v_a_806_);
if (v___x_812_ == 0)
{
v_x_807_ = v_tail_811_;
goto _start;
}
else
{
lean_object* v___x_814_; 
lean_inc(v_value_810_);
v___x_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_814_, 0, v_value_810_);
return v___x_814_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg___boxed(lean_object* v_a_815_, lean_object* v_x_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg(v_a_815_, v_x_816_);
lean_dec(v_x_816_);
lean_dec(v_a_815_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__6___redArg(lean_object* v_m_818_, lean_object* v_a_819_){
_start:
{
lean_object* v_buckets_820_; lean_object* v___x_821_; uint64_t v___y_823_; 
v_buckets_820_ = lean_ctor_get(v_m_818_, 1);
v___x_821_ = lean_array_get_size(v_buckets_820_);
if (lean_obj_tag(v_a_819_) == 0)
{
uint64_t v___x_837_; 
v___x_837_ = 1723ULL;
v___y_823_ = v___x_837_;
goto v___jp_822_;
}
else
{
uint64_t v_hash_838_; 
v_hash_838_ = lean_ctor_get_uint64(v_a_819_, sizeof(void*)*2);
v___y_823_ = v_hash_838_;
goto v___jp_822_;
}
v___jp_822_:
{
uint64_t v___x_824_; uint64_t v___x_825_; uint64_t v_fold_826_; uint64_t v___x_827_; uint64_t v___x_828_; uint64_t v___x_829_; size_t v___x_830_; size_t v___x_831_; size_t v___x_832_; size_t v___x_833_; size_t v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_824_ = 32ULL;
v___x_825_ = lean_uint64_shift_right(v___y_823_, v___x_824_);
v_fold_826_ = lean_uint64_xor(v___y_823_, v___x_825_);
v___x_827_ = 16ULL;
v___x_828_ = lean_uint64_shift_right(v_fold_826_, v___x_827_);
v___x_829_ = lean_uint64_xor(v_fold_826_, v___x_828_);
v___x_830_ = lean_uint64_to_usize(v___x_829_);
v___x_831_ = lean_usize_of_nat(v___x_821_);
v___x_832_ = ((size_t)1ULL);
v___x_833_ = lean_usize_sub(v___x_831_, v___x_832_);
v___x_834_ = lean_usize_land(v___x_830_, v___x_833_);
v___x_835_ = lean_array_uget_borrowed(v_buckets_820_, v___x_834_);
v___x_836_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg(v_a_819_, v___x_835_);
return v___x_836_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__6___redArg___boxed(lean_object* v_m_839_, lean_object* v_a_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__6___redArg(v_m_839_, v_a_840_);
lean_dec(v_a_840_);
lean_dec_ref(v_m_839_);
return v_res_841_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2___closed__0(void){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l_Std_HashMap_instInhabited___redArg();
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2(lean_object* v_declName_845_, uint8_t v_isMeta_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v_env_855_; lean_object* v___y_857_; lean_object* v___x_870_; 
v___x_850_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2___closed__0);
v___x_851_ = lean_st_ref_get(v___y_848_);
v_env_855_ = lean_ctor_get(v___x_851_, 0);
lean_inc_ref(v_env_855_);
lean_dec(v___x_851_);
v___x_870_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_855_, v_declName_845_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_dec_ref(v_env_855_);
lean_dec(v_declName_845_);
goto v___jp_852_;
}
else
{
lean_object* v_val_871_; lean_object* v___x_872_; lean_object* v_modules_873_; lean_object* v___x_874_; uint8_t v___x_875_; 
v_val_871_ = lean_ctor_get(v___x_870_, 0);
lean_inc(v_val_871_);
lean_dec_ref_known(v___x_870_, 1);
v___x_872_ = l_Lean_Environment_header(v_env_855_);
v_modules_873_ = lean_ctor_get(v___x_872_, 3);
lean_inc_ref(v_modules_873_);
lean_dec_ref(v___x_872_);
v___x_874_ = lean_array_get_size(v_modules_873_);
v___x_875_ = lean_nat_dec_lt(v_val_871_, v___x_874_);
if (v___x_875_ == 0)
{
lean_dec_ref(v_modules_873_);
lean_dec(v_val_871_);
lean_dec_ref(v_env_855_);
lean_dec(v_declName_845_);
goto v___jp_852_;
}
else
{
lean_object* v___x_876_; lean_object* v___x_877_; uint8_t v___y_879_; 
v___x_876_ = lean_array_fget(v_modules_873_, v_val_871_);
lean_dec(v_val_871_);
lean_dec_ref(v_modules_873_);
v___x_877_ = lean_st_ref_get(v___y_848_);
if (v_isMeta_846_ == 0)
{
lean_dec(v___x_877_);
v___y_879_ = v_isMeta_846_;
goto v___jp_878_;
}
else
{
lean_object* v_env_890_; uint8_t v___x_891_; 
v_env_890_ = lean_ctor_get(v___x_877_, 0);
lean_inc_ref(v_env_890_);
lean_dec(v___x_877_);
lean_inc(v_declName_845_);
v___x_891_ = l_Lean_isMarkedMeta(v_env_890_, v_declName_845_);
if (v___x_891_ == 0)
{
v___y_879_ = v_isMeta_846_;
goto v___jp_878_;
}
else
{
uint8_t v___x_892_; 
v___x_892_ = 0;
v___y_879_ = v___x_892_;
goto v___jp_878_;
}
}
v___jp_878_:
{
lean_object* v_toImport_880_; lean_object* v_module_881_; lean_object* v___x_882_; 
v_toImport_880_ = lean_ctor_get(v___x_876_, 0);
lean_inc_ref(v_toImport_880_);
lean_dec(v___x_876_);
v_module_881_ = lean_ctor_get(v_toImport_880_, 0);
lean_inc(v_module_881_);
lean_dec_ref(v_toImport_880_);
lean_inc(v_declName_845_);
v___x_882_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4(v_module_881_, v___y_879_, v_declName_845_, v___y_847_, v___y_848_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
lean_dec_ref_known(v___x_882_, 1);
v___x_883_ = l_Lean_indirectModUseExt;
v___x_884_ = lean_box(1);
v___x_885_ = lean_box(0);
lean_inc_ref(v_env_855_);
v___x_886_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_850_, v___x_883_, v_env_855_, v___x_884_, v___x_885_);
v___x_887_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__6___redArg(v___x_886_, v_declName_845_);
lean_dec(v___x_886_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v___x_888_; 
v___x_888_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2___closed__1));
v___y_857_ = v___x_888_;
goto v___jp_856_;
}
else
{
lean_object* v_val_889_; 
v_val_889_ = lean_ctor_get(v___x_887_, 0);
lean_inc(v_val_889_);
lean_dec_ref_known(v___x_887_, 1);
v___y_857_ = v_val_889_;
goto v___jp_856_;
}
}
else
{
lean_dec_ref(v_env_855_);
lean_dec(v_declName_845_);
return v___x_882_;
}
}
}
}
v___jp_852_:
{
lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_853_ = lean_box(0);
v___x_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_854_, 0, v___x_853_);
return v___x_854_;
}
v___jp_856_:
{
lean_object* v___x_858_; size_t v_sz_859_; size_t v___x_860_; lean_object* v___x_861_; 
v___x_858_ = lean_box(0);
v_sz_859_ = lean_array_size(v___y_857_);
v___x_860_ = ((size_t)0ULL);
v___x_861_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__5(v_env_855_, v_declName_845_, v___y_857_, v_sz_859_, v___x_860_, v___x_858_, v___y_847_, v___y_848_);
lean_dec_ref(v___y_857_);
lean_dec_ref(v_env_855_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_868_; 
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_868_ == 0)
{
lean_object* v_unused_869_; 
v_unused_869_ = lean_ctor_get(v___x_861_, 0);
lean_dec(v_unused_869_);
v___x_863_ = v___x_861_;
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
else
{
lean_dec(v___x_861_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_866_; 
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v___x_858_);
v___x_866_ = v___x_863_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v___x_858_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
else
{
return v___x_861_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2___boxed(lean_object* v_declName_893_, lean_object* v_isMeta_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
uint8_t v_isMeta_boxed_898_; lean_object* v_res_899_; 
v_isMeta_boxed_898_ = lean_unbox(v_isMeta_894_);
v_res_899_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2(v_declName_893_, v_isMeta_boxed_898_, v___y_895_, v___y_896_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
return v_res_899_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0(uint8_t v_suppressElabErrors_907_, lean_object* v_x_908_){
_start:
{
if (lean_obj_tag(v_x_908_) == 1)
{
lean_object* v_pre_909_; 
v_pre_909_ = lean_ctor_get(v_x_908_, 0);
switch(lean_obj_tag(v_pre_909_))
{
case 1:
{
lean_object* v_pre_910_; 
v_pre_910_ = lean_ctor_get(v_pre_909_, 0);
switch(lean_obj_tag(v_pre_910_))
{
case 0:
{
lean_object* v_str_911_; lean_object* v_str_912_; lean_object* v___x_913_; uint8_t v___x_914_; 
v_str_911_ = lean_ctor_get(v_x_908_, 1);
v_str_912_ = lean_ctor_get(v_pre_909_, 1);
v___x_913_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__0));
v___x_914_ = lean_string_dec_eq(v_str_912_, v___x_913_);
if (v___x_914_ == 0)
{
lean_object* v___x_915_; uint8_t v___x_916_; 
v___x_915_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__1));
v___x_916_ = lean_string_dec_eq(v_str_912_, v___x_915_);
if (v___x_916_ == 0)
{
return v___x_916_;
}
else
{
lean_object* v___x_917_; uint8_t v___x_918_; 
v___x_917_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__2));
v___x_918_ = lean_string_dec_eq(v_str_911_, v___x_917_);
if (v___x_918_ == 0)
{
return v___x_918_;
}
else
{
return v_suppressElabErrors_907_;
}
}
}
else
{
lean_object* v___x_919_; uint8_t v___x_920_; 
v___x_919_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__3));
v___x_920_ = lean_string_dec_eq(v_str_911_, v___x_919_);
if (v___x_920_ == 0)
{
return v___x_920_;
}
else
{
return v_suppressElabErrors_907_;
}
}
}
case 1:
{
lean_object* v_pre_921_; 
v_pre_921_ = lean_ctor_get(v_pre_910_, 0);
if (lean_obj_tag(v_pre_921_) == 0)
{
lean_object* v_str_922_; lean_object* v_str_923_; lean_object* v_str_924_; lean_object* v___x_925_; uint8_t v___x_926_; 
v_str_922_ = lean_ctor_get(v_x_908_, 1);
v_str_923_ = lean_ctor_get(v_pre_909_, 1);
v_str_924_ = lean_ctor_get(v_pre_910_, 1);
v___x_925_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__4));
v___x_926_ = lean_string_dec_eq(v_str_924_, v___x_925_);
if (v___x_926_ == 0)
{
return v___x_926_;
}
else
{
lean_object* v___x_927_; uint8_t v___x_928_; 
v___x_927_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__5));
v___x_928_ = lean_string_dec_eq(v_str_923_, v___x_927_);
if (v___x_928_ == 0)
{
return v___x_928_;
}
else
{
lean_object* v___x_929_; uint8_t v___x_930_; 
v___x_929_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__6));
v___x_930_ = lean_string_dec_eq(v_str_922_, v___x_929_);
if (v___x_930_ == 0)
{
return v___x_930_;
}
else
{
return v_suppressElabErrors_907_;
}
}
}
}
else
{
uint8_t v___x_931_; 
v___x_931_ = 0;
return v___x_931_;
}
}
default: 
{
uint8_t v___x_932_; 
v___x_932_ = 0;
return v___x_932_;
}
}
}
case 0:
{
lean_object* v_str_933_; lean_object* v___x_934_; uint8_t v___x_935_; 
v_str_933_ = lean_ctor_get(v_x_908_, 1);
v___x_934_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__10));
v___x_935_ = lean_string_dec_eq(v_str_933_, v___x_934_);
if (v___x_935_ == 0)
{
return v___x_935_;
}
else
{
return v_suppressElabErrors_907_;
}
}
default: 
{
uint8_t v___x_936_; 
v___x_936_ = 0;
return v___x_936_;
}
}
}
else
{
uint8_t v___x_937_; 
v___x_937_ = 0;
return v___x_937_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___boxed(lean_object* v_suppressElabErrors_938_, lean_object* v_x_939_){
_start:
{
uint8_t v_suppressElabErrors_boxed_940_; uint8_t v_res_941_; lean_object* v_r_942_; 
v_suppressElabErrors_boxed_940_ = lean_unbox(v_suppressElabErrors_938_);
v_res_941_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0(v_suppressElabErrors_boxed_940_, v_x_939_);
lean_dec(v_x_939_);
v_r_942_ = lean_box(v_res_941_);
return v_r_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5(lean_object* v_ref_943_, lean_object* v_msgData_944_, uint8_t v_severity_945_, uint8_t v_isSilent_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
uint8_t v___y_951_; lean_object* v___y_952_; uint8_t v___y_953_; lean_object* v___y_954_; lean_object* v___y_955_; lean_object* v___y_956_; lean_object* v___y_957_; lean_object* v_toCold_958_; lean_object* v___y_959_; lean_object* v___y_988_; lean_object* v___y_989_; uint8_t v___y_990_; uint8_t v___y_991_; lean_object* v___y_992_; lean_object* v___y_993_; uint8_t v___y_994_; lean_object* v___y_995_; lean_object* v___y_1015_; lean_object* v___y_1016_; uint8_t v___y_1017_; lean_object* v___y_1018_; uint8_t v___y_1019_; uint8_t v___y_1020_; lean_object* v___y_1021_; uint8_t v___y_1025_; uint8_t v___y_1026_; uint8_t v___x_1036_; uint8_t v___y_1038_; uint8_t v___x_1044_; 
v___x_1036_ = 2;
v___x_1044_ = l_Lean_instBEqMessageSeverity_beq(v_severity_945_, v___x_1036_);
if (v___x_1044_ == 0)
{
v___y_1038_ = v___x_1044_;
goto v___jp_1037_;
}
else
{
uint8_t v___x_1045_; 
lean_inc_ref(v_msgData_944_);
v___x_1045_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_944_);
if (v___x_1045_ == 0)
{
v___y_1038_ = v___x_1045_;
goto v___jp_1037_;
}
else
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
lean_dec_ref(v_msgData_944_);
v___x_1046_ = lean_box(0);
v___x_1047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
return v___x_1047_;
}
}
v___jp_950_:
{
lean_object* v_currNamespace_960_; lean_object* v_openDecls_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v_env_966_; lean_object* v_nextMacroScope_967_; lean_object* v_ngen_968_; lean_object* v_auxDeclNGen_969_; lean_object* v_traceState_970_; lean_object* v_cache_971_; lean_object* v_recordedDeps_972_; lean_object* v_messages_973_; lean_object* v_infoState_974_; lean_object* v_snapshotTasks_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_986_; 
v_currNamespace_960_ = lean_ctor_get(v_toCold_958_, 4);
v_openDecls_961_ = lean_ctor_get(v_toCold_958_, 5);
lean_inc(v_openDecls_961_);
lean_inc(v_currNamespace_960_);
v___x_962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_962_, 0, v_currNamespace_960_);
lean_ctor_set(v___x_962_, 1, v_openDecls_961_);
v___x_963_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_962_);
lean_ctor_set(v___x_963_, 1, v___y_952_);
lean_inc_ref(v___y_956_);
lean_inc_ref(v___y_957_);
v___x_964_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_964_, 0, v___y_957_);
lean_ctor_set(v___x_964_, 1, v___y_954_);
lean_ctor_set(v___x_964_, 2, v___y_955_);
lean_ctor_set(v___x_964_, 3, v___y_956_);
lean_ctor_set(v___x_964_, 4, v___x_963_);
lean_ctor_set_uint8(v___x_964_, sizeof(void*)*5, v___y_951_);
lean_ctor_set_uint8(v___x_964_, sizeof(void*)*5 + 1, v___y_953_);
lean_ctor_set_uint8(v___x_964_, sizeof(void*)*5 + 2, v_isSilent_946_);
v___x_965_ = lean_st_ref_take(v___y_959_);
v_env_966_ = lean_ctor_get(v___x_965_, 0);
v_nextMacroScope_967_ = lean_ctor_get(v___x_965_, 1);
v_ngen_968_ = lean_ctor_get(v___x_965_, 2);
v_auxDeclNGen_969_ = lean_ctor_get(v___x_965_, 3);
v_traceState_970_ = lean_ctor_get(v___x_965_, 4);
v_cache_971_ = lean_ctor_get(v___x_965_, 5);
v_recordedDeps_972_ = lean_ctor_get(v___x_965_, 6);
v_messages_973_ = lean_ctor_get(v___x_965_, 7);
v_infoState_974_ = lean_ctor_get(v___x_965_, 8);
v_snapshotTasks_975_ = lean_ctor_get(v___x_965_, 9);
v_isSharedCheck_986_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_986_ == 0)
{
v___x_977_ = v___x_965_;
v_isShared_978_ = v_isSharedCheck_986_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_snapshotTasks_975_);
lean_inc(v_infoState_974_);
lean_inc(v_messages_973_);
lean_inc(v_recordedDeps_972_);
lean_inc(v_cache_971_);
lean_inc(v_traceState_970_);
lean_inc(v_auxDeclNGen_969_);
lean_inc(v_ngen_968_);
lean_inc(v_nextMacroScope_967_);
lean_inc(v_env_966_);
lean_dec(v___x_965_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_986_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_982_; 
v___x_979_ = lean_box(0);
v___x_980_ = l_Lean_MessageLog_add(v___x_964_, v_messages_973_);
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 7, v___x_980_);
v___x_982_ = v___x_977_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_env_966_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v_nextMacroScope_967_);
lean_ctor_set(v_reuseFailAlloc_985_, 2, v_ngen_968_);
lean_ctor_set(v_reuseFailAlloc_985_, 3, v_auxDeclNGen_969_);
lean_ctor_set(v_reuseFailAlloc_985_, 4, v_traceState_970_);
lean_ctor_set(v_reuseFailAlloc_985_, 5, v_cache_971_);
lean_ctor_set(v_reuseFailAlloc_985_, 6, v_recordedDeps_972_);
lean_ctor_set(v_reuseFailAlloc_985_, 7, v___x_980_);
lean_ctor_set(v_reuseFailAlloc_985_, 8, v_infoState_974_);
lean_ctor_set(v_reuseFailAlloc_985_, 9, v_snapshotTasks_975_);
v___x_982_ = v_reuseFailAlloc_985_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = lean_st_ref_put(v___y_959_, v___x_982_);
v___x_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_984_, 0, v___x_979_);
return v___x_984_;
}
}
}
v___jp_987_:
{
lean_object* v_fileName_996_; lean_object* v_fileMap_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1013_; 
v_fileName_996_ = lean_ctor_get(v___y_993_, 0);
v_fileMap_997_ = lean_ctor_get(v___y_993_, 1);
v___x_998_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_944_);
v___x_999_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0(v___x_998_, v___y_947_, v___y_948_);
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1002_ = v___x_999_;
v_isShared_1003_ = v_isSharedCheck_1013_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_999_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1013_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
lean_inc_ref_n(v_fileMap_997_, 2);
v___x_1004_ = l_Lean_FileMap_toPosition(v_fileMap_997_, v___y_992_);
lean_dec(v___y_992_);
v___x_1005_ = l_Lean_FileMap_toPosition(v_fileMap_997_, v___y_995_);
lean_dec(v___y_995_);
v___x_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
v___x_1007_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__1));
if (v___y_994_ == 0)
{
lean_del_object(v___x_1002_);
lean_dec_ref(v___y_988_);
v___y_951_ = v___y_990_;
v___y_952_ = v_a_1000_;
v___y_953_ = v___y_991_;
v___y_954_ = v___x_1004_;
v___y_955_ = v___x_1006_;
v___y_956_ = v___x_1007_;
v___y_957_ = v_fileName_996_;
v_toCold_958_ = v___y_989_;
v___y_959_ = v___y_948_;
goto v___jp_950_;
}
else
{
uint8_t v___x_1008_; 
lean_inc(v_a_1000_);
v___x_1008_ = l_Lean_MessageData_hasTag(v___y_988_, v_a_1000_);
if (v___x_1008_ == 0)
{
lean_object* v___x_1009_; lean_object* v___x_1011_; 
lean_dec_ref_known(v___x_1006_, 1);
lean_dec_ref(v___x_1004_);
lean_dec(v_a_1000_);
v___x_1009_ = lean_box(0);
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 0, v___x_1009_);
v___x_1011_ = v___x_1002_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v___x_1009_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
else
{
lean_del_object(v___x_1002_);
v___y_951_ = v___y_990_;
v___y_952_ = v_a_1000_;
v___y_953_ = v___y_991_;
v___y_954_ = v___x_1004_;
v___y_955_ = v___x_1006_;
v___y_956_ = v___x_1007_;
v___y_957_ = v_fileName_996_;
v_toCold_958_ = v___y_989_;
v___y_959_ = v___y_948_;
goto v___jp_950_;
}
}
}
}
v___jp_1014_:
{
lean_object* v___x_1022_; 
v___x_1022_ = l_Lean_Syntax_getTailPos_x3f(v___y_1018_, v___y_1019_);
lean_dec(v___y_1018_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_inc(v___y_1021_);
v___y_988_ = v___y_1015_;
v___y_989_ = v___y_1016_;
v___y_990_ = v___y_1019_;
v___y_991_ = v___y_1020_;
v___y_992_ = v___y_1021_;
v___y_993_ = v___y_1016_;
v___y_994_ = v___y_1017_;
v___y_995_ = v___y_1021_;
goto v___jp_987_;
}
else
{
lean_object* v_val_1023_; 
v_val_1023_ = lean_ctor_get(v___x_1022_, 0);
lean_inc(v_val_1023_);
lean_dec_ref_known(v___x_1022_, 1);
v___y_988_ = v___y_1015_;
v___y_989_ = v___y_1016_;
v___y_990_ = v___y_1019_;
v___y_991_ = v___y_1020_;
v___y_992_ = v___y_1021_;
v___y_993_ = v___y_1016_;
v___y_994_ = v___y_1017_;
v___y_995_ = v_val_1023_;
goto v___jp_987_;
}
}
v___jp_1024_:
{
lean_object* v_toCold_1027_; lean_object* v_ref_1028_; uint8_t v_suppressElabErrors_1029_; lean_object* v___x_1030_; lean_object* v___f_1031_; lean_object* v_ref_1032_; lean_object* v___x_1033_; 
v_toCold_1027_ = lean_ctor_get(v___y_947_, 0);
v_ref_1028_ = lean_ctor_get(v___y_947_, 2);
v_suppressElabErrors_1029_ = lean_ctor_get_uint8(v___y_947_, sizeof(void*)*3 + 2);
v___x_1030_ = lean_box(v_suppressElabErrors_1029_);
v___f_1031_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1031_, 0, v___x_1030_);
v_ref_1032_ = l_Lean_replaceRef(v_ref_943_, v_ref_1028_);
v___x_1033_ = l_Lean_Syntax_getPos_x3f(v_ref_1032_, v___y_1025_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v___x_1034_; 
v___x_1034_ = lean_unsigned_to_nat(0u);
v___y_1015_ = v___f_1031_;
v___y_1016_ = v_toCold_1027_;
v___y_1017_ = v_suppressElabErrors_1029_;
v___y_1018_ = v_ref_1032_;
v___y_1019_ = v___y_1025_;
v___y_1020_ = v___y_1026_;
v___y_1021_ = v___x_1034_;
goto v___jp_1014_;
}
else
{
lean_object* v_val_1035_; 
v_val_1035_ = lean_ctor_get(v___x_1033_, 0);
lean_inc(v_val_1035_);
lean_dec_ref_known(v___x_1033_, 1);
v___y_1015_ = v___f_1031_;
v___y_1016_ = v_toCold_1027_;
v___y_1017_ = v_suppressElabErrors_1029_;
v___y_1018_ = v_ref_1032_;
v___y_1019_ = v___y_1025_;
v___y_1020_ = v___y_1026_;
v___y_1021_ = v_val_1035_;
goto v___jp_1014_;
}
}
v___jp_1037_:
{
uint8_t v___x_1039_; uint8_t v___x_1040_; 
v___x_1039_ = 1;
v___x_1040_ = l_Lean_instBEqMessageSeverity_beq(v_severity_945_, v___x_1039_);
if (v___x_1040_ == 0)
{
v___y_1025_ = v___y_1038_;
v___y_1026_ = v_severity_945_;
goto v___jp_1024_;
}
else
{
lean_object* v___x_1041_; lean_object* v___x_1042_; uint8_t v___x_1043_; 
v___x_1041_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_947_);
v___x_1042_ = l_Lean_warningAsError;
v___x_1043_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__5(v___x_1041_, v___x_1042_);
lean_dec_ref(v___x_1041_);
if (v___x_1043_ == 0)
{
v___y_1025_ = v___y_1038_;
v___y_1026_ = v_severity_945_;
goto v___jp_1024_;
}
else
{
v___y_1025_ = v___y_1038_;
v___y_1026_ = v___x_1036_;
goto v___jp_1024_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___boxed(lean_object* v_ref_1048_, lean_object* v_msgData_1049_, lean_object* v_severity_1050_, lean_object* v_isSilent_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
uint8_t v_severity_boxed_1055_; uint8_t v_isSilent_boxed_1056_; lean_object* v_res_1057_; 
v_severity_boxed_1055_ = lean_unbox(v_severity_1050_);
v_isSilent_boxed_1056_ = lean_unbox(v_isSilent_1051_);
v_res_1057_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5(v_ref_1048_, v_msgData_1049_, v_severity_boxed_1055_, v_isSilent_boxed_1056_, v___y_1052_, v___y_1053_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v_ref_1048_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_msgData_1058_, uint8_t v_severity_1059_, uint8_t v_isSilent_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v_ref_1064_; lean_object* v___x_1065_; 
v_ref_1064_ = lean_ctor_get(v___y_1061_, 2);
v___x_1065_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5(v_ref_1064_, v_msgData_1058_, v_severity_1059_, v_isSilent_1060_, v___y_1061_, v___y_1062_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_msgData_1066_, lean_object* v_severity_1067_, lean_object* v_isSilent_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
uint8_t v_severity_boxed_1072_; uint8_t v_isSilent_boxed_1073_; lean_object* v_res_1074_; 
v_severity_boxed_1072_ = lean_unbox(v_severity_1067_);
v_isSilent_boxed_1073_ = lean_unbox(v_isSilent_1068_);
v_res_1074_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2(v_msgData_1066_, v_severity_boxed_1072_, v_isSilent_boxed_1073_, v___y_1069_, v___y_1070_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1(lean_object* v_msgData_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_){
_start:
{
uint8_t v___x_1079_; uint8_t v___x_1080_; lean_object* v___x_1081_; 
v___x_1079_ = 1;
v___x_1080_ = 0;
v___x_1081_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2(v_msgData_1075_, v___x_1079_, v___x_1080_, v___y_1076_, v___y_1077_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1___boxed(lean_object* v_msgData_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1(v_msgData_1082_, v___y_1083_, v___y_1084_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
return v_res_1086_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__4_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1087_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1087_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__4_spec__10___redArg(){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__4_spec__10___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__4_spec__10___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__4_spec__10___redArg___closed__0);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__4_spec__10___redArg___boxed(lean_object* v___dummy_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__4_spec__10___redArg();
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__33(lean_object* v_x_1093_){
_start:
{
if (lean_obj_tag(v_x_1093_) == 0)
{
lean_object* v___x_1094_; 
v___x_1094_ = lean_box(0);
return v___x_1094_;
}
else
{
lean_object* v_head_1095_; lean_object* v_tail_1096_; lean_object* v_fst_1097_; uint8_t v___x_1098_; 
v_head_1095_ = lean_ctor_get(v_x_1093_, 0);
v_tail_1096_ = lean_ctor_get(v_x_1093_, 1);
v_fst_1097_ = lean_ctor_get(v_head_1095_, 0);
v___x_1098_ = l_Lean_isPrivateName(v_fst_1097_);
if (v___x_1098_ == 0)
{
v_x_1093_ = v_tail_1096_;
goto _start;
}
else
{
lean_object* v___x_1100_; 
lean_inc(v_head_1095_);
v___x_1100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1100_, 0, v_head_1095_);
return v___x_1100_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__33___boxed(lean_object* v_x_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__33(v_x_1101_);
lean_dec(v_x_1101_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44_spec__46_spec__49(lean_object* v_msgData_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v___x_1109_; lean_object* v_env_1110_; uint8_t v___x_1111_; lean_object* v_env_1112_; lean_object* v___x_1113_; lean_object* v_toCold_1114_; lean_object* v_mctx_1115_; lean_object* v_lctx_1116_; lean_object* v_options_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1109_ = lean_st_ref_get(v___y_1107_);
v_env_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc_ref(v_env_1110_);
lean_dec(v___x_1109_);
v___x_1111_ = 0;
v_env_1112_ = l_Lean_Environment_setRecordingDeps(v_env_1110_, v___x_1111_);
v___x_1113_ = lean_st_ref_get(v___y_1105_);
v_toCold_1114_ = lean_ctor_get(v___y_1106_, 0);
v_mctx_1115_ = lean_ctor_get(v___x_1113_, 0);
lean_inc_ref(v_mctx_1115_);
lean_dec(v___x_1113_);
v_lctx_1116_ = lean_ctor_get(v___y_1104_, 2);
v_options_1117_ = lean_ctor_get(v_toCold_1114_, 2);
lean_inc_ref(v_options_1117_);
lean_inc_ref(v_lctx_1116_);
v___x_1118_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1118_, 0, v_env_1112_);
lean_ctor_set(v___x_1118_, 1, v_mctx_1115_);
lean_ctor_set(v___x_1118_, 2, v_lctx_1116_);
lean_ctor_set(v___x_1118_, 3, v_options_1117_);
v___x_1119_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1118_);
lean_ctor_set(v___x_1119_, 1, v_msgData_1103_);
v___x_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44_spec__46_spec__49___boxed(lean_object* v_msgData_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44_spec__46_spec__49(v_msgData_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46_spec__48_spec__50(lean_object* v_ref_1130_, lean_object* v_msgData_1131_, uint8_t v_severity_1132_, uint8_t v_isSilent_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
lean_object* v_a_1140_; lean_object* v___y_1144_; lean_object* v___y_1145_; lean_object* v___y_1146_; uint8_t v___y_1147_; lean_object* v___y_1148_; uint8_t v___y_1149_; lean_object* v___y_1150_; lean_object* v_toCold_1151_; lean_object* v___y_1152_; lean_object* v___y_1180_; lean_object* v___y_1181_; uint8_t v___y_1182_; lean_object* v___y_1183_; uint8_t v___y_1184_; uint8_t v___y_1185_; lean_object* v___y_1186_; lean_object* v___y_1187_; lean_object* v___y_1206_; uint8_t v___y_1207_; lean_object* v___y_1208_; uint8_t v___y_1209_; lean_object* v___y_1210_; uint8_t v___y_1211_; lean_object* v___y_1212_; uint8_t v___y_1216_; uint8_t v___y_1217_; uint8_t v___x_1227_; uint8_t v___y_1229_; uint8_t v___x_1235_; 
v___x_1227_ = 2;
v___x_1235_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1132_, v___x_1227_);
if (v___x_1235_ == 0)
{
v___y_1229_ = v___x_1235_;
goto v___jp_1228_;
}
else
{
uint8_t v___x_1236_; 
lean_inc_ref(v_msgData_1131_);
v___x_1236_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1131_);
if (v___x_1236_ == 0)
{
v___y_1229_ = v___x_1236_;
goto v___jp_1228_;
}
else
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
lean_dec_ref(v_msgData_1131_);
v___x_1237_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46_spec__48_spec__50___closed__0));
v___x_1238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1237_);
return v___x_1238_;
}
}
v___jp_1139_:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1141_, 0, v_a_1140_);
v___x_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1141_);
return v___x_1142_;
}
v___jp_1143_:
{
lean_object* v_currNamespace_1153_; lean_object* v_openDecls_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v_env_1159_; lean_object* v_nextMacroScope_1160_; lean_object* v_ngen_1161_; lean_object* v_auxDeclNGen_1162_; lean_object* v_traceState_1163_; lean_object* v_cache_1164_; lean_object* v_recordedDeps_1165_; lean_object* v_messages_1166_; lean_object* v_infoState_1167_; lean_object* v_snapshotTasks_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1178_; 
v_currNamespace_1153_ = lean_ctor_get(v_toCold_1151_, 4);
v_openDecls_1154_ = lean_ctor_get(v_toCold_1151_, 5);
lean_inc(v_openDecls_1154_);
lean_inc(v_currNamespace_1153_);
v___x_1155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1155_, 0, v_currNamespace_1153_);
lean_ctor_set(v___x_1155_, 1, v_openDecls_1154_);
v___x_1156_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1155_);
lean_ctor_set(v___x_1156_, 1, v___y_1145_);
lean_inc_ref(v___y_1146_);
lean_inc_ref(v___y_1148_);
v___x_1157_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1157_, 0, v___y_1148_);
lean_ctor_set(v___x_1157_, 1, v___y_1150_);
lean_ctor_set(v___x_1157_, 2, v___y_1144_);
lean_ctor_set(v___x_1157_, 3, v___y_1146_);
lean_ctor_set(v___x_1157_, 4, v___x_1156_);
lean_ctor_set_uint8(v___x_1157_, sizeof(void*)*5, v___y_1149_);
lean_ctor_set_uint8(v___x_1157_, sizeof(void*)*5 + 1, v___y_1147_);
lean_ctor_set_uint8(v___x_1157_, sizeof(void*)*5 + 2, v_isSilent_1133_);
v___x_1158_ = lean_st_ref_take(v___y_1152_);
v_env_1159_ = lean_ctor_get(v___x_1158_, 0);
v_nextMacroScope_1160_ = lean_ctor_get(v___x_1158_, 1);
v_ngen_1161_ = lean_ctor_get(v___x_1158_, 2);
v_auxDeclNGen_1162_ = lean_ctor_get(v___x_1158_, 3);
v_traceState_1163_ = lean_ctor_get(v___x_1158_, 4);
v_cache_1164_ = lean_ctor_get(v___x_1158_, 5);
v_recordedDeps_1165_ = lean_ctor_get(v___x_1158_, 6);
v_messages_1166_ = lean_ctor_get(v___x_1158_, 7);
v_infoState_1167_ = lean_ctor_get(v___x_1158_, 8);
v_snapshotTasks_1168_ = lean_ctor_get(v___x_1158_, 9);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1170_ = v___x_1158_;
v_isShared_1171_ = v_isSharedCheck_1178_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_snapshotTasks_1168_);
lean_inc(v_infoState_1167_);
lean_inc(v_messages_1166_);
lean_inc(v_recordedDeps_1165_);
lean_inc(v_cache_1164_);
lean_inc(v_traceState_1163_);
lean_inc(v_auxDeclNGen_1162_);
lean_inc(v_ngen_1161_);
lean_inc(v_nextMacroScope_1160_);
lean_inc(v_env_1159_);
lean_dec(v___x_1158_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1178_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1175_; 
v___x_1172_ = lean_box(0);
v___x_1173_ = l_Lean_MessageLog_add(v___x_1157_, v_messages_1166_);
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 7, v___x_1173_);
v___x_1175_ = v___x_1170_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_env_1159_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v_nextMacroScope_1160_);
lean_ctor_set(v_reuseFailAlloc_1177_, 2, v_ngen_1161_);
lean_ctor_set(v_reuseFailAlloc_1177_, 3, v_auxDeclNGen_1162_);
lean_ctor_set(v_reuseFailAlloc_1177_, 4, v_traceState_1163_);
lean_ctor_set(v_reuseFailAlloc_1177_, 5, v_cache_1164_);
lean_ctor_set(v_reuseFailAlloc_1177_, 6, v_recordedDeps_1165_);
lean_ctor_set(v_reuseFailAlloc_1177_, 7, v___x_1173_);
lean_ctor_set(v_reuseFailAlloc_1177_, 8, v_infoState_1167_);
lean_ctor_set(v_reuseFailAlloc_1177_, 9, v_snapshotTasks_1168_);
v___x_1175_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
lean_object* v___x_1176_; 
v___x_1176_ = lean_st_ref_put(v___y_1152_, v___x_1175_);
v_a_1140_ = v___x_1172_;
goto v___jp_1139_;
}
}
}
v___jp_1179_:
{
lean_object* v_fileName_1188_; lean_object* v_fileMap_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1204_; 
v_fileName_1188_ = lean_ctor_get(v___y_1183_, 0);
v_fileMap_1189_ = lean_ctor_get(v___y_1183_, 1);
v___x_1190_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1131_);
v___x_1191_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44_spec__46_spec__49(v___x_1190_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1194_ = v___x_1191_;
v_isShared_1195_ = v_isSharedCheck_1204_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1191_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1204_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1199_; 
lean_inc_ref_n(v_fileMap_1189_, 2);
v___x_1196_ = l_Lean_FileMap_toPosition(v_fileMap_1189_, v___y_1186_);
lean_dec(v___y_1186_);
v___x_1197_ = l_Lean_FileMap_toPosition(v_fileMap_1189_, v___y_1187_);
lean_dec(v___y_1187_);
if (v_isShared_1195_ == 0)
{
lean_ctor_set_tag(v___x_1194_, 1);
lean_ctor_set(v___x_1194_, 0, v___x_1197_);
v___x_1199_ = v___x_1194_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1197_);
v___x_1199_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
lean_object* v___x_1200_; 
v___x_1200_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__1));
if (v___y_1182_ == 0)
{
lean_dec_ref(v___y_1180_);
v___y_1144_ = v___x_1199_;
v___y_1145_ = v_a_1192_;
v___y_1146_ = v___x_1200_;
v___y_1147_ = v___y_1184_;
v___y_1148_ = v_fileName_1188_;
v___y_1149_ = v___y_1185_;
v___y_1150_ = v___x_1196_;
v_toCold_1151_ = v___y_1181_;
v___y_1152_ = v___y_1137_;
goto v___jp_1143_;
}
else
{
uint8_t v___x_1201_; 
lean_inc(v_a_1192_);
v___x_1201_ = l_Lean_MessageData_hasTag(v___y_1180_, v_a_1192_);
if (v___x_1201_ == 0)
{
lean_object* v___x_1202_; 
lean_dec_ref(v___x_1199_);
lean_dec_ref(v___x_1196_);
lean_dec(v_a_1192_);
v___x_1202_ = lean_box(0);
v_a_1140_ = v___x_1202_;
goto v___jp_1139_;
}
else
{
v___y_1144_ = v___x_1199_;
v___y_1145_ = v_a_1192_;
v___y_1146_ = v___x_1200_;
v___y_1147_ = v___y_1184_;
v___y_1148_ = v_fileName_1188_;
v___y_1149_ = v___y_1185_;
v___y_1150_ = v___x_1196_;
v_toCold_1151_ = v___y_1181_;
v___y_1152_ = v___y_1137_;
goto v___jp_1143_;
}
}
}
}
}
v___jp_1205_:
{
lean_object* v___x_1213_; 
v___x_1213_ = l_Lean_Syntax_getTailPos_x3f(v___y_1210_, v___y_1211_);
lean_dec(v___y_1210_);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_inc(v___y_1212_);
v___y_1180_ = v___y_1206_;
v___y_1181_ = v___y_1208_;
v___y_1182_ = v___y_1207_;
v___y_1183_ = v___y_1208_;
v___y_1184_ = v___y_1209_;
v___y_1185_ = v___y_1211_;
v___y_1186_ = v___y_1212_;
v___y_1187_ = v___y_1212_;
goto v___jp_1179_;
}
else
{
lean_object* v_val_1214_; 
v_val_1214_ = lean_ctor_get(v___x_1213_, 0);
lean_inc(v_val_1214_);
lean_dec_ref_known(v___x_1213_, 1);
v___y_1180_ = v___y_1206_;
v___y_1181_ = v___y_1208_;
v___y_1182_ = v___y_1207_;
v___y_1183_ = v___y_1208_;
v___y_1184_ = v___y_1209_;
v___y_1185_ = v___y_1211_;
v___y_1186_ = v___y_1212_;
v___y_1187_ = v_val_1214_;
goto v___jp_1179_;
}
}
v___jp_1215_:
{
lean_object* v_toCold_1218_; lean_object* v_ref_1219_; uint8_t v_suppressElabErrors_1220_; lean_object* v___x_1221_; lean_object* v___f_1222_; lean_object* v_ref_1223_; lean_object* v___x_1224_; 
v_toCold_1218_ = lean_ctor_get(v___y_1136_, 0);
v_ref_1219_ = lean_ctor_get(v___y_1136_, 2);
v_suppressElabErrors_1220_ = lean_ctor_get_uint8(v___y_1136_, sizeof(void*)*3 + 2);
v___x_1221_ = lean_box(v_suppressElabErrors_1220_);
v___f_1222_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1222_, 0, v___x_1221_);
v_ref_1223_ = l_Lean_replaceRef(v_ref_1130_, v_ref_1219_);
v___x_1224_ = l_Lean_Syntax_getPos_x3f(v_ref_1223_, v___y_1216_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v___x_1225_; 
v___x_1225_ = lean_unsigned_to_nat(0u);
v___y_1206_ = v___f_1222_;
v___y_1207_ = v_suppressElabErrors_1220_;
v___y_1208_ = v_toCold_1218_;
v___y_1209_ = v___y_1217_;
v___y_1210_ = v_ref_1223_;
v___y_1211_ = v___y_1216_;
v___y_1212_ = v___x_1225_;
goto v___jp_1205_;
}
else
{
lean_object* v_val_1226_; 
v_val_1226_ = lean_ctor_get(v___x_1224_, 0);
lean_inc(v_val_1226_);
lean_dec_ref_known(v___x_1224_, 1);
v___y_1206_ = v___f_1222_;
v___y_1207_ = v_suppressElabErrors_1220_;
v___y_1208_ = v_toCold_1218_;
v___y_1209_ = v___y_1217_;
v___y_1210_ = v_ref_1223_;
v___y_1211_ = v___y_1216_;
v___y_1212_ = v_val_1226_;
goto v___jp_1205_;
}
}
v___jp_1228_:
{
uint8_t v___x_1230_; uint8_t v___x_1231_; 
v___x_1230_ = 1;
v___x_1231_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1132_, v___x_1230_);
if (v___x_1231_ == 0)
{
v___y_1216_ = v___y_1229_;
v___y_1217_ = v_severity_1132_;
goto v___jp_1215_;
}
else
{
lean_object* v___x_1232_; lean_object* v___x_1233_; uint8_t v___x_1234_; 
v___x_1232_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1136_);
v___x_1233_ = l_Lean_warningAsError;
v___x_1234_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__5(v___x_1232_, v___x_1233_);
lean_dec_ref(v___x_1232_);
if (v___x_1234_ == 0)
{
v___y_1216_ = v___y_1229_;
v___y_1217_ = v_severity_1132_;
goto v___jp_1215_;
}
else
{
v___y_1216_ = v___y_1229_;
v___y_1217_ = v___x_1227_;
goto v___jp_1215_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46_spec__48_spec__50___boxed(lean_object* v_ref_1239_, lean_object* v_msgData_1240_, lean_object* v_severity_1241_, lean_object* v_isSilent_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
uint8_t v_severity_boxed_1248_; uint8_t v_isSilent_boxed_1249_; lean_object* v_res_1250_; 
v_severity_boxed_1248_ = lean_unbox(v_severity_1241_);
v_isSilent_boxed_1249_ = lean_unbox(v_isSilent_1242_);
v_res_1250_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46_spec__48_spec__50(v_ref_1239_, v_msgData_1240_, v_severity_boxed_1248_, v_isSilent_boxed_1249_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v_ref_1239_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46_spec__48(lean_object* v_msgData_1251_, uint8_t v_severity_1252_, uint8_t v_isSilent_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v_ref_1259_; lean_object* v___x_1260_; 
v_ref_1259_ = lean_ctor_get(v___y_1256_, 2);
v___x_1260_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46_spec__48_spec__50(v_ref_1259_, v_msgData_1251_, v_severity_1252_, v_isSilent_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46_spec__48___boxed(lean_object* v_msgData_1261_, lean_object* v_severity_1262_, lean_object* v_isSilent_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_){
_start:
{
uint8_t v_severity_boxed_1269_; uint8_t v_isSilent_boxed_1270_; lean_object* v_res_1271_; 
v_severity_boxed_1269_ = lean_unbox(v_severity_1262_);
v_isSilent_boxed_1270_ = lean_unbox(v_isSilent_1263_);
v_res_1271_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46_spec__48(v_msgData_1261_, v_severity_boxed_1269_, v_isSilent_boxed_1270_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46(lean_object* v_msgData_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
uint8_t v___x_1278_; uint8_t v___x_1279_; lean_object* v___x_1280_; 
v___x_1278_ = 1;
v___x_1279_ = 0;
v___x_1280_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46_spec__48(v_msgData_1272_, v___x_1278_, v___x_1279_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46___boxed(lean_object* v_msgData_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46(v_msgData_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__45___redArg(lean_object* v_opt_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v___x_1291_; uint8_t v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1291_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1289_);
v___x_1292_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__5(v___x_1291_, v_opt_1288_);
lean_dec_ref(v___x_1291_);
v___x_1293_ = lean_box(v___x_1292_);
v___x_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1293_);
v___x_1295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1294_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__45___redArg___boxed(lean_object* v_opt_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__45___redArg(v_opt_1296_, v___y_1297_);
lean_dec_ref(v___y_1297_);
lean_dec_ref(v_opt_1296_);
return v_res_1299_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___closed__1(void){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___closed__0));
v___x_1302_ = l_Lean_stringToMessageData(v___x_1301_);
return v___x_1302_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___closed__3(void){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1304_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___closed__2));
v___x_1305_ = l_Lean_stringToMessageData(v___x_1304_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42(lean_object* v_id_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
lean_object* v___x_1312_; lean_object* v_env_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1336_; 
v___x_1312_ = lean_st_ref_get(v___y_1310_);
v_env_1313_ = lean_ctor_get(v___x_1312_, 0);
lean_inc_ref(v_env_1313_);
lean_dec(v___x_1312_);
v___x_1314_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1315_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__45___redArg(v___x_1314_, v___y_1309_);
v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1318_ = v___x_1315_;
v_isShared_1319_ = v_isSharedCheck_1336_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1315_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1336_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
uint8_t v_isExporting_1325_; 
v_isExporting_1325_ = lean_ctor_get_uint8(v_env_1313_, sizeof(void*)*13);
lean_dec_ref(v_env_1313_);
if (v_isExporting_1325_ == 0)
{
lean_dec(v_a_1316_);
lean_dec(v_id_1306_);
goto v___jp_1320_;
}
else
{
lean_object* v_val_1326_; uint8_t v___x_1327_; 
v_val_1326_ = lean_ctor_get(v_a_1316_, 0);
lean_inc(v_val_1326_);
lean_dec(v_a_1316_);
v___x_1327_ = l_Lean_isPrivateName(v_id_1306_);
if (v___x_1327_ == 0)
{
lean_dec(v_val_1326_);
lean_dec(v_id_1306_);
goto v___jp_1320_;
}
else
{
uint8_t v___x_1328_; 
v___x_1328_ = lean_unbox(v_val_1326_);
lean_dec(v_val_1326_);
if (v___x_1328_ == 0)
{
lean_dec(v_id_1306_);
goto v___jp_1320_;
}
else
{
lean_object* v___x_1329_; uint8_t v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
lean_del_object(v___x_1318_);
v___x_1329_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___closed__1);
v___x_1330_ = 0;
v___x_1331_ = l_Lean_MessageData_ofConstName(v_id_1306_, v___x_1330_);
v___x_1332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1329_);
lean_ctor_set(v___x_1332_, 1, v___x_1331_);
v___x_1333_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___closed__3);
v___x_1334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1332_);
lean_ctor_set(v___x_1334_, 1, v___x_1333_);
v___x_1335_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46(v___x_1334_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_);
return v___x_1335_;
}
}
}
v___jp_1320_:
{
lean_object* v___x_1321_; lean_object* v___x_1323_; 
v___x_1321_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46_spec__48_spec__50___closed__0));
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 0, v___x_1321_);
v___x_1323_ = v___x_1318_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v___x_1321_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___boxed(lean_object* v_id_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42(v_id_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36(lean_object* v_id_1344_, uint8_t v_enableLog_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v___x_1351_; lean_object* v_toCold_1352_; lean_object* v_env_1353_; lean_object* v_currNamespace_1354_; lean_object* v_openDecls_1355_; lean_object* v___x_1356_; lean_object* v_res_1357_; lean_object* v___x_1361_; 
v___x_1351_ = lean_st_ref_get(v___y_1349_);
v_toCold_1352_ = lean_ctor_get(v___y_1348_, 0);
v_env_1353_ = lean_ctor_get(v___x_1351_, 0);
lean_inc_ref(v_env_1353_);
lean_dec(v___x_1351_);
v_currNamespace_1354_ = lean_ctor_get(v_toCold_1352_, 4);
v_openDecls_1355_ = lean_ctor_get(v_toCold_1352_, 5);
v___x_1356_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1348_);
lean_inc(v_openDecls_1355_);
lean_inc(v_currNamespace_1354_);
v_res_1357_ = l_Lean_ResolveName_resolveGlobalName(v_env_1353_, v___x_1356_, v_currNamespace_1354_, v_openDecls_1355_, v_id_1344_);
lean_dec_ref(v___x_1356_);
v___x_1361_ = lean_st_ref_get(v___y_1349_);
if (v_enableLog_1345_ == 0)
{
lean_dec(v___x_1361_);
goto v___jp_1358_;
}
else
{
lean_object* v_env_1362_; uint8_t v_isExporting_1363_; 
v_env_1362_ = lean_ctor_get(v___x_1361_, 0);
lean_inc_ref(v_env_1362_);
lean_dec(v___x_1361_);
v_isExporting_1363_ = lean_ctor_get_uint8(v_env_1362_, sizeof(void*)*13);
lean_dec_ref(v_env_1362_);
if (v_isExporting_1363_ == 0)
{
goto v___jp_1358_;
}
else
{
lean_object* v___x_1364_; 
v___x_1364_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__33(v_res_1357_);
if (lean_obj_tag(v___x_1364_) == 1)
{
lean_object* v_val_1365_; lean_object* v_fst_1366_; lean_object* v___x_1367_; 
v_val_1365_ = lean_ctor_get(v___x_1364_, 0);
lean_inc(v_val_1365_);
lean_dec_ref_known(v___x_1364_, 1);
v_fst_1366_ = lean_ctor_get(v_val_1365_, 0);
lean_inc(v_fst_1366_);
lean_dec(v_val_1365_);
v___x_1367_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42(v_fst_1366_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1376_; 
v_a_1368_ = lean_ctor_get(v___x_1367_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1370_ = v___x_1367_;
v_isShared_1371_ = v_isSharedCheck_1376_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1367_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1376_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
if (lean_obj_tag(v_a_1368_) == 0)
{
lean_object* v___x_1372_; lean_object* v___x_1374_; 
lean_dec(v_res_1357_);
v___x_1372_ = lean_box(0);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 0, v___x_1372_);
v___x_1374_ = v___x_1370_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v___x_1372_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
else
{
lean_dec_ref_known(v_a_1368_, 1);
lean_del_object(v___x_1370_);
goto v___jp_1358_;
}
}
}
else
{
lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1384_; 
lean_dec(v_res_1357_);
v_a_1377_ = lean_ctor_get(v___x_1367_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1379_ = v___x_1367_;
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1367_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1382_; 
if (v_isShared_1380_ == 0)
{
v___x_1382_ = v___x_1379_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_a_1377_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
}
else
{
lean_dec(v___x_1364_);
goto v___jp_1358_;
}
}
}
v___jp_1358_:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1359_, 0, v_res_1357_);
v___x_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1359_);
return v___x_1360_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36___boxed(lean_object* v_id_1385_, lean_object* v_enableLog_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
uint8_t v_enableLog_boxed_1392_; lean_object* v_res_1393_; 
v_enableLog_boxed_1392_ = lean_unbox(v_enableLog_1386_);
v_res_1393_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36(v_id_1385_, v_enableLog_boxed_1392_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24___lam__0(lean_object* v___x_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v___x_1400_; 
v___x_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1394_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24___lam__0___boxed(lean_object* v___x_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24___lam__0(v___x_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27(lean_object* v_n_u2080_1412_, lean_object* v_filter_1413_, lean_object* v_view_x3f_1414_, lean_object* v_n_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1491_; 
if (lean_obj_tag(v_view_x3f_1414_) == 1)
{
lean_object* v_val_1518_; lean_object* v_imported_1519_; lean_object* v_ctx_1520_; lean_object* v_scopes_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1529_; 
v_val_1518_ = lean_ctor_get(v_view_x3f_1414_, 0);
lean_inc(v_val_1518_);
lean_dec_ref_known(v_view_x3f_1414_, 1);
v_imported_1519_ = lean_ctor_get(v_val_1518_, 1);
v_ctx_1520_ = lean_ctor_get(v_val_1518_, 2);
v_scopes_1521_ = lean_ctor_get(v_val_1518_, 3);
v_isSharedCheck_1529_ = !lean_is_exclusive(v_val_1518_);
if (v_isSharedCheck_1529_ == 0)
{
lean_object* v_unused_1530_; 
v_unused_1530_ = lean_ctor_get(v_val_1518_, 0);
lean_dec(v_unused_1530_);
v___x_1523_ = v_val_1518_;
v_isShared_1524_ = v_isSharedCheck_1529_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_scopes_1521_);
lean_inc(v_ctx_1520_);
lean_inc(v_imported_1519_);
lean_dec(v_val_1518_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1529_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1526_; 
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 0, v_n_1415_);
v___x_1526_ = v___x_1523_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_n_1415_);
lean_ctor_set(v_reuseFailAlloc_1528_, 1, v_imported_1519_);
lean_ctor_set(v_reuseFailAlloc_1528_, 2, v_ctx_1520_);
lean_ctor_set(v_reuseFailAlloc_1528_, 3, v_scopes_1521_);
v___x_1526_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
lean_object* v___x_1527_; 
v___x_1527_ = l_Lean_MacroScopesView_review(v___x_1526_);
v___y_1491_ = v___x_1527_;
goto v___jp_1490_;
}
}
}
else
{
lean_dec(v_view_x3f_1414_);
v___y_1491_ = v_n_1415_;
goto v___jp_1490_;
}
v___jp_1421_:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1422_ = lean_box(0);
v___x_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1422_);
return v___x_1423_;
}
v___jp_1424_:
{
lean_object* v___x_1427_; 
lean_inc_ref(v___y_1426_);
lean_inc(v___y_1419_);
lean_inc_ref(v___y_1418_);
lean_inc(v___y_1417_);
lean_inc_ref(v___y_1416_);
v___x_1427_ = lean_apply_5(v___y_1426_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, lean_box(0));
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1447_; 
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1430_ = v___x_1427_;
v_isShared_1431_ = v_isSharedCheck_1447_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1427_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1447_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
if (lean_obj_tag(v_a_1428_) == 0)
{
lean_object* v___x_1432_; lean_object* v___x_1434_; 
lean_dec(v___y_1425_);
v___x_1432_ = lean_box(0);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v___x_1432_);
v___x_1434_ = v___x_1430_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1432_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
else
{
lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1445_; 
v_isSharedCheck_1445_ = !lean_is_exclusive(v_a_1428_);
if (v_isSharedCheck_1445_ == 0)
{
lean_object* v_unused_1446_; 
v_unused_1446_ = lean_ctor_get(v_a_1428_, 0);
lean_dec(v_unused_1446_);
v___x_1437_ = v_a_1428_;
v_isShared_1438_ = v_isSharedCheck_1445_;
goto v_resetjp_1436_;
}
else
{
lean_dec(v_a_1428_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1445_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1440_; 
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 0, v___y_1425_);
v___x_1440_ = v___x_1437_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___y_1425_);
v___x_1440_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
lean_object* v___x_1442_; 
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v___x_1440_);
v___x_1442_ = v___x_1430_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1440_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
}
}
}
else
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1455_; 
lean_dec(v___y_1425_);
v_a_1448_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1450_ = v___x_1427_;
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1427_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1453_; 
if (v_isShared_1451_ == 0)
{
v___x_1453_ = v___x_1450_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_a_1448_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
}
v___jp_1456_:
{
lean_object* v___x_1459_; 
lean_inc_ref(v___y_1458_);
lean_inc(v___y_1419_);
lean_inc_ref(v___y_1418_);
lean_inc(v___y_1417_);
lean_inc_ref(v___y_1416_);
v___x_1459_ = lean_apply_5(v___y_1458_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, lean_box(0));
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1481_; 
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1462_ = v___x_1459_;
v_isShared_1463_ = v_isSharedCheck_1481_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1459_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1481_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
if (lean_obj_tag(v_a_1460_) == 0)
{
lean_object* v___x_1464_; lean_object* v___x_1466_; 
lean_dec(v___y_1457_);
lean_dec_ref(v_filter_1413_);
v___x_1464_ = lean_box(0);
if (v_isShared_1463_ == 0)
{
lean_ctor_set(v___x_1462_, 0, v___x_1464_);
v___x_1466_ = v___x_1462_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v___x_1464_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
else
{
lean_object* v___x_1468_; 
lean_dec_ref_known(v_a_1460_, 1);
lean_del_object(v___x_1462_);
lean_inc(v___y_1419_);
lean_inc_ref(v___y_1418_);
lean_inc(v___y_1417_);
lean_inc_ref(v___y_1416_);
lean_inc(v___y_1457_);
v___x_1468_ = lean_apply_6(v_filter_1413_, v___y_1457_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, lean_box(0));
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_object* v_a_1469_; uint8_t v___x_1470_; 
v_a_1469_ = lean_ctor_get(v___x_1468_, 0);
lean_inc(v_a_1469_);
lean_dec_ref_known(v___x_1468_, 1);
v___x_1470_ = lean_unbox(v_a_1469_);
lean_dec(v_a_1469_);
if (v___x_1470_ == 0)
{
lean_object* v___f_1471_; 
v___f_1471_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27___closed__0));
v___y_1425_ = v___y_1457_;
v___y_1426_ = v___f_1471_;
goto v___jp_1424_;
}
else
{
lean_object* v___f_1472_; 
v___f_1472_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27___closed__1));
v___y_1425_ = v___y_1457_;
v___y_1426_ = v___f_1472_;
goto v___jp_1424_;
}
}
else
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
lean_dec(v___y_1457_);
v_a_1473_ = lean_ctor_get(v___x_1468_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1475_ = v___x_1468_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1468_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1473_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
}
}
else
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1489_; 
lean_dec(v___y_1457_);
lean_dec_ref(v_filter_1413_);
v_a_1482_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1484_ = v___x_1459_;
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1459_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1487_; 
if (v_isShared_1485_ == 0)
{
v___x_1487_ = v___x_1484_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1482_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
}
v___jp_1490_:
{
uint8_t v___x_1492_; lean_object* v___x_1493_; 
v___x_1492_ = 0;
lean_inc(v___y_1491_);
v___x_1493_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36(v___y_1491_, v___x_1492_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_object* v_a_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1509_; 
v_a_1494_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1496_ = v___x_1493_;
v_isShared_1497_ = v_isSharedCheck_1509_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_a_1494_);
lean_dec(v___x_1493_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1509_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
if (lean_obj_tag(v_a_1494_) == 0)
{
lean_object* v___x_1498_; lean_object* v___x_1500_; 
lean_dec(v___y_1491_);
lean_dec_ref(v_filter_1413_);
v___x_1498_ = lean_box(0);
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 0, v___x_1498_);
v___x_1500_ = v___x_1496_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1498_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
else
{
lean_object* v_val_1502_; 
lean_del_object(v___x_1496_);
v_val_1502_ = lean_ctor_get(v_a_1494_, 0);
lean_inc(v_val_1502_);
lean_dec_ref_known(v_a_1494_, 1);
if (lean_obj_tag(v_val_1502_) == 1)
{
lean_object* v_head_1503_; lean_object* v_tail_1504_; 
v_head_1503_ = lean_ctor_get(v_val_1502_, 0);
lean_inc(v_head_1503_);
v_tail_1504_ = lean_ctor_get(v_val_1502_, 1);
lean_inc(v_tail_1504_);
lean_dec_ref_known(v_val_1502_, 2);
if (lean_obj_tag(v_tail_1504_) == 0)
{
lean_object* v_fst_1505_; uint8_t v___x_1506_; 
v_fst_1505_ = lean_ctor_get(v_head_1503_, 0);
lean_inc(v_fst_1505_);
lean_dec(v_head_1503_);
v___x_1506_ = lean_name_eq(v_fst_1505_, v_n_u2080_1412_);
lean_dec(v_fst_1505_);
if (v___x_1506_ == 0)
{
lean_object* v___f_1507_; 
v___f_1507_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27___closed__0));
v___y_1457_ = v___y_1491_;
v___y_1458_ = v___f_1507_;
goto v___jp_1456_;
}
else
{
lean_object* v___f_1508_; 
v___f_1508_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27___closed__1));
v___y_1457_ = v___y_1491_;
v___y_1458_ = v___f_1508_;
goto v___jp_1456_;
}
}
else
{
lean_dec(v_tail_1504_);
lean_dec(v_head_1503_);
lean_dec(v___y_1491_);
lean_dec_ref(v_filter_1413_);
goto v___jp_1421_;
}
}
else
{
lean_dec(v_val_1502_);
lean_dec(v___y_1491_);
lean_dec_ref(v_filter_1413_);
goto v___jp_1421_;
}
}
}
}
else
{
lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1517_; 
lean_dec(v___y_1491_);
lean_dec_ref(v_filter_1413_);
v_a_1510_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1512_ = v___x_1493_;
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___x_1493_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1515_; 
if (v_isShared_1513_ == 0)
{
v___x_1515_ = v___x_1512_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_a_1510_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27___boxed(lean_object* v_n_u2080_1531_, lean_object* v_filter_1532_, lean_object* v_view_x3f_1533_, lean_object* v_n_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v_res_1540_; 
v_res_1540_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27(v_n_u2080_1531_, v_filter_1532_, v_view_x3f_1533_, v_n_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
lean_dec(v_n_u2080_1531_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24_spec__32___redArg(lean_object* v_n_u2080_1541_, lean_object* v_filter_1542_, lean_object* v_view_x3f_1543_, lean_object* v_a_1544_, lean_object* v_b_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_){
_start:
{
lean_object* v___x_1551_; lean_object* v_it_1553_; lean_object* v_out_1554_; lean_object* v___x_1594_; 
v___x_1551_ = lean_box(0);
v___x_1594_ = lean_box(0);
switch(lean_obj_tag(v_a_1544_))
{
case 0:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; 
lean_dec(v_view_x3f_1543_);
lean_dec_ref(v_filter_1542_);
v___x_1595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1595_, 0, v_b_1545_);
v___x_1596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1595_);
return v___x_1596_;
}
case 1:
{
lean_object* v_pre_1597_; lean_object* v_str_1598_; lean_object* v___x_1599_; 
v_pre_1597_ = lean_ctor_get(v_a_1544_, 0);
lean_inc(v_pre_1597_);
v_str_1598_ = lean_ctor_get(v_a_1544_, 1);
lean_inc_ref(v_str_1598_);
lean_dec_ref_known(v_a_1544_, 2);
v___x_1599_ = l_Lean_Name_str___override(v___x_1594_, v_str_1598_);
v_it_1553_ = v_pre_1597_;
v_out_1554_ = v___x_1599_;
goto v___jp_1552_;
}
default: 
{
lean_object* v_pre_1600_; lean_object* v_i_1601_; lean_object* v___x_1602_; 
v_pre_1600_ = lean_ctor_get(v_a_1544_, 0);
lean_inc(v_pre_1600_);
v_i_1601_ = lean_ctor_get(v_a_1544_, 1);
lean_inc(v_i_1601_);
lean_dec_ref_known(v_a_1544_, 2);
v___x_1602_ = l_Lean_Name_num___override(v___x_1594_, v_i_1601_);
v_it_1553_ = v_pre_1600_;
v_out_1554_ = v___x_1602_;
goto v___jp_1552_;
}
}
v___jp_1552_:
{
lean_object* v_snd_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1592_; 
v_snd_1555_ = lean_ctor_get(v_b_1545_, 1);
v_isSharedCheck_1592_ = !lean_is_exclusive(v_b_1545_);
if (v_isSharedCheck_1592_ == 0)
{
lean_object* v_unused_1593_; 
v_unused_1593_ = lean_ctor_get(v_b_1545_, 0);
lean_dec(v_unused_1593_);
v___x_1557_ = v_b_1545_;
v_isShared_1558_ = v_isSharedCheck_1592_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_snd_1555_);
lean_dec(v_b_1545_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1592_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1559_ = l_Lean_Name_appendCore(v_out_1554_, v_snd_1555_);
lean_dec(v_out_1554_);
lean_inc(v___x_1559_);
lean_inc(v_view_x3f_1543_);
lean_inc_ref(v_filter_1542_);
v___x_1560_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27(v_n_u2080_1541_, v_filter_1542_, v_view_x3f_1543_, v___x_1559_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v_a_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1583_; 
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1563_ = v___x_1560_;
v_isShared_1564_ = v_isSharedCheck_1583_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_dec(v___x_1560_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1583_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
if (lean_obj_tag(v_a_1561_) == 0)
{
lean_object* v___x_1566_; 
lean_del_object(v___x_1563_);
if (v_isShared_1558_ == 0)
{
lean_ctor_set(v___x_1557_, 1, v___x_1559_);
lean_ctor_set(v___x_1557_, 0, v___x_1551_);
v___x_1566_ = v___x_1557_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v___x_1551_);
lean_ctor_set(v_reuseFailAlloc_1568_, 1, v___x_1559_);
v___x_1566_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
v_a_1544_ = v_it_1553_;
v_b_1545_ = v___x_1566_;
goto _start;
}
}
else
{
lean_object* v___x_1570_; 
lean_dec(v_it_1553_);
lean_dec(v_view_x3f_1543_);
lean_dec_ref(v_filter_1542_);
lean_inc_ref(v_a_1561_);
if (v_isShared_1558_ == 0)
{
lean_ctor_set(v___x_1557_, 1, v___x_1559_);
lean_ctor_set(v___x_1557_, 0, v_a_1561_);
v___x_1570_ = v___x_1557_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_a_1561_);
lean_ctor_set(v_reuseFailAlloc_1582_, 1, v___x_1559_);
v___x_1570_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1580_; 
v_isSharedCheck_1580_ = !lean_is_exclusive(v_a_1561_);
if (v_isSharedCheck_1580_ == 0)
{
lean_object* v_unused_1581_; 
v_unused_1581_ = lean_ctor_get(v_a_1561_, 0);
lean_dec(v_unused_1581_);
v___x_1572_ = v_a_1561_;
v_isShared_1573_ = v_isSharedCheck_1580_;
goto v_resetjp_1571_;
}
else
{
lean_dec(v_a_1561_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1580_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1575_; 
if (v_isShared_1573_ == 0)
{
lean_ctor_set(v___x_1572_, 0, v___x_1570_);
v___x_1575_ = v___x_1572_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1570_);
v___x_1575_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
lean_object* v___x_1577_; 
if (v_isShared_1564_ == 0)
{
lean_ctor_set(v___x_1563_, 0, v___x_1575_);
v___x_1577_ = v___x_1563_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___x_1575_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1591_; 
lean_dec(v___x_1559_);
lean_del_object(v___x_1557_);
lean_dec(v_it_1553_);
lean_dec(v_view_x3f_1543_);
lean_dec_ref(v_filter_1542_);
v_a_1584_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1586_ = v___x_1560_;
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1560_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1589_; 
if (v_isShared_1587_ == 0)
{
v___x_1589_ = v___x_1586_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_a_1584_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24_spec__32___redArg___boxed(lean_object* v_n_u2080_1603_, lean_object* v_filter_1604_, lean_object* v_view_x3f_1605_, lean_object* v_a_1606_, lean_object* v_b_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24_spec__32___redArg(v_n_u2080_1603_, v_filter_1604_, v_view_x3f_1605_, v_a_1606_, v_b_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
lean_dec(v_n_u2080_1603_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24(lean_object* v_n_u2080_1617_, lean_object* v_filter_1618_, lean_object* v_view_x3f_1619_, lean_object* v_n_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
lean_object* v___y_1627_; uint8_t v___x_1672_; 
v___x_1672_ = l_Lean_Name_hasMacroScopes(v_n_1620_);
if (v___x_1672_ == 0)
{
lean_object* v___f_1673_; 
v___f_1673_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27___closed__1));
v___y_1627_ = v___f_1673_;
goto v___jp_1626_;
}
else
{
lean_object* v___f_1674_; 
v___f_1674_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27___closed__0));
v___y_1627_ = v___f_1674_;
goto v___jp_1626_;
}
v___jp_1626_:
{
lean_object* v___x_1628_; 
lean_inc_ref(v___y_1627_);
lean_inc(v___y_1624_);
lean_inc_ref(v___y_1623_);
lean_inc(v___y_1622_);
lean_inc_ref(v___y_1621_);
v___x_1628_ = lean_apply_5(v___y_1627_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, lean_box(0));
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1663_; 
v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1631_ = v___x_1628_;
v_isShared_1632_ = v_isSharedCheck_1663_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1628_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1663_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
if (lean_obj_tag(v_a_1629_) == 0)
{
lean_object* v___x_1633_; lean_object* v___x_1635_; 
lean_dec(v_n_1620_);
lean_dec(v_view_x3f_1619_);
lean_dec_ref(v_filter_1618_);
v___x_1633_ = lean_box(0);
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 0, v___x_1633_);
v___x_1635_ = v___x_1631_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v___x_1633_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
else
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
lean_dec_ref_known(v_a_1629_, 1);
lean_del_object(v___x_1631_);
v___x_1637_ = l_Lean_privateToUserName(v_n_1620_);
v___x_1638_ = l_Lean_Name_revIter(v___x_1637_);
lean_dec(v___x_1637_);
v___x_1639_ = lean_box(0);
v___x_1640_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24___closed__0));
v___x_1641_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24_spec__32___redArg(v_n_u2080_1617_, v_filter_1618_, v_view_x3f_1619_, v___x_1638_, v___x_1640_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1654_; 
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1644_ = v___x_1641_;
v_isShared_1645_ = v_isSharedCheck_1654_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v___x_1641_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1654_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
if (lean_obj_tag(v_a_1642_) == 0)
{
lean_object* v___x_1647_; 
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 0, v___x_1639_);
v___x_1647_ = v___x_1644_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v___x_1639_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
else
{
lean_object* v_val_1649_; lean_object* v_fst_1650_; lean_object* v___x_1652_; 
v_val_1649_ = lean_ctor_get(v_a_1642_, 0);
lean_inc(v_val_1649_);
lean_dec_ref_known(v_a_1642_, 1);
v_fst_1650_ = lean_ctor_get(v_val_1649_, 0);
lean_inc(v_fst_1650_);
lean_dec(v_val_1649_);
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 0, v_fst_1650_);
v___x_1652_ = v___x_1644_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v_fst_1650_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
}
else
{
lean_object* v_a_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1662_; 
v_a_1655_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1657_ = v___x_1641_;
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_a_1655_);
lean_dec(v___x_1641_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1660_; 
if (v_isShared_1658_ == 0)
{
v___x_1660_ = v___x_1657_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_a_1655_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
}
}
}
}
else
{
lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1671_; 
lean_dec(v_n_1620_);
lean_dec(v_view_x3f_1619_);
lean_dec_ref(v_filter_1618_);
v_a_1664_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1666_ = v___x_1628_;
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_dec(v___x_1628_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1669_; 
if (v_isShared_1667_ == 0)
{
v___x_1669_ = v___x_1666_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_a_1664_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24___boxed(lean_object* v_n_u2080_1675_, lean_object* v_filter_1676_, lean_object* v_view_x3f_1677_, lean_object* v_n_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24(v_n_u2080_1675_, v_filter_1676_, v_view_x3f_1677_, v_n_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v_n_u2080_1675_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__25(lean_object* v_n_u2080_1685_, lean_object* v_filter_1686_, lean_object* v_as_1687_, lean_object* v_i_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
lean_object* v___x_1694_; uint8_t v___x_1695_; 
v___x_1694_ = lean_array_get_size(v_as_1687_);
v___x_1695_ = lean_nat_dec_lt(v_i_1688_, v___x_1694_);
if (v___x_1695_ == 0)
{
lean_object* v___x_1696_; lean_object* v___x_1697_; 
lean_dec(v_i_1688_);
lean_dec_ref(v_filter_1686_);
v___x_1696_ = lean_box(0);
v___x_1697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1696_);
return v___x_1697_;
}
else
{
lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1698_ = lean_box(0);
v___x_1699_ = lean_array_fget_borrowed(v_as_1687_, v_i_1688_);
lean_inc(v___x_1699_);
lean_inc_ref(v_filter_1686_);
v___x_1700_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24(v_n_u2080_1685_, v_filter_1686_, v___x_1698_, v___x_1699_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
if (lean_obj_tag(v___x_1700_) == 0)
{
lean_object* v_a_1701_; 
v_a_1701_ = lean_ctor_get(v___x_1700_, 0);
if (lean_obj_tag(v_a_1701_) == 0)
{
lean_object* v___x_1702_; lean_object* v___x_1703_; 
lean_dec_ref_known(v___x_1700_, 1);
v___x_1702_ = lean_unsigned_to_nat(1u);
v___x_1703_ = lean_nat_add(v_i_1688_, v___x_1702_);
lean_dec(v_i_1688_);
v_i_1688_ = v___x_1703_;
goto _start;
}
else
{
lean_dec(v_i_1688_);
lean_dec_ref(v_filter_1686_);
return v___x_1700_;
}
}
else
{
lean_dec(v_i_1688_);
lean_dec_ref(v_filter_1686_);
return v___x_1700_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__25___boxed(lean_object* v_n_u2080_1705_, lean_object* v_filter_1706_, lean_object* v_as_1707_, lean_object* v_i_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__25(v_n_u2080_1705_, v_filter_1706_, v_as_1707_, v_i_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
lean_dec_ref(v_as_1707_);
lean_dec(v_n_u2080_1705_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__26(lean_object* v_n_u2081_1715_, lean_object* v_as_1716_, size_t v_i_1717_, size_t v_stop_1718_, lean_object* v_b_1719_){
_start:
{
lean_object* v___y_1721_; uint8_t v___x_1725_; 
v___x_1725_ = lean_usize_dec_eq(v_i_1717_, v_stop_1718_);
if (v___x_1725_ == 0)
{
lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; uint8_t v___x_1729_; 
v___x_1726_ = lean_array_uget_borrowed(v_as_1716_, v_i_1717_);
v___x_1727_ = l_Lean_Name_getPrefix(v___x_1726_);
v___x_1728_ = l_Lean_Name_getPrefix(v_n_u2081_1715_);
v___x_1729_ = l_Lean_Name_isPrefixOf(v___x_1727_, v___x_1728_);
lean_dec(v___x_1728_);
lean_dec(v___x_1727_);
if (v___x_1729_ == 0)
{
v___y_1721_ = v_b_1719_;
goto v___jp_1720_;
}
else
{
lean_object* v___x_1730_; 
lean_inc(v___x_1726_);
v___x_1730_ = lean_array_push(v_b_1719_, v___x_1726_);
v___y_1721_ = v___x_1730_;
goto v___jp_1720_;
}
}
else
{
return v_b_1719_;
}
v___jp_1720_:
{
size_t v___x_1722_; size_t v___x_1723_; 
v___x_1722_ = ((size_t)1ULL);
v___x_1723_ = lean_usize_add(v_i_1717_, v___x_1722_);
v_i_1717_ = v___x_1723_;
v_b_1719_ = v___y_1721_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__26___boxed(lean_object* v_n_u2081_1731_, lean_object* v_as_1732_, lean_object* v_i_1733_, lean_object* v_stop_1734_, lean_object* v_b_1735_){
_start:
{
size_t v_i_boxed_1736_; size_t v_stop_boxed_1737_; lean_object* v_res_1738_; 
v_i_boxed_1736_ = lean_unbox_usize(v_i_1733_);
lean_dec(v_i_1733_);
v_stop_boxed_1737_ = lean_unbox_usize(v_stop_1734_);
lean_dec(v_stop_1734_);
v_res_1738_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__26(v_n_u2081_1731_, v_as_1732_, v_i_boxed_1736_, v_stop_boxed_1737_, v_b_1735_);
lean_dec_ref(v_as_1732_);
lean_dec(v_n_u2081_1731_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14(lean_object* v_n_u2080_1741_, uint8_t v_fullNames_1742_, uint8_t v_allowHorizAliases_1743_, lean_object* v_filter_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v_view_1750_; lean_object* v_name_1751_; lean_object* v_n_u2081_1752_; 
lean_inc(v_n_u2080_1741_);
v_view_1750_ = l_Lean_extractMacroScopes(v_n_u2080_1741_);
v_name_1751_ = lean_ctor_get(v_view_1750_, 0);
lean_inc(v_name_1751_);
v_n_u2081_1752_ = l_Lean_privateToUserName(v_name_1751_);
if (v_fullNames_1742_ == 0)
{
lean_object* v___x_1753_; lean_object* v_aliases_1755_; lean_object* v_env_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1753_ = lean_st_ref_get(v___y_1748_);
v_env_1770_ = lean_ctor_get(v___x_1753_, 0);
lean_inc_ref(v_env_1770_);
lean_dec(v___x_1753_);
lean_inc(v_n_u2080_1741_);
v___x_1771_ = l_Lean_getRevAliases(v_env_1770_, v_n_u2080_1741_);
v___x_1772_ = lean_array_mk(v___x_1771_);
if (v_allowHorizAliases_1743_ == 0)
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; uint8_t v___x_1776_; 
v___x_1773_ = lean_unsigned_to_nat(0u);
v___x_1774_ = lean_array_get_size(v___x_1772_);
v___x_1775_ = ((lean_object*)(l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14___closed__0));
v___x_1776_ = lean_nat_dec_lt(v___x_1773_, v___x_1774_);
if (v___x_1776_ == 0)
{
lean_dec_ref(v___x_1772_);
v_aliases_1755_ = v___x_1775_;
goto v___jp_1754_;
}
else
{
size_t v___x_1777_; size_t v___x_1778_; lean_object* v___x_1779_; 
v___x_1777_ = ((size_t)0ULL);
v___x_1778_ = lean_usize_of_nat(v___x_1774_);
v___x_1779_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__26(v_n_u2081_1752_, v___x_1772_, v___x_1777_, v___x_1778_, v___x_1775_);
lean_dec_ref(v___x_1772_);
v_aliases_1755_ = v___x_1779_;
goto v___jp_1754_;
}
}
else
{
v_aliases_1755_ = v___x_1772_;
goto v___jp_1754_;
}
v___jp_1754_:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1756_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_filter_1744_);
v___x_1757_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__25(v_n_u2080_1741_, v_filter_1744_, v_aliases_1755_, v___x_1756_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
lean_dec_ref(v_aliases_1755_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
if (lean_obj_tag(v_a_1758_) == 0)
{
lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1768_; 
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1768_ == 0)
{
lean_object* v_unused_1769_; 
v_unused_1769_ = lean_ctor_get(v___x_1757_, 0);
lean_dec(v_unused_1769_);
v___x_1760_ = v___x_1757_;
v_isShared_1761_ = v_isSharedCheck_1768_;
goto v_resetjp_1759_;
}
else
{
lean_dec(v___x_1757_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1768_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1763_; 
if (v_isShared_1761_ == 0)
{
lean_ctor_set_tag(v___x_1760_, 1);
lean_ctor_set(v___x_1760_, 0, v_view_1750_);
v___x_1763_ = v___x_1760_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_view_1750_);
v___x_1763_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1764_ = l_Lean_rootNamespace;
v___x_1765_ = l_Lean_Name_append(v___x_1764_, v_n_u2081_1752_);
v___x_1766_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24(v_n_u2080_1741_, v_filter_1744_, v___x_1763_, v___x_1765_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
lean_dec(v_n_u2080_1741_);
return v___x_1766_;
}
}
}
else
{
lean_dec(v_n_u2081_1752_);
lean_dec_ref(v_view_1750_);
lean_dec_ref(v_filter_1744_);
lean_dec(v_n_u2080_1741_);
return v___x_1757_;
}
}
else
{
lean_dec(v_n_u2081_1752_);
lean_dec_ref(v_view_1750_);
lean_dec_ref(v_filter_1744_);
lean_dec(v_n_u2080_1741_);
return v___x_1757_;
}
}
}
else
{
lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1780_, 0, v_view_1750_);
lean_inc(v_n_u2081_1752_);
lean_inc_ref(v___x_1780_);
lean_inc_ref(v_filter_1744_);
v___x_1781_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27(v_n_u2080_1741_, v_filter_1744_, v___x_1780_, v_n_u2081_1752_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_object* v_a_1782_; 
v_a_1782_ = lean_ctor_get(v___x_1781_, 0);
if (lean_obj_tag(v_a_1782_) == 0)
{
lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
lean_dec_ref_known(v___x_1781_, 1);
v___x_1783_ = l_Lean_rootNamespace;
v___x_1784_ = l_Lean_Name_append(v___x_1783_, v_n_u2081_1752_);
v___x_1785_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27(v_n_u2080_1741_, v_filter_1744_, v___x_1780_, v___x_1784_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
lean_dec(v_n_u2080_1741_);
return v___x_1785_;
}
else
{
lean_dec_ref_known(v___x_1780_, 1);
lean_dec(v_n_u2081_1752_);
lean_dec_ref(v_filter_1744_);
lean_dec(v_n_u2080_1741_);
return v___x_1781_;
}
}
else
{
lean_dec_ref_known(v___x_1780_, 1);
lean_dec(v_n_u2081_1752_);
lean_dec_ref(v_filter_1744_);
lean_dec(v_n_u2080_1741_);
return v___x_1781_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14___boxed(lean_object* v_n_u2080_1786_, lean_object* v_fullNames_1787_, lean_object* v_allowHorizAliases_1788_, lean_object* v_filter_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
uint8_t v_fullNames_boxed_1795_; uint8_t v_allowHorizAliases_boxed_1796_; lean_object* v_res_1797_; 
v_fullNames_boxed_1795_ = lean_unbox(v_fullNames_1787_);
v_allowHorizAliases_boxed_1796_ = lean_unbox(v_allowHorizAliases_1788_);
v_res_1797_ = l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14(v_n_u2080_1786_, v_fullNames_boxed_1795_, v_allowHorizAliases_boxed_1796_, v_filter_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
return v_res_1797_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__29(lean_object* v_snd_1798_, lean_object* v_x_1799_){
_start:
{
if (lean_obj_tag(v_x_1799_) == 0)
{
uint8_t v___x_1800_; 
v___x_1800_ = 0;
return v___x_1800_;
}
else
{
lean_object* v_head_1801_; lean_object* v_tail_1802_; lean_object* v_snd_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; uint8_t v___x_1806_; 
v_head_1801_ = lean_ctor_get(v_x_1799_, 0);
v_tail_1802_ = lean_ctor_get(v_x_1799_, 1);
v_snd_1803_ = lean_ctor_get(v_head_1801_, 1);
v___x_1804_ = l_List_lengthTR___redArg(v_snd_1803_);
v___x_1805_ = l_List_lengthTR___redArg(v_snd_1798_);
v___x_1806_ = lean_nat_dec_lt(v___x_1804_, v___x_1805_);
lean_dec(v___x_1805_);
lean_dec(v___x_1804_);
if (v___x_1806_ == 0)
{
v_x_1799_ = v_tail_1802_;
goto _start;
}
else
{
return v___x_1806_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__29___boxed(lean_object* v_snd_1808_, lean_object* v_x_1809_){
_start:
{
uint8_t v_res_1810_; lean_object* v_r_1811_; 
v_res_1810_ = l_List_any___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__29(v_snd_1808_, v_x_1809_);
lean_dec(v_x_1809_);
lean_dec(v_snd_1808_);
v_r_1811_ = lean_box(v_res_1810_);
return v_r_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__39___redArg(lean_object* v_opt_1812_, lean_object* v___y_1813_){
_start:
{
lean_object* v___x_1815_; uint8_t v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1815_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1813_);
v___x_1816_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__5(v___x_1815_, v_opt_1812_);
lean_dec_ref(v___x_1815_);
v___x_1817_ = lean_box(v___x_1816_);
v___x_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1817_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__39___redArg___boxed(lean_object* v_opt_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__39___redArg(v_opt_1819_, v___y_1820_);
lean_dec_ref(v___y_1820_);
lean_dec_ref(v_opt_1819_);
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44_spec__46(lean_object* v_ref_1823_, lean_object* v_msgData_1824_, uint8_t v_severity_1825_, uint8_t v_isSilent_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_){
_start:
{
lean_object* v___y_1833_; uint8_t v___y_1834_; lean_object* v___y_1835_; lean_object* v___y_1836_; uint8_t v___y_1837_; lean_object* v___y_1838_; lean_object* v___y_1839_; lean_object* v_toCold_1840_; lean_object* v___y_1841_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1872_; uint8_t v___y_1873_; uint8_t v___y_1874_; uint8_t v___y_1875_; lean_object* v___y_1876_; lean_object* v___y_1877_; uint8_t v___y_1897_; lean_object* v___y_1898_; lean_object* v___y_1899_; uint8_t v___y_1900_; lean_object* v___y_1901_; uint8_t v___y_1902_; lean_object* v___y_1903_; uint8_t v___y_1907_; uint8_t v___y_1908_; uint8_t v___x_1918_; uint8_t v___y_1920_; uint8_t v___x_1926_; 
v___x_1918_ = 2;
v___x_1926_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1825_, v___x_1918_);
if (v___x_1926_ == 0)
{
v___y_1920_ = v___x_1926_;
goto v___jp_1919_;
}
else
{
uint8_t v___x_1927_; 
lean_inc_ref(v_msgData_1824_);
v___x_1927_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1824_);
if (v___x_1927_ == 0)
{
v___y_1920_ = v___x_1927_;
goto v___jp_1919_;
}
else
{
lean_object* v___x_1928_; lean_object* v___x_1929_; 
lean_dec_ref(v_msgData_1824_);
v___x_1928_ = lean_box(0);
v___x_1929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1928_);
return v___x_1929_;
}
}
v___jp_1832_:
{
lean_object* v_currNamespace_1842_; lean_object* v_openDecls_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v_env_1848_; lean_object* v_nextMacroScope_1849_; lean_object* v_ngen_1850_; lean_object* v_auxDeclNGen_1851_; lean_object* v_traceState_1852_; lean_object* v_cache_1853_; lean_object* v_recordedDeps_1854_; lean_object* v_messages_1855_; lean_object* v_infoState_1856_; lean_object* v_snapshotTasks_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1868_; 
v_currNamespace_1842_ = lean_ctor_get(v_toCold_1840_, 4);
v_openDecls_1843_ = lean_ctor_get(v_toCold_1840_, 5);
lean_inc(v_openDecls_1843_);
lean_inc(v_currNamespace_1842_);
v___x_1844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1844_, 0, v_currNamespace_1842_);
lean_ctor_set(v___x_1844_, 1, v_openDecls_1843_);
v___x_1845_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1844_);
lean_ctor_set(v___x_1845_, 1, v___y_1836_);
lean_inc_ref(v___y_1833_);
lean_inc_ref(v___y_1838_);
v___x_1846_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1846_, 0, v___y_1838_);
lean_ctor_set(v___x_1846_, 1, v___y_1835_);
lean_ctor_set(v___x_1846_, 2, v___y_1839_);
lean_ctor_set(v___x_1846_, 3, v___y_1833_);
lean_ctor_set(v___x_1846_, 4, v___x_1845_);
lean_ctor_set_uint8(v___x_1846_, sizeof(void*)*5, v___y_1837_);
lean_ctor_set_uint8(v___x_1846_, sizeof(void*)*5 + 1, v___y_1834_);
lean_ctor_set_uint8(v___x_1846_, sizeof(void*)*5 + 2, v_isSilent_1826_);
v___x_1847_ = lean_st_ref_take(v___y_1841_);
v_env_1848_ = lean_ctor_get(v___x_1847_, 0);
v_nextMacroScope_1849_ = lean_ctor_get(v___x_1847_, 1);
v_ngen_1850_ = lean_ctor_get(v___x_1847_, 2);
v_auxDeclNGen_1851_ = lean_ctor_get(v___x_1847_, 3);
v_traceState_1852_ = lean_ctor_get(v___x_1847_, 4);
v_cache_1853_ = lean_ctor_get(v___x_1847_, 5);
v_recordedDeps_1854_ = lean_ctor_get(v___x_1847_, 6);
v_messages_1855_ = lean_ctor_get(v___x_1847_, 7);
v_infoState_1856_ = lean_ctor_get(v___x_1847_, 8);
v_snapshotTasks_1857_ = lean_ctor_get(v___x_1847_, 9);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1859_ = v___x_1847_;
v_isShared_1860_ = v_isSharedCheck_1868_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_snapshotTasks_1857_);
lean_inc(v_infoState_1856_);
lean_inc(v_messages_1855_);
lean_inc(v_recordedDeps_1854_);
lean_inc(v_cache_1853_);
lean_inc(v_traceState_1852_);
lean_inc(v_auxDeclNGen_1851_);
lean_inc(v_ngen_1850_);
lean_inc(v_nextMacroScope_1849_);
lean_inc(v_env_1848_);
lean_dec(v___x_1847_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1868_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1864_; 
v___x_1861_ = lean_box(0);
v___x_1862_ = l_Lean_MessageLog_add(v___x_1846_, v_messages_1855_);
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 7, v___x_1862_);
v___x_1864_ = v___x_1859_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_env_1848_);
lean_ctor_set(v_reuseFailAlloc_1867_, 1, v_nextMacroScope_1849_);
lean_ctor_set(v_reuseFailAlloc_1867_, 2, v_ngen_1850_);
lean_ctor_set(v_reuseFailAlloc_1867_, 3, v_auxDeclNGen_1851_);
lean_ctor_set(v_reuseFailAlloc_1867_, 4, v_traceState_1852_);
lean_ctor_set(v_reuseFailAlloc_1867_, 5, v_cache_1853_);
lean_ctor_set(v_reuseFailAlloc_1867_, 6, v_recordedDeps_1854_);
lean_ctor_set(v_reuseFailAlloc_1867_, 7, v___x_1862_);
lean_ctor_set(v_reuseFailAlloc_1867_, 8, v_infoState_1856_);
lean_ctor_set(v_reuseFailAlloc_1867_, 9, v_snapshotTasks_1857_);
v___x_1864_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1865_ = lean_st_ref_put(v___y_1841_, v___x_1864_);
v___x_1866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1861_);
return v___x_1866_;
}
}
}
v___jp_1869_:
{
lean_object* v_fileName_1878_; lean_object* v_fileMap_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1895_; 
v_fileName_1878_ = lean_ctor_get(v___y_1876_, 0);
v_fileMap_1879_ = lean_ctor_get(v___y_1876_, 1);
v___x_1880_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1824_);
v___x_1881_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44_spec__46_spec__49(v___x_1880_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
v_a_1882_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1884_ = v___x_1881_;
v_isShared_1885_ = v_isSharedCheck_1895_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1881_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1895_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
lean_inc_ref_n(v_fileMap_1879_, 2);
v___x_1886_ = l_Lean_FileMap_toPosition(v_fileMap_1879_, v___y_1872_);
lean_dec(v___y_1872_);
v___x_1887_ = l_Lean_FileMap_toPosition(v_fileMap_1879_, v___y_1877_);
lean_dec(v___y_1877_);
v___x_1888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1887_);
v___x_1889_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__1));
if (v___y_1873_ == 0)
{
lean_del_object(v___x_1884_);
lean_dec_ref(v___y_1870_);
v___y_1833_ = v___x_1889_;
v___y_1834_ = v___y_1874_;
v___y_1835_ = v___x_1886_;
v___y_1836_ = v_a_1882_;
v___y_1837_ = v___y_1875_;
v___y_1838_ = v_fileName_1878_;
v___y_1839_ = v___x_1888_;
v_toCold_1840_ = v___y_1871_;
v___y_1841_ = v___y_1830_;
goto v___jp_1832_;
}
else
{
uint8_t v___x_1890_; 
lean_inc(v_a_1882_);
v___x_1890_ = l_Lean_MessageData_hasTag(v___y_1870_, v_a_1882_);
if (v___x_1890_ == 0)
{
lean_object* v___x_1891_; lean_object* v___x_1893_; 
lean_dec_ref_known(v___x_1888_, 1);
lean_dec_ref(v___x_1886_);
lean_dec(v_a_1882_);
v___x_1891_ = lean_box(0);
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 0, v___x_1891_);
v___x_1893_ = v___x_1884_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1891_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
else
{
lean_del_object(v___x_1884_);
v___y_1833_ = v___x_1889_;
v___y_1834_ = v___y_1874_;
v___y_1835_ = v___x_1886_;
v___y_1836_ = v_a_1882_;
v___y_1837_ = v___y_1875_;
v___y_1838_ = v_fileName_1878_;
v___y_1839_ = v___x_1888_;
v_toCold_1840_ = v___y_1871_;
v___y_1841_ = v___y_1830_;
goto v___jp_1832_;
}
}
}
}
v___jp_1896_:
{
lean_object* v___x_1904_; 
v___x_1904_ = l_Lean_Syntax_getTailPos_x3f(v___y_1901_, v___y_1902_);
lean_dec(v___y_1901_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_inc(v___y_1903_);
v___y_1870_ = v___y_1898_;
v___y_1871_ = v___y_1899_;
v___y_1872_ = v___y_1903_;
v___y_1873_ = v___y_1897_;
v___y_1874_ = v___y_1900_;
v___y_1875_ = v___y_1902_;
v___y_1876_ = v___y_1899_;
v___y_1877_ = v___y_1903_;
goto v___jp_1869_;
}
else
{
lean_object* v_val_1905_; 
v_val_1905_ = lean_ctor_get(v___x_1904_, 0);
lean_inc(v_val_1905_);
lean_dec_ref_known(v___x_1904_, 1);
v___y_1870_ = v___y_1898_;
v___y_1871_ = v___y_1899_;
v___y_1872_ = v___y_1903_;
v___y_1873_ = v___y_1897_;
v___y_1874_ = v___y_1900_;
v___y_1875_ = v___y_1902_;
v___y_1876_ = v___y_1899_;
v___y_1877_ = v_val_1905_;
goto v___jp_1869_;
}
}
v___jp_1906_:
{
lean_object* v_toCold_1909_; lean_object* v_ref_1910_; uint8_t v_suppressElabErrors_1911_; lean_object* v___x_1912_; lean_object* v___f_1913_; lean_object* v_ref_1914_; lean_object* v___x_1915_; 
v_toCold_1909_ = lean_ctor_get(v___y_1829_, 0);
v_ref_1910_ = lean_ctor_get(v___y_1829_, 2);
v_suppressElabErrors_1911_ = lean_ctor_get_uint8(v___y_1829_, sizeof(void*)*3 + 2);
v___x_1912_ = lean_box(v_suppressElabErrors_1911_);
v___f_1913_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1913_, 0, v___x_1912_);
v_ref_1914_ = l_Lean_replaceRef(v_ref_1823_, v_ref_1910_);
v___x_1915_ = l_Lean_Syntax_getPos_x3f(v_ref_1914_, v___y_1907_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v___x_1916_; 
v___x_1916_ = lean_unsigned_to_nat(0u);
v___y_1897_ = v_suppressElabErrors_1911_;
v___y_1898_ = v___f_1913_;
v___y_1899_ = v_toCold_1909_;
v___y_1900_ = v___y_1908_;
v___y_1901_ = v_ref_1914_;
v___y_1902_ = v___y_1907_;
v___y_1903_ = v___x_1916_;
goto v___jp_1896_;
}
else
{
lean_object* v_val_1917_; 
v_val_1917_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_val_1917_);
lean_dec_ref_known(v___x_1915_, 1);
v___y_1897_ = v_suppressElabErrors_1911_;
v___y_1898_ = v___f_1913_;
v___y_1899_ = v_toCold_1909_;
v___y_1900_ = v___y_1908_;
v___y_1901_ = v_ref_1914_;
v___y_1902_ = v___y_1907_;
v___y_1903_ = v_val_1917_;
goto v___jp_1896_;
}
}
v___jp_1919_:
{
uint8_t v___x_1921_; uint8_t v___x_1922_; 
v___x_1921_ = 1;
v___x_1922_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1825_, v___x_1921_);
if (v___x_1922_ == 0)
{
v___y_1907_ = v___y_1920_;
v___y_1908_ = v_severity_1825_;
goto v___jp_1906_;
}
else
{
lean_object* v___x_1923_; lean_object* v___x_1924_; uint8_t v___x_1925_; 
v___x_1923_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1829_);
v___x_1924_ = l_Lean_warningAsError;
v___x_1925_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__5(v___x_1923_, v___x_1924_);
lean_dec_ref(v___x_1923_);
if (v___x_1925_ == 0)
{
v___y_1907_ = v___y_1920_;
v___y_1908_ = v_severity_1825_;
goto v___jp_1906_;
}
else
{
v___y_1907_ = v___y_1920_;
v___y_1908_ = v___x_1918_;
goto v___jp_1906_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44_spec__46___boxed(lean_object* v_ref_1930_, lean_object* v_msgData_1931_, lean_object* v_severity_1932_, lean_object* v_isSilent_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
uint8_t v_severity_boxed_1939_; uint8_t v_isSilent_boxed_1940_; lean_object* v_res_1941_; 
v_severity_boxed_1939_ = lean_unbox(v_severity_1932_);
v_isSilent_boxed_1940_ = lean_unbox(v_isSilent_1933_);
v_res_1941_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44_spec__46(v_ref_1930_, v_msgData_1931_, v_severity_boxed_1939_, v_isSilent_boxed_1940_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
lean_dec(v_ref_1930_);
return v_res_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44(lean_object* v_msgData_1942_, uint8_t v_severity_1943_, uint8_t v_isSilent_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
lean_object* v_ref_1950_; lean_object* v___x_1951_; 
v_ref_1950_ = lean_ctor_get(v___y_1947_, 2);
v___x_1951_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44_spec__46(v_ref_1950_, v_msgData_1942_, v_severity_1943_, v_isSilent_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44___boxed(lean_object* v_msgData_1952_, lean_object* v_severity_1953_, lean_object* v_isSilent_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_){
_start:
{
uint8_t v_severity_boxed_1960_; uint8_t v_isSilent_boxed_1961_; lean_object* v_res_1962_; 
v_severity_boxed_1960_ = lean_unbox(v_severity_1953_);
v_isSilent_boxed_1961_ = lean_unbox(v_isSilent_1954_);
v_res_1962_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44(v_msgData_1952_, v_severity_boxed_1960_, v_isSilent_boxed_1961_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
return v_res_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40(lean_object* v_msgData_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
uint8_t v___x_1969_; uint8_t v___x_1970_; lean_object* v___x_1971_; 
v___x_1969_ = 1;
v___x_1970_ = 0;
v___x_1971_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44(v_msgData_1963_, v___x_1969_, v___x_1970_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_);
return v___x_1971_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40___boxed(lean_object* v_msgData_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40(v_msgData_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34(lean_object* v_id_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_){
_start:
{
lean_object* v___x_1985_; lean_object* v_env_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v_a_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_2008_; 
v___x_1985_ = lean_st_ref_get(v___y_1983_);
v_env_1986_ = lean_ctor_get(v___x_1985_, 0);
lean_inc_ref(v_env_1986_);
lean_dec(v___x_1985_);
v___x_1987_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1988_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__39___redArg(v___x_1987_, v___y_1982_);
v_a_1989_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_1991_ = v___x_1988_;
v_isShared_1992_ = v_isSharedCheck_2008_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_a_1989_);
lean_dec(v___x_1988_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_2008_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
uint8_t v_isExporting_1998_; 
v_isExporting_1998_ = lean_ctor_get_uint8(v_env_1986_, sizeof(void*)*13);
lean_dec_ref(v_env_1986_);
if (v_isExporting_1998_ == 0)
{
lean_dec(v_a_1989_);
lean_dec(v_id_1979_);
goto v___jp_1993_;
}
else
{
uint8_t v___x_1999_; 
v___x_1999_ = l_Lean_isPrivateName(v_id_1979_);
if (v___x_1999_ == 0)
{
lean_dec(v_a_1989_);
lean_dec(v_id_1979_);
goto v___jp_1993_;
}
else
{
uint8_t v___x_2000_; 
v___x_2000_ = lean_unbox(v_a_1989_);
lean_dec(v_a_1989_);
if (v___x_2000_ == 0)
{
lean_dec(v_id_1979_);
goto v___jp_1993_;
}
else
{
lean_object* v___x_2001_; uint8_t v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; 
lean_del_object(v___x_1991_);
v___x_2001_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___closed__1);
v___x_2002_ = 0;
v___x_2003_ = l_Lean_MessageData_ofConstName(v_id_1979_, v___x_2002_);
v___x_2004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2004_, 0, v___x_2001_);
lean_ctor_set(v___x_2004_, 1, v___x_2003_);
v___x_2005_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___closed__3);
v___x_2006_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2006_, 0, v___x_2004_);
lean_ctor_set(v___x_2006_, 1, v___x_2005_);
v___x_2007_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40(v___x_2006_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_);
return v___x_2007_;
}
}
}
v___jp_1993_:
{
lean_object* v___x_1994_; lean_object* v___x_1996_; 
v___x_1994_ = lean_box(0);
if (v_isShared_1992_ == 0)
{
lean_ctor_set(v___x_1991_, 0, v___x_1994_);
v___x_1996_ = v___x_1991_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v___x_1994_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34___boxed(lean_object* v_id_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_){
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34(v_id_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28(lean_object* v_id_2016_, uint8_t v_enableLog_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_){
_start:
{
lean_object* v___x_2023_; lean_object* v_toCold_2024_; lean_object* v_env_2025_; lean_object* v_currNamespace_2026_; lean_object* v_openDecls_2027_; lean_object* v___x_2028_; lean_object* v_res_2029_; lean_object* v___x_2030_; 
v___x_2023_ = lean_st_ref_get(v___y_2021_);
v_toCold_2024_ = lean_ctor_get(v___y_2020_, 0);
v_env_2025_ = lean_ctor_get(v___x_2023_, 0);
lean_inc_ref(v_env_2025_);
lean_dec(v___x_2023_);
v_currNamespace_2026_ = lean_ctor_get(v_toCold_2024_, 4);
v_openDecls_2027_ = lean_ctor_get(v_toCold_2024_, 5);
v___x_2028_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2020_);
lean_inc(v_openDecls_2027_);
lean_inc(v_currNamespace_2026_);
v_res_2029_ = l_Lean_ResolveName_resolveGlobalName(v_env_2025_, v___x_2028_, v_currNamespace_2026_, v_openDecls_2027_, v_id_2016_);
lean_dec_ref(v___x_2028_);
v___x_2030_ = lean_st_ref_get(v___y_2021_);
if (v_enableLog_2017_ == 0)
{
lean_object* v___x_2031_; 
lean_dec(v___x_2030_);
v___x_2031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2031_, 0, v_res_2029_);
return v___x_2031_;
}
else
{
lean_object* v_env_2032_; uint8_t v_isExporting_2033_; 
v_env_2032_ = lean_ctor_get(v___x_2030_, 0);
lean_inc_ref(v_env_2032_);
lean_dec(v___x_2030_);
v_isExporting_2033_ = lean_ctor_get_uint8(v_env_2032_, sizeof(void*)*13);
lean_dec_ref(v_env_2032_);
if (v_isExporting_2033_ == 0)
{
lean_object* v___x_2034_; 
v___x_2034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2034_, 0, v_res_2029_);
return v___x_2034_;
}
else
{
lean_object* v___x_2035_; 
v___x_2035_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__33(v_res_2029_);
if (lean_obj_tag(v___x_2035_) == 1)
{
lean_object* v_val_2036_; lean_object* v_fst_2037_; lean_object* v___x_2038_; 
v_val_2036_ = lean_ctor_get(v___x_2035_, 0);
lean_inc(v_val_2036_);
lean_dec_ref_known(v___x_2035_, 1);
v_fst_2037_ = lean_ctor_get(v_val_2036_, 0);
lean_inc(v_fst_2037_);
lean_dec(v_val_2036_);
v___x_2038_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34(v_fst_2037_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_);
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2045_ == 0)
{
lean_object* v_unused_2046_; 
v_unused_2046_ = lean_ctor_get(v___x_2038_, 0);
lean_dec(v_unused_2046_);
v___x_2040_ = v___x_2038_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_dec(v___x_2038_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
lean_ctor_set(v___x_2040_, 0, v_res_2029_);
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_res_2029_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
else
{
lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2054_; 
lean_dec(v_res_2029_);
v_a_2047_ = lean_ctor_get(v___x_2038_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2049_ = v___x_2038_;
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_dec(v___x_2038_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2052_; 
if (v_isShared_2050_ == 0)
{
v___x_2052_ = v___x_2049_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_a_2047_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
}
else
{
lean_object* v___x_2055_; 
lean_dec(v___x_2035_);
v___x_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2055_, 0, v_res_2029_);
return v___x_2055_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28___boxed(lean_object* v_id_2056_, lean_object* v_enableLog_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_){
_start:
{
uint8_t v_enableLog_boxed_2063_; lean_object* v_res_2064_; 
v_enableLog_boxed_2063_ = lean_unbox(v_enableLog_2057_);
v_res_2064_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28(v_id_2056_, v_enableLog_boxed_2063_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22(lean_object* v_view_2065_, lean_object* v_findLocalDecl_x3f_2066_, lean_object* v_n_2067_, lean_object* v_projs_2068_, lean_object* v_auxDecl_x3f_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_){
_start:
{
lean_object* v___y_2076_; lean_object* v___y_2077_; lean_object* v_auxDecl_x3f_2083_; lean_object* v_imported_2114_; lean_object* v_ctx_2115_; lean_object* v_scopes_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v_imported_2114_ = lean_ctor_get(v_view_2065_, 1);
v_ctx_2115_ = lean_ctor_get(v_view_2065_, 2);
v_scopes_2116_ = lean_ctor_get(v_view_2065_, 3);
lean_inc(v_scopes_2116_);
lean_inc(v_ctx_2115_);
lean_inc(v_imported_2114_);
lean_inc(v_n_2067_);
v___x_2117_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2117_, 0, v_n_2067_);
lean_ctor_set(v___x_2117_, 1, v_imported_2114_);
lean_ctor_set(v___x_2117_, 2, v_ctx_2115_);
lean_ctor_set(v___x_2117_, 3, v_scopes_2116_);
lean_inc_ref(v_findLocalDecl_x3f_2066_);
v___x_2118_ = lean_apply_1(v_findLocalDecl_x3f_2066_, v___x_2117_);
if (lean_obj_tag(v___x_2118_) == 1)
{
lean_object* v_val_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2134_; 
v_val_2119_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2121_ = v___x_2118_;
v_isShared_2122_ = v_isSharedCheck_2134_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_val_2119_);
lean_dec(v___x_2118_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2134_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
uint8_t v___x_2123_; 
v___x_2123_ = l_Lean_LocalDecl_isAuxDecl(v_val_2119_);
if (v___x_2123_ == 0)
{
lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2127_; 
lean_dec(v_auxDecl_x3f_2069_);
lean_dec(v_n_2067_);
lean_dec_ref(v_findLocalDecl_x3f_2066_);
lean_dec_ref(v_view_2065_);
v___x_2124_ = l_Lean_LocalDecl_toExpr(v_val_2119_);
v___x_2125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2124_);
lean_ctor_set(v___x_2125_, 1, v_projs_2068_);
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 0, v___x_2125_);
v___x_2127_ = v___x_2121_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v___x_2125_);
v___x_2127_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
lean_object* v___x_2128_; 
v___x_2128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2127_);
return v___x_2128_;
}
}
else
{
if (lean_obj_tag(v_auxDecl_x3f_2069_) == 0)
{
lean_object* v___x_2130_; lean_object* v___x_2132_; 
lean_inc(v_projs_2068_);
v___x_2130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2130_, 0, v_val_2119_);
lean_ctor_set(v___x_2130_, 1, v_projs_2068_);
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 0, v___x_2130_);
v___x_2132_ = v___x_2121_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v___x_2130_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
v_auxDecl_x3f_2083_ = v___x_2132_;
goto v___jp_2082_;
}
}
else
{
lean_del_object(v___x_2121_);
lean_dec(v_val_2119_);
v_auxDecl_x3f_2083_ = v_auxDecl_x3f_2069_;
goto v___jp_2082_;
}
}
}
}
else
{
lean_dec(v___x_2118_);
v_auxDecl_x3f_2083_ = v_auxDecl_x3f_2069_;
goto v___jp_2082_;
}
v___jp_2075_:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2078_ = l_Lean_LocalDecl_toExpr(v___y_2076_);
v___x_2079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2078_);
lean_ctor_set(v___x_2079_, 1, v___y_2077_);
v___x_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2079_);
v___x_2081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2080_);
return v___x_2081_;
}
v___jp_2082_:
{
if (lean_obj_tag(v_n_2067_) == 1)
{
lean_object* v_pre_2084_; lean_object* v_str_2085_; lean_object* v___x_2086_; 
v_pre_2084_ = lean_ctor_get(v_n_2067_, 0);
lean_inc(v_pre_2084_);
v_str_2085_ = lean_ctor_get(v_n_2067_, 1);
lean_inc_ref(v_str_2085_);
lean_dec_ref_known(v_n_2067_, 2);
v___x_2086_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2086_, 0, v_str_2085_);
lean_ctor_set(v___x_2086_, 1, v_projs_2068_);
v_n_2067_ = v_pre_2084_;
v_projs_2068_ = v___x_2086_;
v_auxDecl_x3f_2069_ = v_auxDecl_x3f_2083_;
goto _start;
}
else
{
lean_dec(v_projs_2068_);
lean_dec(v_n_2067_);
lean_dec_ref(v_findLocalDecl_x3f_2066_);
if (lean_obj_tag(v_auxDecl_x3f_2083_) == 1)
{
lean_object* v_val_2088_; lean_object* v_fst_2089_; lean_object* v_snd_2090_; uint8_t v___x_2091_; 
v_val_2088_ = lean_ctor_get(v_auxDecl_x3f_2083_, 0);
lean_inc(v_val_2088_);
lean_dec_ref_known(v_auxDecl_x3f_2083_, 1);
v_fst_2089_ = lean_ctor_get(v_val_2088_, 0);
lean_inc(v_fst_2089_);
v_snd_2090_ = lean_ctor_get(v_val_2088_, 1);
lean_inc(v_snd_2090_);
lean_dec(v_val_2088_);
v___x_2091_ = l_List_isEmpty___redArg(v_snd_2090_);
if (v___x_2091_ == 0)
{
lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2092_ = l_Lean_MacroScopesView_review(v_view_2065_);
v___x_2093_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28(v___x_2092_, v___x_2091_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v_a_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2103_; 
v_a_2094_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2096_ = v___x_2093_;
v_isShared_2097_ = v_isSharedCheck_2103_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_a_2094_);
lean_dec(v___x_2093_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2103_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
uint8_t v___x_2098_; 
v___x_2098_ = l_List_any___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__29(v_snd_2090_, v_a_2094_);
lean_dec(v_a_2094_);
if (v___x_2098_ == 0)
{
lean_del_object(v___x_2096_);
v___y_2076_ = v_fst_2089_;
v___y_2077_ = v_snd_2090_;
goto v___jp_2075_;
}
else
{
lean_object* v___x_2099_; lean_object* v___x_2101_; 
lean_dec(v_snd_2090_);
lean_dec(v_fst_2089_);
v___x_2099_ = lean_box(0);
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 0, v___x_2099_);
v___x_2101_ = v___x_2096_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v___x_2099_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
else
{
lean_object* v_a_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2111_; 
lean_dec(v_snd_2090_);
lean_dec(v_fst_2089_);
v_a_2104_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2106_ = v___x_2093_;
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_a_2104_);
lean_dec(v___x_2093_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2109_; 
if (v_isShared_2107_ == 0)
{
v___x_2109_ = v___x_2106_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_a_2104_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
}
else
{
lean_dec_ref(v_view_2065_);
v___y_2076_ = v_fst_2089_;
v___y_2077_ = v_snd_2090_;
goto v___jp_2075_;
}
}
else
{
lean_object* v___x_2112_; lean_object* v___x_2113_; 
lean_dec(v_auxDecl_x3f_2083_);
lean_dec_ref(v_view_2065_);
v___x_2112_ = lean_box(0);
v___x_2113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2112_);
return v___x_2113_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22___boxed(lean_object* v_view_2135_, lean_object* v_findLocalDecl_x3f_2136_, lean_object* v_n_2137_, lean_object* v_projs_2138_, lean_object* v_auxDecl_x3f_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_){
_start:
{
lean_object* v_res_2145_; 
v_res_2145_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22(v_view_2135_, v_findLocalDecl_x3f_2136_, v_n_2137_, v_projs_2138_, v_auxDecl_x3f_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_);
lean_dec(v___y_2143_);
lean_dec_ref(v___y_2142_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
return v_res_2145_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__25___redArg(lean_object* v_localDecl_x3f_2146_, lean_object* v_givenName_2147_, lean_object* v_as_2148_, lean_object* v_i_2149_){
_start:
{
lean_object* v_zero_2150_; uint8_t v_isZero_2151_; 
v_zero_2150_ = lean_unsigned_to_nat(0u);
v_isZero_2151_ = lean_nat_dec_eq(v_i_2149_, v_zero_2150_);
if (v_isZero_2151_ == 1)
{
lean_object* v___x_2152_; 
lean_dec(v_i_2149_);
v___x_2152_ = lean_box(0);
return v___x_2152_;
}
else
{
lean_object* v_one_2153_; lean_object* v_n_2154_; lean_object* v___x_2155_; 
v_one_2153_ = lean_unsigned_to_nat(1u);
v_n_2154_ = lean_nat_sub(v_i_2149_, v_one_2153_);
lean_dec(v_i_2149_);
v___x_2155_ = lean_array_fget_borrowed(v_as_2148_, v_n_2154_);
if (lean_obj_tag(v___x_2155_) == 0)
{
v_i_2149_ = v_n_2154_;
goto _start;
}
else
{
lean_object* v_val_2157_; uint8_t v___x_2158_; 
v_val_2157_ = lean_ctor_get(v___x_2155_, 0);
v___x_2158_ = l_Lean_LocalDecl_isAuxDecl(v_val_2157_);
if (v___x_2158_ == 0)
{
if (lean_obj_tag(v_localDecl_x3f_2146_) == 0)
{
v_i_2149_ = v_n_2154_;
goto _start;
}
else
{
lean_dec(v_n_2154_);
lean_inc_ref(v_localDecl_x3f_2146_);
return v_localDecl_x3f_2146_;
}
}
else
{
lean_object* v___x_2160_; uint8_t v___x_2161_; 
v___x_2160_ = l_Lean_LocalDecl_userName(v_val_2157_);
v___x_2161_ = lean_name_eq(v___x_2160_, v_givenName_2147_);
lean_dec(v___x_2160_);
if (v___x_2161_ == 0)
{
v_i_2149_ = v_n_2154_;
goto _start;
}
else
{
lean_dec(v_n_2154_);
lean_inc_ref(v___x_2155_);
return v___x_2155_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__25___redArg___boxed(lean_object* v_localDecl_x3f_2163_, lean_object* v_givenName_2164_, lean_object* v_as_2165_, lean_object* v_i_2166_){
_start:
{
lean_object* v_res_2167_; 
v_res_2167_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__25___redArg(v_localDecl_x3f_2163_, v_givenName_2164_, v_as_2165_, v_i_2166_);
lean_dec_ref(v_as_2165_);
lean_dec(v_givenName_2164_);
lean_dec(v_localDecl_x3f_2163_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26_spec__30___redArg(lean_object* v_localDecl_x3f_2168_, lean_object* v_givenName_2169_, lean_object* v_as_2170_, lean_object* v_i_2171_){
_start:
{
lean_object* v_zero_2172_; uint8_t v_isZero_2173_; 
v_zero_2172_ = lean_unsigned_to_nat(0u);
v_isZero_2173_ = lean_nat_dec_eq(v_i_2171_, v_zero_2172_);
if (v_isZero_2173_ == 1)
{
lean_object* v___x_2174_; 
lean_dec(v_i_2171_);
v___x_2174_ = lean_box(0);
return v___x_2174_;
}
else
{
lean_object* v_one_2175_; lean_object* v_n_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v_one_2175_ = lean_unsigned_to_nat(1u);
v_n_2176_ = lean_nat_sub(v_i_2171_, v_one_2175_);
lean_dec(v_i_2171_);
v___x_2177_ = lean_array_fget_borrowed(v_as_2170_, v_n_2176_);
v___x_2178_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26(v_localDecl_x3f_2168_, v_givenName_2169_, v___x_2177_);
if (lean_obj_tag(v___x_2178_) == 0)
{
v_i_2171_ = v_n_2176_;
goto _start;
}
else
{
lean_dec(v_n_2176_);
return v___x_2178_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26(lean_object* v_localDecl_x3f_2180_, lean_object* v_givenName_2181_, lean_object* v_x_2182_){
_start:
{
if (lean_obj_tag(v_x_2182_) == 0)
{
lean_object* v_cs_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
v_cs_2183_ = lean_ctor_get(v_x_2182_, 0);
v___x_2184_ = lean_array_get_size(v_cs_2183_);
v___x_2185_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26_spec__30___redArg(v_localDecl_x3f_2180_, v_givenName_2181_, v_cs_2183_, v___x_2184_);
return v___x_2185_;
}
else
{
lean_object* v_vs_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; 
v_vs_2186_ = lean_ctor_get(v_x_2182_, 0);
v___x_2187_ = lean_array_get_size(v_vs_2186_);
v___x_2188_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__25___redArg(v_localDecl_x3f_2180_, v_givenName_2181_, v_vs_2186_, v___x_2187_);
return v___x_2188_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26___boxed(lean_object* v_localDecl_x3f_2189_, lean_object* v_givenName_2190_, lean_object* v_x_2191_){
_start:
{
lean_object* v_res_2192_; 
v_res_2192_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26(v_localDecl_x3f_2189_, v_givenName_2190_, v_x_2191_);
lean_dec_ref(v_x_2191_);
lean_dec(v_givenName_2190_);
lean_dec(v_localDecl_x3f_2189_);
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26_spec__30___redArg___boxed(lean_object* v_localDecl_x3f_2193_, lean_object* v_givenName_2194_, lean_object* v_as_2195_, lean_object* v_i_2196_){
_start:
{
lean_object* v_res_2197_; 
v_res_2197_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26_spec__30___redArg(v_localDecl_x3f_2193_, v_givenName_2194_, v_as_2195_, v_i_2196_);
lean_dec_ref(v_as_2195_);
lean_dec(v_givenName_2194_);
lean_dec(v_localDecl_x3f_2193_);
return v_res_2197_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21(lean_object* v_localDecl_x3f_2198_, lean_object* v_givenName_2199_, lean_object* v_t_2200_){
_start:
{
lean_object* v_root_2201_; lean_object* v_tail_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v_root_2201_ = lean_ctor_get(v_t_2200_, 0);
v_tail_2202_ = lean_ctor_get(v_t_2200_, 1);
v___x_2203_ = lean_array_get_size(v_tail_2202_);
v___x_2204_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__25___redArg(v_localDecl_x3f_2198_, v_givenName_2199_, v_tail_2202_, v___x_2203_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v___x_2205_; 
v___x_2205_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26(v_localDecl_x3f_2198_, v_givenName_2199_, v_root_2201_);
return v___x_2205_;
}
else
{
return v___x_2204_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21___boxed(lean_object* v_localDecl_x3f_2206_, lean_object* v_givenName_2207_, lean_object* v_t_2208_){
_start:
{
lean_object* v_res_2209_; 
v_res_2209_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21(v_localDecl_x3f_2206_, v_givenName_2207_, v_t_2208_);
lean_dec_ref(v_t_2208_);
lean_dec(v_givenName_2207_);
lean_dec(v_localDecl_x3f_2206_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__19___redArg(lean_object* v_t_2210_, lean_object* v_k_2211_){
_start:
{
if (lean_obj_tag(v_t_2210_) == 0)
{
lean_object* v_k_2212_; lean_object* v_v_2213_; lean_object* v_l_2214_; lean_object* v_r_2215_; uint8_t v___x_2216_; 
v_k_2212_ = lean_ctor_get(v_t_2210_, 1);
v_v_2213_ = lean_ctor_get(v_t_2210_, 2);
v_l_2214_ = lean_ctor_get(v_t_2210_, 3);
v_r_2215_ = lean_ctor_get(v_t_2210_, 4);
v___x_2216_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2211_, v_k_2212_);
switch(v___x_2216_)
{
case 0:
{
v_t_2210_ = v_l_2214_;
goto _start;
}
case 1:
{
lean_object* v___x_2218_; 
lean_inc(v_v_2213_);
v___x_2218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2218_, 0, v_v_2213_);
return v___x_2218_;
}
default: 
{
v_t_2210_ = v_r_2215_;
goto _start;
}
}
}
else
{
lean_object* v___x_2220_; 
v___x_2220_ = lean_box(0);
return v___x_2220_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__19___redArg___boxed(lean_object* v_t_2221_, lean_object* v_k_2222_){
_start:
{
lean_object* v_res_2223_; 
v_res_2223_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__19___redArg(v_t_2221_, v_k_2222_);
lean_dec(v_k_2222_);
lean_dec(v_t_2221_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22___redArg___lam__0(lean_object* v_localDecl_2224_, lean_object* v_givenName_2225_){
_start:
{
lean_object* v___x_2226_; uint8_t v___x_2227_; 
v___x_2226_ = l_Lean_LocalDecl_userName(v_localDecl_2224_);
v___x_2227_ = lean_name_eq(v___x_2226_, v_givenName_2225_);
lean_dec(v___x_2226_);
if (v___x_2227_ == 0)
{
lean_object* v___x_2228_; 
lean_dec_ref(v_localDecl_2224_);
v___x_2228_ = lean_box(0);
return v___x_2228_;
}
else
{
lean_object* v___x_2229_; 
v___x_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2229_, 0, v_localDecl_2224_);
return v___x_2229_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22___redArg___lam__0___boxed(lean_object* v_localDecl_2230_, lean_object* v_givenName_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22___redArg___lam__0(v_localDecl_2230_, v_givenName_2231_);
lean_dec(v_givenName_2231_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22___redArg(lean_object* v_givenName_2233_, lean_object* v_auxDeclToFullName_2234_, lean_object* v___x_2235_, lean_object* v_givenNameView_2236_, lean_object* v_as_2237_, lean_object* v_i_2238_){
_start:
{
lean_object* v_zero_2239_; uint8_t v_isZero_2240_; 
v_zero_2239_ = lean_unsigned_to_nat(0u);
v_isZero_2240_ = lean_nat_dec_eq(v_i_2238_, v_zero_2239_);
if (v_isZero_2240_ == 1)
{
lean_object* v___x_2241_; 
lean_dec(v_i_2238_);
lean_dec_ref(v_givenNameView_2236_);
lean_dec(v___x_2235_);
v___x_2241_ = lean_box(0);
return v___x_2241_;
}
else
{
lean_object* v_one_2242_; lean_object* v_n_2243_; lean_object* v___y_2245_; lean_object* v___x_2247_; 
v_one_2242_ = lean_unsigned_to_nat(1u);
v_n_2243_ = lean_nat_sub(v_i_2238_, v_one_2242_);
lean_dec(v_i_2238_);
v___x_2247_ = lean_array_fget_borrowed(v_as_2237_, v_n_2243_);
if (lean_obj_tag(v___x_2247_) == 0)
{
v_i_2238_ = v_n_2243_;
goto _start;
}
else
{
lean_object* v_val_2249_; uint8_t v___x_2250_; 
v_val_2249_ = lean_ctor_get(v___x_2247_, 0);
v___x_2250_ = l_Lean_LocalDecl_isAuxDecl(v_val_2249_);
if (v___x_2250_ == 0)
{
lean_object* v___x_2251_; 
lean_inc(v_val_2249_);
v___x_2251_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22___redArg___lam__0(v_val_2249_, v_givenName_2233_);
v___y_2245_ = v___x_2251_;
goto v___jp_2244_;
}
else
{
lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2252_ = l_Lean_LocalDecl_fvarId(v_val_2249_);
v___x_2253_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__19___redArg(v_auxDeclToFullName_2234_, v___x_2252_);
lean_dec(v___x_2252_);
if (lean_obj_tag(v___x_2253_) == 1)
{
lean_object* v_val_2254_; lean_object* v_fullDeclView_2255_; lean_object* v_name_2256_; lean_object* v_imported_2257_; lean_object* v_ctx_2258_; lean_object* v_scopes_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2279_; 
v_val_2254_ = lean_ctor_get(v___x_2253_, 0);
lean_inc(v_val_2254_);
lean_dec_ref_known(v___x_2253_, 1);
v_fullDeclView_2255_ = l_Lean_extractMacroScopes(v_val_2254_);
v_name_2256_ = lean_ctor_get(v_fullDeclView_2255_, 0);
v_imported_2257_ = lean_ctor_get(v_fullDeclView_2255_, 1);
v_ctx_2258_ = lean_ctor_get(v_fullDeclView_2255_, 2);
v_scopes_2259_ = lean_ctor_get(v_fullDeclView_2255_, 3);
v_isSharedCheck_2279_ = !lean_is_exclusive(v_fullDeclView_2255_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2261_ = v_fullDeclView_2255_;
v_isShared_2262_ = v_isSharedCheck_2279_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_scopes_2259_);
lean_inc(v_ctx_2258_);
lean_inc(v_imported_2257_);
lean_inc(v_name_2256_);
lean_dec(v_fullDeclView_2255_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2279_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___y_2264_; lean_object* v___x_2277_; 
lean_inc(v_name_2256_);
v___x_2277_ = l_Lean_privateToUserName_x3f(v_name_2256_);
if (lean_obj_tag(v___x_2277_) == 0)
{
v___y_2264_ = v_name_2256_;
goto v___jp_2263_;
}
else
{
lean_object* v_val_2278_; 
lean_dec(v_name_2256_);
v_val_2278_ = lean_ctor_get(v___x_2277_, 0);
lean_inc(v_val_2278_);
lean_dec_ref_known(v___x_2277_, 1);
v___y_2264_ = v_val_2278_;
goto v___jp_2263_;
}
v___jp_2263_:
{
lean_object* v_fullDeclView_2266_; 
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 0, v___y_2264_);
v_fullDeclView_2266_ = v___x_2261_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v___y_2264_);
lean_ctor_set(v_reuseFailAlloc_2276_, 1, v_imported_2257_);
lean_ctor_set(v_reuseFailAlloc_2276_, 2, v_ctx_2258_);
lean_ctor_set(v_reuseFailAlloc_2276_, 3, v_scopes_2259_);
v_fullDeclView_2266_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
lean_object* v_fullDeclName_2267_; uint8_t v___x_2268_; 
lean_inc_ref(v_fullDeclView_2266_);
v_fullDeclName_2267_ = l_Lean_MacroScopesView_review(v_fullDeclView_2266_);
v___x_2268_ = l_Lean_Name_isPrefixOf(v___x_2235_, v_fullDeclName_2267_);
if (v___x_2268_ == 0)
{
lean_object* v___x_2269_; 
lean_dec_ref(v_fullDeclView_2266_);
lean_inc(v___x_2235_);
lean_inc_ref(v_givenNameView_2236_);
lean_inc(v_val_2249_);
v___x_2269_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_val_2249_, v_givenNameView_2236_, v_fullDeclName_2267_, v___x_2235_);
lean_dec(v_fullDeclName_2267_);
v___y_2245_ = v___x_2269_;
goto v___jp_2244_;
}
else
{
lean_object* v___x_2270_; lean_object* v_localDeclNameView_2271_; uint8_t v___x_2272_; 
lean_dec(v_fullDeclName_2267_);
v___x_2270_ = l_Lean_LocalDecl_userName(v_val_2249_);
v_localDeclNameView_2271_ = l_Lean_extractMacroScopes(v___x_2270_);
v___x_2272_ = l_Lean_MacroScopesView_isSuffixOf(v_localDeclNameView_2271_, v_givenNameView_2236_);
lean_dec_ref(v_localDeclNameView_2271_);
if (v___x_2272_ == 0)
{
lean_dec_ref(v_fullDeclView_2266_);
v_i_2238_ = v_n_2243_;
goto _start;
}
else
{
uint8_t v___x_2274_; 
v___x_2274_ = l_Lean_MacroScopesView_isSuffixOf(v_givenNameView_2236_, v_fullDeclView_2266_);
lean_dec_ref(v_fullDeclView_2266_);
if (v___x_2274_ == 0)
{
v_i_2238_ = v_n_2243_;
goto _start;
}
else
{
lean_dec(v_n_2243_);
lean_dec_ref(v_givenNameView_2236_);
lean_dec(v___x_2235_);
lean_inc_ref(v___x_2247_);
return v___x_2247_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2280_; 
lean_dec(v___x_2253_);
lean_inc(v_val_2249_);
v___x_2280_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22___redArg___lam__0(v_val_2249_, v_givenName_2233_);
v___y_2245_ = v___x_2280_;
goto v___jp_2244_;
}
}
}
v___jp_2244_:
{
if (lean_obj_tag(v___y_2245_) == 0)
{
v_i_2238_ = v_n_2243_;
goto _start;
}
else
{
lean_dec(v_n_2243_);
lean_dec_ref(v_givenNameView_2236_);
lean_dec(v___x_2235_);
return v___y_2245_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22___redArg___boxed(lean_object* v_givenName_2281_, lean_object* v_auxDeclToFullName_2282_, lean_object* v___x_2283_, lean_object* v_givenNameView_2284_, lean_object* v_as_2285_, lean_object* v_i_2286_){
_start:
{
lean_object* v_res_2287_; 
v_res_2287_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22___redArg(v_givenName_2281_, v_auxDeclToFullName_2282_, v___x_2283_, v_givenNameView_2284_, v_as_2285_, v_i_2286_);
lean_dec_ref(v_as_2285_);
lean_dec(v_auxDeclToFullName_2282_);
lean_dec(v_givenName_2281_);
return v_res_2287_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23_spec__26___redArg(lean_object* v_givenName_2288_, lean_object* v_auxDeclToFullName_2289_, lean_object* v___x_2290_, lean_object* v_givenNameView_2291_, lean_object* v_as_2292_, lean_object* v_i_2293_){
_start:
{
lean_object* v_zero_2294_; uint8_t v_isZero_2295_; 
v_zero_2294_ = lean_unsigned_to_nat(0u);
v_isZero_2295_ = lean_nat_dec_eq(v_i_2293_, v_zero_2294_);
if (v_isZero_2295_ == 1)
{
lean_object* v___x_2296_; 
lean_dec(v_i_2293_);
lean_dec_ref(v_givenNameView_2291_);
lean_dec(v___x_2290_);
v___x_2296_ = lean_box(0);
return v___x_2296_;
}
else
{
lean_object* v_one_2297_; lean_object* v_n_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; 
v_one_2297_ = lean_unsigned_to_nat(1u);
v_n_2298_ = lean_nat_sub(v_i_2293_, v_one_2297_);
lean_dec(v_i_2293_);
v___x_2299_ = lean_array_fget_borrowed(v_as_2292_, v_n_2298_);
lean_inc_ref(v_givenNameView_2291_);
lean_inc(v___x_2290_);
v___x_2300_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23(v_givenName_2288_, v_auxDeclToFullName_2289_, v___x_2290_, v_givenNameView_2291_, v___x_2299_);
if (lean_obj_tag(v___x_2300_) == 0)
{
v_i_2293_ = v_n_2298_;
goto _start;
}
else
{
lean_dec(v_n_2298_);
lean_dec_ref(v_givenNameView_2291_);
lean_dec(v___x_2290_);
return v___x_2300_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23(lean_object* v_givenName_2302_, lean_object* v_auxDeclToFullName_2303_, lean_object* v___x_2304_, lean_object* v_givenNameView_2305_, lean_object* v_x_2306_){
_start:
{
if (lean_obj_tag(v_x_2306_) == 0)
{
lean_object* v_cs_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; 
v_cs_2307_ = lean_ctor_get(v_x_2306_, 0);
v___x_2308_ = lean_array_get_size(v_cs_2307_);
v___x_2309_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23_spec__26___redArg(v_givenName_2302_, v_auxDeclToFullName_2303_, v___x_2304_, v_givenNameView_2305_, v_cs_2307_, v___x_2308_);
return v___x_2309_;
}
else
{
lean_object* v_vs_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
v_vs_2310_ = lean_ctor_get(v_x_2306_, 0);
v___x_2311_ = lean_array_get_size(v_vs_2310_);
v___x_2312_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22___redArg(v_givenName_2302_, v_auxDeclToFullName_2303_, v___x_2304_, v_givenNameView_2305_, v_vs_2310_, v___x_2311_);
return v___x_2312_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23___boxed(lean_object* v_givenName_2313_, lean_object* v_auxDeclToFullName_2314_, lean_object* v___x_2315_, lean_object* v_givenNameView_2316_, lean_object* v_x_2317_){
_start:
{
lean_object* v_res_2318_; 
v_res_2318_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23(v_givenName_2313_, v_auxDeclToFullName_2314_, v___x_2315_, v_givenNameView_2316_, v_x_2317_);
lean_dec_ref(v_x_2317_);
lean_dec(v_auxDeclToFullName_2314_);
lean_dec(v_givenName_2313_);
return v_res_2318_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23_spec__26___redArg___boxed(lean_object* v_givenName_2319_, lean_object* v_auxDeclToFullName_2320_, lean_object* v___x_2321_, lean_object* v_givenNameView_2322_, lean_object* v_as_2323_, lean_object* v_i_2324_){
_start:
{
lean_object* v_res_2325_; 
v_res_2325_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23_spec__26___redArg(v_givenName_2319_, v_auxDeclToFullName_2320_, v___x_2321_, v_givenNameView_2322_, v_as_2323_, v_i_2324_);
lean_dec_ref(v_as_2323_);
lean_dec(v_auxDeclToFullName_2320_);
lean_dec(v_givenName_2319_);
return v_res_2325_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20(lean_object* v_givenName_2326_, lean_object* v_auxDeclToFullName_2327_, lean_object* v___x_2328_, lean_object* v_givenNameView_2329_, lean_object* v_t_2330_){
_start:
{
lean_object* v_root_2331_; lean_object* v_tail_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; 
v_root_2331_ = lean_ctor_get(v_t_2330_, 0);
v_tail_2332_ = lean_ctor_get(v_t_2330_, 1);
v___x_2333_ = lean_array_get_size(v_tail_2332_);
lean_inc_ref(v_givenNameView_2329_);
lean_inc(v___x_2328_);
v___x_2334_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22___redArg(v_givenName_2326_, v_auxDeclToFullName_2327_, v___x_2328_, v_givenNameView_2329_, v_tail_2332_, v___x_2333_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v___x_2335_; 
v___x_2335_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23(v_givenName_2326_, v_auxDeclToFullName_2327_, v___x_2328_, v_givenNameView_2329_, v_root_2331_);
return v___x_2335_;
}
else
{
lean_dec_ref(v_givenNameView_2329_);
lean_dec(v___x_2328_);
return v___x_2334_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20___boxed(lean_object* v_givenName_2336_, lean_object* v_auxDeclToFullName_2337_, lean_object* v___x_2338_, lean_object* v_givenNameView_2339_, lean_object* v_t_2340_){
_start:
{
lean_object* v_res_2341_; 
v_res_2341_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20(v_givenName_2336_, v_auxDeclToFullName_2337_, v___x_2338_, v_givenNameView_2339_, v_t_2340_);
lean_dec_ref(v_t_2340_);
lean_dec(v_auxDeclToFullName_2337_);
lean_dec(v_givenName_2336_);
return v_res_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13___lam__0(lean_object* v_auxDeclToFullName_2342_, lean_object* v_currNamespace_2343_, lean_object* v_decls_2344_, lean_object* v_givenNameView_2345_){
_start:
{
lean_object* v_givenName_2346_; lean_object* v_localDecl_x3f_2347_; 
lean_inc_ref(v_givenNameView_2345_);
v_givenName_2346_ = l_Lean_MacroScopesView_review(v_givenNameView_2345_);
v_localDecl_x3f_2347_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20(v_givenName_2346_, v_auxDeclToFullName_2342_, v_currNamespace_2343_, v_givenNameView_2345_, v_decls_2344_);
if (lean_obj_tag(v_localDecl_x3f_2347_) == 0)
{
lean_object* v___x_2348_; 
v___x_2348_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21(v_localDecl_x3f_2347_, v_givenName_2346_, v_decls_2344_);
lean_dec(v_givenName_2346_);
return v___x_2348_;
}
else
{
lean_dec(v_givenName_2346_);
return v_localDecl_x3f_2347_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13___lam__0___boxed(lean_object* v_auxDeclToFullName_2349_, lean_object* v_currNamespace_2350_, lean_object* v_decls_2351_, lean_object* v_givenNameView_2352_){
_start:
{
lean_object* v_res_2353_; 
v_res_2353_ = l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13___lam__0(v_auxDeclToFullName_2349_, v_currNamespace_2350_, v_decls_2351_, v_givenNameView_2352_);
lean_dec_ref(v_decls_2351_);
lean_dec(v_auxDeclToFullName_2349_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13(lean_object* v_n_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_){
_start:
{
lean_object* v_lctx_2360_; lean_object* v_toCold_2361_; lean_object* v_decls_2362_; lean_object* v_auxDeclToFullName_2363_; lean_object* v_currNamespace_2364_; lean_object* v_view_2365_; lean_object* v_name_2366_; lean_object* v_findLocalDecl_x3f_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
v_lctx_2360_ = lean_ctor_get(v___y_2355_, 2);
v_toCold_2361_ = lean_ctor_get(v___y_2357_, 0);
v_decls_2362_ = lean_ctor_get(v_lctx_2360_, 1);
v_auxDeclToFullName_2363_ = lean_ctor_get(v_lctx_2360_, 2);
v_currNamespace_2364_ = lean_ctor_get(v_toCold_2361_, 4);
v_view_2365_ = l_Lean_extractMacroScopes(v_n_2354_);
v_name_2366_ = lean_ctor_get(v_view_2365_, 0);
lean_inc(v_name_2366_);
lean_inc_ref(v_decls_2362_);
lean_inc(v_currNamespace_2364_);
lean_inc(v_auxDeclToFullName_2363_);
v_findLocalDecl_x3f_2367_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13___lam__0___boxed), 4, 3);
lean_closure_set(v_findLocalDecl_x3f_2367_, 0, v_auxDeclToFullName_2363_);
lean_closure_set(v_findLocalDecl_x3f_2367_, 1, v_currNamespace_2364_);
lean_closure_set(v_findLocalDecl_x3f_2367_, 2, v_decls_2362_);
v___x_2368_ = lean_box(0);
v___x_2369_ = lean_box(0);
v___x_2370_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22(v_view_2365_, v_findLocalDecl_x3f_2367_, v_name_2366_, v___x_2368_, v___x_2369_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
return v___x_2370_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13___boxed(lean_object* v_n_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_){
_start:
{
lean_object* v_res_2377_; 
v_res_2377_ = l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13(v_n_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
return v_res_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6___lam__0(uint8_t v___x_2378_, lean_object* v_n_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_){
_start:
{
lean_object* v___x_2385_; 
v___x_2385_ = l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13(v_n_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
if (lean_obj_tag(v___x_2385_) == 0)
{
lean_object* v_a_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2399_; 
v_a_2386_ = lean_ctor_get(v___x_2385_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2388_ = v___x_2385_;
v_isShared_2389_ = v_isSharedCheck_2399_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_a_2386_);
lean_dec(v___x_2385_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2399_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
if (lean_obj_tag(v_a_2386_) == 0)
{
uint8_t v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2393_; 
v___x_2390_ = 1;
v___x_2391_ = lean_box(v___x_2390_);
if (v_isShared_2389_ == 0)
{
lean_ctor_set(v___x_2388_, 0, v___x_2391_);
v___x_2393_ = v___x_2388_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v___x_2391_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
else
{
lean_object* v___x_2395_; lean_object* v___x_2397_; 
lean_dec_ref_known(v_a_2386_, 1);
v___x_2395_ = lean_box(v___x_2378_);
if (v_isShared_2389_ == 0)
{
lean_ctor_set(v___x_2388_, 0, v___x_2395_);
v___x_2397_ = v___x_2388_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v___x_2395_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
}
}
else
{
lean_object* v_a_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2407_; 
v_a_2400_ = lean_ctor_get(v___x_2385_, 0);
v_isSharedCheck_2407_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2407_ == 0)
{
v___x_2402_ = v___x_2385_;
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_a_2400_);
lean_dec(v___x_2385_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2405_; 
if (v_isShared_2403_ == 0)
{
v___x_2405_ = v___x_2402_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_a_2400_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
return v___x_2405_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6___lam__0___boxed(lean_object* v___x_2408_, lean_object* v_n_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_){
_start:
{
uint8_t v___x_47642__boxed_2415_; lean_object* v_res_2416_; 
v___x_47642__boxed_2415_ = lean_unbox(v___x_2408_);
v_res_2416_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6___lam__0(v___x_47642__boxed_2415_, v_n_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_);
lean_dec(v___y_2413_);
lean_dec_ref(v___y_2412_);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6(lean_object* v_n_u2080_2420_, uint8_t v_fullNames_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
uint8_t v___x_2427_; lean_object* v___f_2428_; lean_object* v___x_2429_; 
v___x_2427_ = 0;
v___f_2428_ = ((lean_object*)(l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6___closed__0));
v___x_2429_ = l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14(v_n_u2080_2420_, v_fullNames_2421_, v___x_2427_, v___f_2428_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6___boxed(lean_object* v_n_u2080_2430_, lean_object* v_fullNames_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_){
_start:
{
uint8_t v_fullNames_boxed_2437_; lean_object* v_res_2438_; 
v_fullNames_boxed_2437_ = lean_unbox(v_fullNames_2431_);
v_res_2438_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6(v_n_u2080_2430_, v_fullNames_boxed_2437_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_);
lean_dec(v___y_2435_);
lean_dec_ref(v___y_2434_);
lean_dec(v___y_2433_);
lean_dec_ref(v___y_2432_);
return v_res_2438_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__1_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2440_; lean_object* v___x_2441_; 
v___x_2440_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__0_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2441_ = l_Lean_stringToMessageData(v___x_2440_);
return v___x_2441_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__4_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; 
v___x_2445_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__3_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2446_ = l_Lean_MessageData_ofFormat(v___x_2445_);
return v___x_2446_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2448_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__5_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2449_ = l_Lean_stringToMessageData(v___x_2448_);
return v___x_2449_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2451_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2452_ = l_Lean_stringToMessageData(v___x_2451_);
return v___x_2452_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__10_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2454_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2455_ = l_Lean_stringToMessageData(v___x_2454_);
return v___x_2455_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__13_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2459_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__12_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2460_ = l_Lean_MessageData_ofFormat(v___x_2459_);
return v___x_2460_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__14_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2461_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__13_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__13_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__13_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2462_ = l_Lean_MessageData_hint_x27(v___x_2461_);
return v___x_2462_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2464_; lean_object* v___x_2465_; 
v___x_2464_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__15_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2465_ = l_Lean_stringToMessageData(v___x_2464_);
return v___x_2465_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__19_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; 
v___x_2469_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__18_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2470_ = l_Lean_MessageData_ofFormat(v___x_2469_);
return v___x_2470_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__24_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2477_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__23_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2478_ = l_Lean_MessageData_ofFormat(v___x_2477_);
return v___x_2478_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__25_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2479_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__24_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__24_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__24_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2479_);
return v___x_2480_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2481_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_2482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2481_);
return v___x_2482_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__27_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2483_ = lean_box(1);
v___x_2484_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_2485_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2486_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2486_, 0, v___x_2485_);
lean_ctor_set(v___x_2486_, 1, v___x_2484_);
lean_ctor_set(v___x_2486_, 2, v___x_2483_);
return v___x_2486_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
v___x_2489_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2490_ = lean_unsigned_to_nat(0u);
v___x_2491_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2491_, 0, v___x_2490_);
lean_ctor_set(v___x_2491_, 1, v___x_2490_);
lean_ctor_set(v___x_2491_, 2, v___x_2490_);
lean_ctor_set(v___x_2491_, 3, v___x_2490_);
lean_ctor_set(v___x_2491_, 4, v___x_2489_);
lean_ctor_set(v___x_2491_, 5, v___x_2489_);
lean_ctor_set(v___x_2491_, 6, v___x_2489_);
lean_ctor_set(v___x_2491_, 7, v___x_2489_);
lean_ctor_set(v___x_2491_, 8, v___x_2489_);
lean_ctor_set(v___x_2491_, 9, v___x_2489_);
lean_ctor_set(v___x_2491_, 10, v___x_2489_);
return v___x_2491_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2492_; 
v___x_2492_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__4_spec__10___redArg();
return v___x_2492_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2493_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2493_);
lean_ctor_set(v___x_2494_, 1, v___x_2493_);
return v___x_2494_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2495_ = lean_unsigned_to_nat(0u);
v___x_2496_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2497_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2497_, 0, v___x_2496_);
lean_ctor_set(v___x_2497_, 1, v___x_2496_);
lean_ctor_set(v___x_2497_, 2, v___x_2495_);
return v___x_2497_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2498_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2499_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2500_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2501_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2502_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2502_, 0, v___x_2501_);
lean_ctor_set(v___x_2502_, 1, v___x_2500_);
lean_ctor_set(v___x_2502_, 2, v___x_2499_);
lean_ctor_set(v___x_2502_, 3, v___x_2500_);
lean_ctor_set(v___x_2502_, 4, v___x_2500_);
lean_ctor_set(v___x_2502_, 5, v___x_2500_);
lean_ctor_set(v___x_2502_, 6, v___x_2498_);
return v___x_2502_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2503_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2504_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2503_);
lean_ctor_set(v___x_2504_, 1, v___x_2503_);
lean_ctor_set(v___x_2504_, 2, v___x_2503_);
lean_ctor_set(v___x_2504_, 3, v___x_2503_);
lean_ctor_set(v___x_2504_, 4, v___x_2503_);
return v___x_2504_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__37_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2508_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__36_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2509_ = l_Lean_MessageData_ofFormat(v___x_2508_);
return v___x_2509_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__39_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2511_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__38_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2512_ = l_Lean_stringToMessageData(v___x_2511_);
return v___x_2512_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2514_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__40_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2515_ = l_Lean_stringToMessageData(v___x_2514_);
return v___x_2515_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2517_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2518_ = l_Lean_stringToMessageData(v___x_2517_);
return v___x_2518_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2520_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2521_ = l_Lean_stringToMessageData(v___x_2520_);
return v___x_2521_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__47_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2523_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2524_ = l_Lean_stringToMessageData(v___x_2523_);
return v___x_2524_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__49_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2526_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__48_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2527_ = l_Lean_stringToMessageData(v___x_2526_);
return v___x_2527_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__51_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2529_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__50_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2530_ = l_Lean_stringToMessageData(v___x_2529_);
return v___x_2530_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__53_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2532_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__52_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2533_ = l_Lean_stringToMessageData(v___x_2532_);
return v___x_2533_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__55_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2535_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__54_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2536_ = l_Lean_stringToMessageData(v___x_2535_);
return v___x_2536_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__57_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2538_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__56_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2539_ = l_Lean_stringToMessageData(v___x_2538_);
return v___x_2539_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__59_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; 
v___x_2541_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__58_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2542_ = l_Lean_stringToMessageData(v___x_2541_);
return v___x_2542_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__61_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2544_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__60_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2545_ = l_Lean_stringToMessageData(v___x_2544_);
return v___x_2545_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__63_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___x_2547_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__62_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2548_ = l_Lean_stringToMessageData(v___x_2547_);
return v___x_2548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(lean_object* v___x_2549_, lean_object* v___x_2550_, lean_object* v___f_2551_, uint8_t v___x_2552_, lean_object* v___x_2553_, lean_object* v___x_2554_, lean_object* v_a_2555_, lean_object* v_declName_2556_, lean_object* v_stx_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_){
_start:
{
lean_object* v___y_2562_; lean_object* v___y_2563_; lean_object* v___y_2564_; lean_object* v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2595_; lean_object* v___y_2596_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v___y_2612_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2615_; lean_object* v___y_2616_; lean_object* v___y_2617_; lean_object* v___y_2629_; lean_object* v___y_2630_; lean_object* v___y_2631_; lean_object* v___y_2632_; lean_object* v___y_2633_; lean_object* v___y_2634_; lean_object* v___y_2646_; lean_object* v___y_2647_; lean_object* v___y_2648_; lean_object* v___y_2649_; lean_object* v___y_2650_; lean_object* v___y_2651_; lean_object* v_hint_2652_; lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___x_2686_; uint8_t v___x_2687_; 
v___x_2686_ = l_Lean_Name_mkStr2(v___x_2549_, v___x_2550_);
lean_inc(v_stx_2557_);
v___x_2687_ = l_Lean_Syntax_isOfKind(v_stx_2557_, v___x_2686_);
lean_dec(v___x_2686_);
if (v___x_2687_ == 0)
{
lean_object* v___x_2688_; lean_object* v___x_2689_; 
lean_dec(v_stx_2557_);
lean_dec(v_declName_2556_);
lean_dec_ref(v___x_2554_);
lean_dec(v___x_2553_);
lean_dec_ref(v___f_2551_);
v___x_2688_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2689_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0___redArg(v___x_2688_, v___y_2558_, v___y_2559_);
return v___x_2689_;
}
else
{
lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___y_2693_; lean_object* v___y_2694_; lean_object* v___y_2695_; lean_object* v___y_2696_; lean_object* v___y_2697_; lean_object* v___y_2698_; lean_object* v___y_2699_; lean_object* v___y_2700_; lean_object* v_val_2701_; lean_object* v___y_2726_; lean_object* v___y_2727_; lean_object* v___y_2728_; lean_object* v___y_2729_; lean_object* v___y_2730_; lean_object* v___y_2731_; lean_object* v___y_2732_; lean_object* v___y_2733_; lean_object* v___y_2738_; lean_object* v___y_2739_; uint8_t v___y_2740_; lean_object* v___y_2741_; lean_object* v___y_2742_; lean_object* v___y_2743_; lean_object* v___y_2744_; lean_object* v___y_2745_; lean_object* v___y_2746_; lean_object* v___y_2747_; lean_object* v___y_2794_; lean_object* v___y_2795_; lean_object* v___y_2796_; uint8_t v___y_2797_; lean_object* v___y_2798_; lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v_msg_2802_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2815_; lean_object* v___y_2816_; lean_object* v___y_2817_; lean_object* v___y_2818_; lean_object* v___y_2819_; lean_object* v___y_2820_; lean_object* v___y_2821_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v_a_2962_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v___y_2982_; lean_object* v_since_x3f_2983_; lean_object* v___y_2984_; lean_object* v___y_2985_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v_typeChanged_x3f_3004_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3018_; lean_object* v_text_x3f_3019_; lean_object* v___y_3020_; lean_object* v___y_3021_; lean_object* v_id_x3f_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___x_3044_; uint8_t v___x_3045_; 
v___x_2690_ = lean_unsigned_to_nat(0u);
v___x_2691_ = lean_unsigned_to_nat(1u);
v___x_3044_ = l_Lean_Syntax_getArg(v_stx_2557_, v___x_2691_);
v___x_3045_ = l_Lean_Syntax_isNone(v___x_3044_);
if (v___x_3045_ == 0)
{
uint8_t v___x_3046_; 
lean_inc(v___x_3044_);
v___x_3046_ = l_Lean_Syntax_matchesNull(v___x_3044_, v___x_2691_);
if (v___x_3046_ == 0)
{
lean_object* v___x_3047_; lean_object* v___x_3048_; 
lean_dec(v___x_3044_);
lean_dec(v_stx_2557_);
lean_dec(v_declName_2556_);
lean_dec_ref(v___x_2554_);
lean_dec(v___x_2553_);
lean_dec_ref(v___f_2551_);
v___x_3047_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_3048_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0___redArg(v___x_3047_, v___y_2558_, v___y_2559_);
return v___x_3048_;
}
else
{
lean_object* v___x_3049_; lean_object* v___x_3050_; 
v___x_3049_ = l_Lean_Syntax_getArg(v___x_3044_, v___x_2690_);
lean_dec(v___x_3044_);
v___x_3050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3050_, 0, v___x_3049_);
v_id_x3f_3032_ = v___x_3050_;
v___y_3033_ = v___y_2558_;
v___y_3034_ = v___y_2559_;
goto v___jp_3031_;
}
}
else
{
lean_object* v___x_3051_; 
lean_dec(v___x_3044_);
v___x_3051_ = lean_box(0);
v_id_x3f_3032_ = v___x_3051_;
v___y_3033_ = v___y_2558_;
v___y_3034_ = v___y_2559_;
goto v___jp_3031_;
}
v___jp_2692_:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; uint8_t v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2702_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__19_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__19_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__19_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2703_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__21_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2704_ = lean_box(0);
v___x_2705_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__25_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__25_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__25_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2706_, 0, v___f_2551_);
v___x_2707_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2707_, 0, v___x_2703_);
lean_ctor_set(v___x_2707_, 1, v___x_2704_);
lean_ctor_set(v___x_2707_, 2, v___x_2704_);
lean_ctor_set(v___x_2707_, 3, v___x_2704_);
lean_ctor_set(v___x_2707_, 4, v___x_2705_);
lean_ctor_set(v___x_2707_, 5, v___x_2706_);
lean_inc(v_val_2701_);
v___x_2708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2708_, 0, v_val_2701_);
lean_ctor_set(v___x_2708_, 1, v_val_2701_);
v___x_2709_ = l_Lean_Syntax_ofRange(v___x_2708_, v___x_2687_);
v___x_2710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2710_, 0, v___x_2709_);
v___x_2711_ = 4;
v___x_2712_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2712_, 0, v___x_2707_);
lean_ctor_set(v___x_2712_, 1, v___x_2710_);
lean_ctor_set(v___x_2712_, 2, v___x_2704_);
lean_ctor_set_uint8(v___x_2712_, sizeof(void*)*3, v___x_2711_);
v___x_2713_ = lean_mk_empty_array_with_capacity(v___x_2691_);
v___x_2714_ = lean_array_push(v___x_2713_, v___x_2712_);
v___x_2715_ = l_Lean_MessageData_hint(v___x_2702_, v___x_2714_, v___x_2704_, v___x_2704_, v___x_2552_, v___y_2695_, v___y_2694_);
lean_dec_ref(v___x_2714_);
if (lean_obj_tag(v___x_2715_) == 0)
{
lean_object* v_a_2716_; 
v_a_2716_ = lean_ctor_get(v___x_2715_, 0);
lean_inc(v_a_2716_);
lean_dec_ref_known(v___x_2715_, 1);
v___y_2646_ = v___y_2693_;
v___y_2647_ = v___y_2696_;
v___y_2648_ = v___y_2697_;
v___y_2649_ = v___y_2698_;
v___y_2650_ = v___y_2699_;
v___y_2651_ = v___y_2700_;
v_hint_2652_ = v_a_2716_;
v___y_2653_ = v___y_2695_;
v___y_2654_ = v___y_2694_;
goto v___jp_2645_;
}
else
{
lean_object* v_a_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2724_; 
lean_dec(v___y_2700_);
lean_dec(v___y_2699_);
lean_dec_ref(v___y_2698_);
lean_dec(v___y_2697_);
lean_dec(v___y_2696_);
lean_dec_ref(v___y_2693_);
lean_dec(v_stx_2557_);
v_a_2717_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2719_ = v___x_2715_;
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_a_2717_);
lean_dec(v___x_2715_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v___x_2722_; 
if (v_isShared_2720_ == 0)
{
v___x_2722_ = v___x_2719_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_a_2717_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
}
}
v___jp_2725_:
{
if (lean_obj_tag(v___y_2732_) == 0)
{
lean_dec_ref(v___f_2551_);
v___y_2677_ = v___y_2726_;
v___y_2678_ = v___y_2727_;
v___y_2679_ = v___y_2728_;
v___y_2680_ = v___y_2729_;
v___y_2681_ = v___y_2730_;
v___y_2682_ = v___y_2731_;
v___y_2683_ = v___y_2732_;
v___y_2684_ = v___y_2733_;
goto v___jp_2676_;
}
else
{
lean_object* v_val_2734_; lean_object* v___x_2735_; 
v_val_2734_ = lean_ctor_get(v___y_2732_, 0);
v___x_2735_ = l_Lean_Syntax_getTailPos_x3f(v_val_2734_, v___x_2687_);
if (lean_obj_tag(v___x_2735_) == 1)
{
lean_object* v_val_2736_; 
v_val_2736_ = lean_ctor_get(v___x_2735_, 0);
lean_inc(v_val_2736_);
lean_dec_ref_known(v___x_2735_, 1);
v___y_2693_ = v___y_2726_;
v___y_2694_ = v___y_2727_;
v___y_2695_ = v___y_2728_;
v___y_2696_ = v___y_2729_;
v___y_2697_ = v___y_2730_;
v___y_2698_ = v___y_2731_;
v___y_2699_ = v___y_2732_;
v___y_2700_ = v___y_2733_;
v_val_2701_ = v_val_2736_;
goto v___jp_2692_;
}
else
{
lean_dec(v___x_2735_);
lean_dec_ref(v___f_2551_);
v___y_2677_ = v___y_2726_;
v___y_2678_ = v___y_2727_;
v___y_2679_ = v___y_2728_;
v___y_2680_ = v___y_2729_;
v___y_2681_ = v___y_2730_;
v___y_2682_ = v___y_2731_;
v___y_2683_ = v___y_2732_;
v___y_2684_ = v___y_2733_;
goto v___jp_2676_;
}
}
}
v___jp_2737_:
{
lean_object* v___x_2748_; 
lean_inc_ref(v___y_2738_);
v___x_2748_ = l_Lean_Environment_findConstVal_x3f(v___y_2738_, v_declName_2556_, v___x_2552_);
if (lean_obj_tag(v___x_2748_) == 1)
{
lean_object* v_val_2749_; lean_object* v___x_2750_; 
v_val_2749_ = lean_ctor_get(v___x_2748_, 0);
lean_inc(v_val_2749_);
lean_dec_ref_known(v___x_2748_, 1);
v___x_2750_ = l_Lean_Environment_findConstVal_x3f(v___y_2738_, v___y_2745_, v___x_2552_);
if (lean_obj_tag(v___x_2750_) == 1)
{
lean_object* v_val_2751_; uint8_t v___x_2752_; uint8_t v___x_2753_; uint8_t v___x_2754_; lean_object* v___x_2755_; uint64_t v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; 
v_val_2751_ = lean_ctor_get(v___x_2750_, 0);
lean_inc(v_val_2751_);
lean_dec_ref_known(v___x_2750_, 1);
v___x_2752_ = 1;
v___x_2753_ = 0;
v___x_2754_ = 2;
v___x_2755_ = lean_alloc_ctor(0, 0, 21);
lean_ctor_set_uint8(v___x_2755_, 0, v___x_2552_);
lean_ctor_set_uint8(v___x_2755_, 1, v___x_2552_);
lean_ctor_set_uint8(v___x_2755_, 2, v___x_2552_);
lean_ctor_set_uint8(v___x_2755_, 3, v___x_2552_);
lean_ctor_set_uint8(v___x_2755_, 4, v___x_2552_);
lean_ctor_set_uint8(v___x_2755_, 5, v___y_2740_);
lean_ctor_set_uint8(v___x_2755_, 6, v___y_2740_);
lean_ctor_set_uint8(v___x_2755_, 7, v___x_2552_);
lean_ctor_set_uint8(v___x_2755_, 8, v___y_2740_);
lean_ctor_set_uint8(v___x_2755_, 9, v___x_2752_);
lean_ctor_set_uint8(v___x_2755_, 10, v___x_2753_);
lean_ctor_set_uint8(v___x_2755_, 11, v___y_2740_);
lean_ctor_set_uint8(v___x_2755_, 12, v___y_2740_);
lean_ctor_set_uint8(v___x_2755_, 13, v___y_2740_);
lean_ctor_set_uint8(v___x_2755_, 14, v___x_2754_);
lean_ctor_set_uint8(v___x_2755_, 15, v___y_2740_);
lean_ctor_set_uint8(v___x_2755_, 16, v___y_2740_);
lean_ctor_set_uint8(v___x_2755_, 17, v___y_2740_);
lean_ctor_set_uint8(v___x_2755_, 18, v___y_2740_);
lean_ctor_set_uint8(v___x_2755_, 19, v___x_2552_);
lean_ctor_set_uint8(v___x_2755_, 20, v___y_2740_);
v___x_2756_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2755_);
v___x_2757_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2757_, 0, v___x_2755_);
lean_ctor_set_uint64(v___x_2757_, sizeof(void*)*1, v___x_2756_);
v___x_2758_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_2759_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__27_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__27_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__27_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2760_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__28_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2761_ = lean_box(0);
lean_inc(v___x_2553_);
v___x_2762_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2762_, 0, v___x_2757_);
lean_ctor_set(v___x_2762_, 1, v___x_2553_);
lean_ctor_set(v___x_2762_, 2, v___x_2759_);
lean_ctor_set(v___x_2762_, 3, v___x_2760_);
lean_ctor_set(v___x_2762_, 4, v___x_2761_);
lean_ctor_set(v___x_2762_, 5, v___x_2690_);
lean_ctor_set(v___x_2762_, 6, v___x_2761_);
lean_ctor_set_uint8(v___x_2762_, sizeof(void*)*7, v___x_2552_);
lean_ctor_set_uint8(v___x_2762_, sizeof(void*)*7 + 1, v___x_2552_);
lean_ctor_set_uint8(v___x_2762_, sizeof(void*)*7 + 2, v___x_2552_);
lean_ctor_set_uint8(v___x_2762_, sizeof(void*)*7 + 3, v___x_2687_);
v___x_2763_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2764_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2765_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2766_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2766_, 0, v___x_2763_);
lean_ctor_set(v___x_2766_, 1, v___x_2764_);
lean_ctor_set(v___x_2766_, 2, v___x_2553_);
lean_ctor_set(v___x_2766_, 3, v___x_2758_);
lean_ctor_set(v___x_2766_, 4, v___x_2765_);
v___x_2767_ = lean_st_mk_ref(v___x_2766_);
v___x_2768_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq(v_val_2749_, v_val_2751_, v___x_2762_, v___x_2767_, v___y_2746_, v___y_2747_);
lean_dec_ref_known(v___x_2762_, 7);
if (lean_obj_tag(v___x_2768_) == 0)
{
lean_object* v_a_2769_; lean_object* v___x_2770_; uint8_t v___x_2771_; 
v_a_2769_ = lean_ctor_get(v___x_2768_, 0);
lean_inc(v_a_2769_);
lean_dec_ref_known(v___x_2768_, 1);
v___x_2770_ = lean_st_ref_get(v___x_2767_);
lean_dec(v___x_2767_);
lean_dec(v___x_2770_);
v___x_2771_ = lean_unbox(v_a_2769_);
lean_dec(v_a_2769_);
if (v___x_2771_ == 0)
{
if (lean_obj_tag(v___y_2742_) == 0)
{
if (lean_obj_tag(v___y_2741_) == 0)
{
v___y_2726_ = v_val_2751_;
v___y_2727_ = v___y_2747_;
v___y_2728_ = v___y_2746_;
v___y_2729_ = v___y_2739_;
v___y_2730_ = v___y_2741_;
v___y_2731_ = v_val_2749_;
v___y_2732_ = v___y_2743_;
v___y_2733_ = v___y_2744_;
goto v___jp_2725_;
}
else
{
lean_object* v_val_2772_; lean_object* v___x_2773_; 
v_val_2772_ = lean_ctor_get(v___y_2741_, 0);
v___x_2773_ = l_Lean_Syntax_getTailPos_x3f(v_val_2772_, v___x_2687_);
if (lean_obj_tag(v___x_2773_) == 0)
{
v___y_2726_ = v_val_2751_;
v___y_2727_ = v___y_2747_;
v___y_2728_ = v___y_2746_;
v___y_2729_ = v___y_2739_;
v___y_2730_ = v___y_2741_;
v___y_2731_ = v_val_2749_;
v___y_2732_ = v___y_2743_;
v___y_2733_ = v___y_2744_;
goto v___jp_2725_;
}
else
{
lean_object* v_val_2774_; 
v_val_2774_ = lean_ctor_get(v___x_2773_, 0);
lean_inc(v_val_2774_);
lean_dec_ref_known(v___x_2773_, 1);
v___y_2693_ = v_val_2751_;
v___y_2694_ = v___y_2747_;
v___y_2695_ = v___y_2746_;
v___y_2696_ = v___y_2739_;
v___y_2697_ = v___y_2741_;
v___y_2698_ = v_val_2749_;
v___y_2699_ = v___y_2743_;
v___y_2700_ = v___y_2744_;
v_val_2701_ = v_val_2774_;
goto v___jp_2692_;
}
}
}
else
{
lean_dec_ref_known(v___y_2742_, 1);
lean_dec(v_val_2751_);
lean_dec(v_val_2749_);
lean_dec_ref(v___f_2551_);
v___y_2629_ = v___y_2739_;
v___y_2630_ = v___y_2741_;
v___y_2631_ = v___y_2743_;
v___y_2632_ = v___y_2744_;
v___y_2633_ = v___y_2746_;
v___y_2634_ = v___y_2747_;
goto v___jp_2628_;
}
}
else
{
lean_dec(v_val_2751_);
lean_dec(v_val_2749_);
lean_dec_ref(v___f_2551_);
if (lean_obj_tag(v___y_2742_) == 0)
{
v___y_2629_ = v___y_2739_;
v___y_2630_ = v___y_2741_;
v___y_2631_ = v___y_2743_;
v___y_2632_ = v___y_2744_;
v___y_2633_ = v___y_2746_;
v___y_2634_ = v___y_2747_;
goto v___jp_2628_;
}
else
{
lean_object* v___x_2775_; lean_object* v___x_2776_; 
lean_dec_ref_known(v___y_2742_, 1);
v___x_2775_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__37_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__37_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__37_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2776_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1(v___x_2775_, v___y_2746_, v___y_2747_);
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_dec_ref_known(v___x_2776_, 1);
v___y_2629_ = v___y_2739_;
v___y_2630_ = v___y_2741_;
v___y_2631_ = v___y_2743_;
v___y_2632_ = v___y_2744_;
v___y_2633_ = v___y_2746_;
v___y_2634_ = v___y_2747_;
goto v___jp_2628_;
}
else
{
lean_object* v_a_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2784_; 
lean_dec(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec(v___y_2741_);
lean_dec(v___y_2739_);
lean_dec(v_stx_2557_);
v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2779_ = v___x_2776_;
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v___x_2776_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___x_2782_; 
if (v_isShared_2780_ == 0)
{
v___x_2782_ = v___x_2779_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_a_2777_);
v___x_2782_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
return v___x_2782_;
}
}
}
}
}
}
else
{
lean_object* v_a_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2792_; 
lean_dec(v___x_2767_);
lean_dec(v_val_2751_);
lean_dec(v_val_2749_);
lean_dec(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec(v___y_2742_);
lean_dec(v___y_2741_);
lean_dec(v___y_2739_);
lean_dec(v_stx_2557_);
lean_dec_ref(v___f_2551_);
v_a_2785_ = lean_ctor_get(v___x_2768_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2768_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2787_ = v___x_2768_;
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_a_2785_);
lean_dec(v___x_2768_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___x_2790_; 
if (v_isShared_2788_ == 0)
{
v___x_2790_ = v___x_2787_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_a_2785_);
v___x_2790_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
return v___x_2790_;
}
}
}
}
else
{
lean_dec(v___x_2750_);
lean_dec(v_val_2749_);
lean_dec(v___y_2742_);
lean_dec(v___x_2553_);
lean_dec_ref(v___f_2551_);
v___y_2629_ = v___y_2739_;
v___y_2630_ = v___y_2741_;
v___y_2631_ = v___y_2743_;
v___y_2632_ = v___y_2744_;
v___y_2633_ = v___y_2746_;
v___y_2634_ = v___y_2747_;
goto v___jp_2628_;
}
}
else
{
lean_dec(v___x_2748_);
lean_dec(v___y_2745_);
lean_dec(v___y_2742_);
lean_dec_ref(v___y_2738_);
lean_dec(v___x_2553_);
lean_dec_ref(v___f_2551_);
v___y_2629_ = v___y_2739_;
v___y_2630_ = v___y_2741_;
v___y_2631_ = v___y_2743_;
v___y_2632_ = v___y_2744_;
v___y_2633_ = v___y_2746_;
v___y_2634_ = v___y_2747_;
goto v___jp_2628_;
}
}
v___jp_2793_:
{
lean_object* v___x_2805_; 
v___x_2805_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1(v_msg_2802_, v___y_2803_, v___y_2804_);
if (lean_obj_tag(v___x_2805_) == 0)
{
lean_dec_ref_known(v___x_2805_, 1);
v___y_2738_ = v___y_2794_;
v___y_2739_ = v___y_2795_;
v___y_2740_ = v___y_2797_;
v___y_2741_ = v___y_2796_;
v___y_2742_ = v___y_2798_;
v___y_2743_ = v___y_2799_;
v___y_2744_ = v___y_2801_;
v___y_2745_ = v___y_2800_;
v___y_2746_ = v___y_2803_;
v___y_2747_ = v___y_2804_;
goto v___jp_2737_;
}
else
{
lean_object* v_a_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2813_; 
lean_dec(v___y_2801_);
lean_dec(v___y_2800_);
lean_dec(v___y_2799_);
lean_dec(v___y_2798_);
lean_dec(v___y_2796_);
lean_dec(v___y_2795_);
lean_dec_ref(v___y_2794_);
lean_dec(v_stx_2557_);
lean_dec(v_declName_2556_);
lean_dec(v___x_2553_);
lean_dec_ref(v___f_2551_);
v_a_2806_ = lean_ctor_get(v___x_2805_, 0);
v_isSharedCheck_2813_ = !lean_is_exclusive(v___x_2805_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2808_ = v___x_2805_;
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_a_2806_);
lean_dec(v___x_2805_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v___x_2811_; 
if (v_isShared_2809_ == 0)
{
v___x_2811_ = v___x_2808_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v_a_2806_);
v___x_2811_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
return v___x_2811_;
}
}
}
}
v___jp_2814_:
{
if (lean_obj_tag(v___y_2815_) == 1)
{
lean_object* v_val_2822_; lean_object* v___x_2823_; 
v_val_2822_ = lean_ctor_get(v___y_2815_, 0);
lean_inc(v_val_2822_);
v___x_2823_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2(v_val_2822_, v___x_2552_, v___y_2820_, v___y_2821_);
if (lean_obj_tag(v___x_2823_) == 0)
{
lean_object* v___x_2824_; lean_object* v_a_2825_; lean_object* v___x_2826_; uint8_t v___x_2827_; 
lean_dec_ref_known(v___x_2823_, 1);
v___x_2824_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__3(v___y_2820_, v___y_2821_);
v_a_2825_ = lean_ctor_get(v___x_2824_, 0);
lean_inc(v_a_2825_);
lean_dec_ref(v___x_2824_);
v___x_2826_ = l_Lean_Linter_linter_deprecated;
v___x_2827_ = l_Lean_Linter_getLinterValue(v___x_2826_, v_a_2825_);
lean_dec(v_a_2825_);
if (v___x_2827_ == 0)
{
lean_dec(v___y_2817_);
lean_dec(v_declName_2556_);
lean_dec_ref(v___x_2554_);
lean_dec(v___x_2553_);
lean_dec_ref(v___f_2551_);
v___y_2629_ = v___y_2815_;
v___y_2630_ = v___y_2816_;
v___y_2631_ = v___y_2818_;
v___y_2632_ = v___y_2819_;
v___y_2633_ = v___y_2820_;
v___y_2634_ = v___y_2821_;
goto v___jp_2628_;
}
else
{
lean_object* v___x_2828_; lean_object* v_env_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; uint8_t v___x_2832_; 
lean_inc(v_val_2822_);
v___x_2828_ = lean_st_ref_get(v___y_2821_);
v_env_2829_ = lean_ctor_get(v___x_2828_, 0);
lean_inc_ref(v_env_2829_);
lean_dec(v___x_2828_);
v___x_2830_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2820_);
v___x_2831_ = l_Lean_Linter_linter_deprecated_deprecatedTarget;
v___x_2832_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__5(v___x_2830_, v___x_2831_);
lean_dec_ref(v___x_2830_);
if (v___x_2832_ == 0)
{
lean_dec_ref(v___x_2554_);
v___y_2738_ = v_env_2829_;
v___y_2739_ = v___y_2815_;
v___y_2740_ = v___x_2827_;
v___y_2741_ = v___y_2816_;
v___y_2742_ = v___y_2817_;
v___y_2743_ = v___y_2818_;
v___y_2744_ = v___y_2819_;
v___y_2745_ = v_val_2822_;
v___y_2746_ = v___y_2820_;
v___y_2747_ = v___y_2821_;
goto v___jp_2737_;
}
else
{
lean_object* v___x_2833_; 
lean_inc(v_val_2822_);
lean_inc_ref(v_env_2829_);
v___x_2833_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v___x_2554_, v_a_2555_, v___x_2552_, v_env_2829_, v_val_2822_);
if (lean_obj_tag(v___x_2833_) == 1)
{
lean_object* v_val_2834_; lean_object* v_name_2835_; lean_object* v_newName_x3f_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; 
v_val_2834_ = lean_ctor_get(v___x_2833_, 0);
lean_inc(v_val_2834_);
lean_dec_ref_known(v___x_2833_, 1);
v_name_2835_ = lean_ctor_get(v___x_2831_, 0);
v_newName_x3f_2836_ = lean_ctor_get(v_val_2834_, 0);
lean_inc(v_newName_x3f_2836_);
lean_dec(v_val_2834_);
v___x_2837_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__39_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__39_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__39_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
lean_inc(v_name_2835_);
v___x_2838_ = l_Lean_MessageData_ofName(v_name_2835_);
v___x_2839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2839_, 0, v___x_2837_);
lean_ctor_set(v___x_2839_, 1, v___x_2838_);
v___x_2840_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2839_);
lean_ctor_set(v___x_2841_, 1, v___x_2840_);
v___x_2842_ = l_Lean_MessageData_note(v___x_2841_);
if (lean_obj_tag(v_newName_x3f_2836_) == 0)
{
lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; 
v___x_2843_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
lean_inc(v_val_2822_);
v___x_2844_ = l_Lean_MessageData_ofConstName(v_val_2822_, v___x_2687_);
v___x_2845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2845_, 0, v___x_2843_);
lean_ctor_set(v___x_2845_, 1, v___x_2844_);
v___x_2846_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2847_, 0, v___x_2845_);
lean_ctor_set(v___x_2847_, 1, v___x_2846_);
lean_inc(v_declName_2556_);
v___x_2848_ = l_Lean_MessageData_ofConstName(v_declName_2556_, v___x_2687_);
v___x_2849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2847_);
lean_ctor_set(v___x_2849_, 1, v___x_2848_);
v___x_2850_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__47_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__47_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__47_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2851_, 0, v___x_2849_);
lean_ctor_set(v___x_2851_, 1, v___x_2850_);
v___x_2852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2852_, 0, v___x_2851_);
lean_ctor_set(v___x_2852_, 1, v___x_2842_);
v___x_2853_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1(v___x_2852_, v___y_2820_, v___y_2821_);
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_dec_ref_known(v___x_2853_, 1);
v___y_2738_ = v_env_2829_;
v___y_2739_ = v___y_2815_;
v___y_2740_ = v___x_2827_;
v___y_2741_ = v___y_2816_;
v___y_2742_ = v___y_2817_;
v___y_2743_ = v___y_2818_;
v___y_2744_ = v___y_2819_;
v___y_2745_ = v_val_2822_;
v___y_2746_ = v___y_2820_;
v___y_2747_ = v___y_2821_;
goto v___jp_2737_;
}
else
{
lean_object* v_a_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2861_; 
lean_dec_ref(v_env_2829_);
lean_dec_ref_known(v___y_2815_, 1);
lean_dec(v_val_2822_);
lean_dec(v___y_2819_);
lean_dec(v___y_2818_);
lean_dec(v___y_2817_);
lean_dec(v___y_2816_);
lean_dec(v_stx_2557_);
lean_dec(v_declName_2556_);
lean_dec(v___x_2553_);
lean_dec_ref(v___f_2551_);
v_a_2854_ = lean_ctor_get(v___x_2853_, 0);
v_isSharedCheck_2861_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_2861_ == 0)
{
v___x_2856_ = v___x_2853_;
v_isShared_2857_ = v_isSharedCheck_2861_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_a_2854_);
lean_dec(v___x_2853_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2861_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___x_2859_; 
if (v_isShared_2857_ == 0)
{
v___x_2859_ = v___x_2856_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_a_2854_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
return v___x_2859_;
}
}
}
}
else
{
lean_object* v_val_2862_; uint8_t v___x_2863_; 
v_val_2862_ = lean_ctor_get(v_newName_x3f_2836_, 0);
lean_inc(v_val_2862_);
lean_dec_ref_known(v_newName_x3f_2836_, 1);
v___x_2863_ = lean_name_eq(v_val_2862_, v_val_2822_);
if (v___x_2863_ == 0)
{
lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; 
v___x_2864_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
lean_inc(v_val_2822_);
v___x_2865_ = l_Lean_MessageData_ofConstName(v_val_2822_, v___x_2687_);
v___x_2866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2864_);
lean_ctor_set(v___x_2866_, 1, v___x_2865_);
v___x_2867_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__49_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__49_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__49_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2868_, 0, v___x_2866_);
lean_ctor_set(v___x_2868_, 1, v___x_2867_);
lean_inc(v_val_2862_);
v___x_2869_ = l_Lean_MessageData_ofConstName(v_val_2862_, v___x_2687_);
lean_inc_ref_n(v___x_2869_, 2);
v___x_2870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2870_, 0, v___x_2868_);
lean_ctor_set(v___x_2870_, 1, v___x_2869_);
v___x_2871_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__51_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__51_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__51_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2870_);
lean_ctor_set(v___x_2872_, 1, v___x_2871_);
lean_inc(v_declName_2556_);
v___x_2873_ = l_Lean_MessageData_ofConstName(v_declName_2556_, v___x_2687_);
v___x_2874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2874_, 0, v___x_2872_);
lean_ctor_set(v___x_2874_, 1, v___x_2873_);
v___x_2875_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__53_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__53_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__53_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2874_);
lean_ctor_set(v___x_2876_, 1, v___x_2875_);
v___x_2877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2876_);
lean_ctor_set(v___x_2877_, 1, v___x_2869_);
v___x_2878_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__55_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__55_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__55_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2877_);
lean_ctor_set(v___x_2879_, 1, v___x_2878_);
v___x_2880_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2880_, 0, v___x_2879_);
lean_ctor_set(v___x_2880_, 1, v___x_2842_);
if (lean_obj_tag(v___y_2818_) == 1)
{
lean_object* v_val_2881_; lean_object* v___x_2882_; 
v_val_2881_ = lean_ctor_get(v___y_2818_, 0);
v___x_2882_ = l_Lean_Syntax_getRange_x3f(v_val_2881_, v___x_2687_);
if (lean_obj_tag(v___x_2882_) == 0)
{
lean_dec_ref(v___x_2869_);
lean_dec(v_val_2862_);
v___y_2794_ = v_env_2829_;
v___y_2795_ = v___y_2815_;
v___y_2796_ = v___y_2816_;
v___y_2797_ = v___x_2827_;
v___y_2798_ = v___y_2817_;
v___y_2799_ = v___y_2818_;
v___y_2800_ = v_val_2822_;
v___y_2801_ = v___y_2819_;
v_msg_2802_ = v___x_2880_;
v___y_2803_ = v___y_2820_;
v___y_2804_ = v___y_2821_;
goto v___jp_2793_;
}
else
{
lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2945_; 
v_isSharedCheck_2945_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_2945_ == 0)
{
lean_object* v_unused_2946_; 
v_unused_2946_ = lean_ctor_get(v___x_2882_, 0);
lean_dec(v_unused_2946_);
v___x_2884_ = v___x_2882_;
v_isShared_2885_ = v_isSharedCheck_2945_;
goto v_resetjp_2883_;
}
else
{
lean_dec(v___x_2882_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2945_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
uint8_t v___x_2886_; uint8_t v___x_2887_; uint8_t v___x_2888_; lean_object* v___x_2889_; uint64_t v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; 
v___x_2886_ = 1;
v___x_2887_ = 0;
v___x_2888_ = 2;
v___x_2889_ = lean_alloc_ctor(0, 0, 21);
lean_ctor_set_uint8(v___x_2889_, 0, v___x_2863_);
lean_ctor_set_uint8(v___x_2889_, 1, v___x_2863_);
lean_ctor_set_uint8(v___x_2889_, 2, v___x_2863_);
lean_ctor_set_uint8(v___x_2889_, 3, v___x_2863_);
lean_ctor_set_uint8(v___x_2889_, 4, v___x_2863_);
lean_ctor_set_uint8(v___x_2889_, 5, v___x_2832_);
lean_ctor_set_uint8(v___x_2889_, 6, v___x_2832_);
lean_ctor_set_uint8(v___x_2889_, 7, v___x_2863_);
lean_ctor_set_uint8(v___x_2889_, 8, v___x_2832_);
lean_ctor_set_uint8(v___x_2889_, 9, v___x_2886_);
lean_ctor_set_uint8(v___x_2889_, 10, v___x_2887_);
lean_ctor_set_uint8(v___x_2889_, 11, v___x_2832_);
lean_ctor_set_uint8(v___x_2889_, 12, v___x_2832_);
lean_ctor_set_uint8(v___x_2889_, 13, v___x_2832_);
lean_ctor_set_uint8(v___x_2889_, 14, v___x_2888_);
lean_ctor_set_uint8(v___x_2889_, 15, v___x_2832_);
lean_ctor_set_uint8(v___x_2889_, 16, v___x_2832_);
lean_ctor_set_uint8(v___x_2889_, 17, v___x_2832_);
lean_ctor_set_uint8(v___x_2889_, 18, v___x_2832_);
lean_ctor_set_uint8(v___x_2889_, 19, v___x_2863_);
lean_ctor_set_uint8(v___x_2889_, 20, v___x_2832_);
v___x_2890_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2889_);
v___x_2891_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2891_, 0, v___x_2889_);
lean_ctor_set_uint64(v___x_2891_, sizeof(void*)*1, v___x_2890_);
v___x_2892_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_2893_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__27_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__27_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__27_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2894_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__28_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2895_ = lean_box(0);
lean_inc_n(v___x_2553_, 2);
v___x_2896_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2896_, 0, v___x_2891_);
lean_ctor_set(v___x_2896_, 1, v___x_2553_);
lean_ctor_set(v___x_2896_, 2, v___x_2893_);
lean_ctor_set(v___x_2896_, 3, v___x_2894_);
lean_ctor_set(v___x_2896_, 4, v___x_2895_);
lean_ctor_set(v___x_2896_, 5, v___x_2690_);
lean_ctor_set(v___x_2896_, 6, v___x_2895_);
lean_ctor_set_uint8(v___x_2896_, sizeof(void*)*7, v___x_2552_);
lean_ctor_set_uint8(v___x_2896_, sizeof(void*)*7 + 1, v___x_2552_);
lean_ctor_set_uint8(v___x_2896_, sizeof(void*)*7 + 2, v___x_2552_);
lean_ctor_set_uint8(v___x_2896_, sizeof(void*)*7 + 3, v___x_2687_);
v___x_2897_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2898_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2899_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2900_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2900_, 0, v___x_2897_);
lean_ctor_set(v___x_2900_, 1, v___x_2898_);
lean_ctor_set(v___x_2900_, 2, v___x_2553_);
lean_ctor_set(v___x_2900_, 3, v___x_2892_);
lean_ctor_set(v___x_2900_, 4, v___x_2899_);
v___x_2901_ = lean_st_mk_ref(v___x_2900_);
v___x_2902_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6(v_val_2862_, v___x_2552_, v___x_2896_, v___x_2901_, v___y_2820_, v___y_2821_);
lean_dec_ref_known(v___x_2896_, 7);
if (lean_obj_tag(v___x_2902_) == 0)
{
lean_object* v_a_2903_; lean_object* v___x_2904_; 
v_a_2903_ = lean_ctor_get(v___x_2902_, 0);
lean_inc(v_a_2903_);
lean_dec_ref_known(v___x_2902_, 1);
v___x_2904_ = lean_st_ref_get(v___x_2901_);
lean_dec(v___x_2901_);
lean_dec(v___x_2904_);
if (lean_obj_tag(v_a_2903_) == 1)
{
lean_object* v_val_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2936_; 
v_val_2905_ = lean_ctor_get(v_a_2903_, 0);
v_isSharedCheck_2936_ = !lean_is_exclusive(v_a_2903_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2907_ = v_a_2903_;
v_isShared_2908_ = v_isSharedCheck_2936_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_val_2905_);
lean_dec(v_a_2903_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2936_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2915_; 
v___x_2909_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__57_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__57_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__57_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2910_, 0, v___x_2909_);
lean_ctor_set(v___x_2910_, 1, v___x_2869_);
v___x_2911_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__59_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__59_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__59_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2910_);
lean_ctor_set(v___x_2912_, 1, v___x_2911_);
v___x_2913_ = l_Lean_Name_toString(v_val_2905_, v___x_2687_);
if (v_isShared_2885_ == 0)
{
lean_ctor_set(v___x_2884_, 0, v___x_2913_);
v___x_2915_ = v___x_2884_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v___x_2913_);
v___x_2915_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
lean_object* v___x_2916_; uint8_t v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2922_; 
v___x_2916_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2916_, 0, v___x_2915_);
lean_ctor_set(v___x_2916_, 1, v___x_2895_);
lean_ctor_set(v___x_2916_, 2, v___x_2895_);
lean_ctor_set(v___x_2916_, 3, v___x_2895_);
lean_ctor_set(v___x_2916_, 4, v___x_2895_);
lean_ctor_set(v___x_2916_, 5, v___x_2895_);
v___x_2917_ = 0;
v___x_2918_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2918_, 0, v___x_2916_);
lean_ctor_set(v___x_2918_, 1, v___x_2895_);
lean_ctor_set(v___x_2918_, 2, v___x_2895_);
lean_ctor_set_uint8(v___x_2918_, sizeof(void*)*3, v___x_2917_);
v___x_2919_ = lean_mk_empty_array_with_capacity(v___x_2691_);
v___x_2920_ = lean_array_push(v___x_2919_, v___x_2918_);
lean_inc(v_val_2881_);
if (v_isShared_2908_ == 0)
{
lean_ctor_set(v___x_2907_, 0, v_val_2881_);
v___x_2922_ = v___x_2907_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_val_2881_);
v___x_2922_ = v_reuseFailAlloc_2934_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
lean_object* v___x_2923_; 
v___x_2923_ = l_Lean_MessageData_hint(v___x_2912_, v___x_2920_, v___x_2922_, v___x_2895_, v___x_2552_, v___y_2820_, v___y_2821_);
lean_dec_ref(v___x_2920_);
if (lean_obj_tag(v___x_2923_) == 0)
{
lean_object* v_a_2924_; lean_object* v___x_2925_; 
v_a_2924_ = lean_ctor_get(v___x_2923_, 0);
lean_inc(v_a_2924_);
lean_dec_ref_known(v___x_2923_, 1);
v___x_2925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2925_, 0, v___x_2880_);
lean_ctor_set(v___x_2925_, 1, v_a_2924_);
v___y_2794_ = v_env_2829_;
v___y_2795_ = v___y_2815_;
v___y_2796_ = v___y_2816_;
v___y_2797_ = v___x_2827_;
v___y_2798_ = v___y_2817_;
v___y_2799_ = v___y_2818_;
v___y_2800_ = v_val_2822_;
v___y_2801_ = v___y_2819_;
v_msg_2802_ = v___x_2925_;
v___y_2803_ = v___y_2820_;
v___y_2804_ = v___y_2821_;
goto v___jp_2793_;
}
else
{
lean_object* v_a_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2933_; 
lean_dec_ref_known(v___y_2818_, 1);
lean_dec_ref_known(v___x_2880_, 2);
lean_dec_ref(v_env_2829_);
lean_dec(v_val_2822_);
lean_dec_ref_known(v___y_2815_, 1);
lean_dec(v___y_2819_);
lean_dec(v___y_2817_);
lean_dec(v___y_2816_);
lean_dec(v_stx_2557_);
lean_dec(v_declName_2556_);
lean_dec(v___x_2553_);
lean_dec_ref(v___f_2551_);
v_a_2926_ = lean_ctor_get(v___x_2923_, 0);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___x_2923_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2928_ = v___x_2923_;
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_a_2926_);
lean_dec(v___x_2923_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v___x_2931_; 
if (v_isShared_2929_ == 0)
{
v___x_2931_ = v___x_2928_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_a_2926_);
v___x_2931_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
return v___x_2931_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2903_);
lean_del_object(v___x_2884_);
lean_dec_ref(v___x_2869_);
v___y_2794_ = v_env_2829_;
v___y_2795_ = v___y_2815_;
v___y_2796_ = v___y_2816_;
v___y_2797_ = v___x_2827_;
v___y_2798_ = v___y_2817_;
v___y_2799_ = v___y_2818_;
v___y_2800_ = v_val_2822_;
v___y_2801_ = v___y_2819_;
v_msg_2802_ = v___x_2880_;
v___y_2803_ = v___y_2820_;
v___y_2804_ = v___y_2821_;
goto v___jp_2793_;
}
}
else
{
lean_object* v_a_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2944_; 
lean_dec(v___x_2901_);
lean_del_object(v___x_2884_);
lean_dec_ref_known(v___y_2818_, 1);
lean_dec_ref_known(v___x_2880_, 2);
lean_dec_ref(v___x_2869_);
lean_dec_ref(v_env_2829_);
lean_dec_ref_known(v___y_2815_, 1);
lean_dec(v_val_2822_);
lean_dec(v___y_2819_);
lean_dec(v___y_2817_);
lean_dec(v___y_2816_);
lean_dec(v_stx_2557_);
lean_dec(v_declName_2556_);
lean_dec(v___x_2553_);
lean_dec_ref(v___f_2551_);
v_a_2937_ = lean_ctor_get(v___x_2902_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2939_ = v___x_2902_;
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_a_2937_);
lean_dec(v___x_2902_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v___x_2942_; 
if (v_isShared_2940_ == 0)
{
v___x_2942_ = v___x_2939_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_a_2937_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_2869_);
lean_dec(v_val_2862_);
v___y_2794_ = v_env_2829_;
v___y_2795_ = v___y_2815_;
v___y_2796_ = v___y_2816_;
v___y_2797_ = v___x_2827_;
v___y_2798_ = v___y_2817_;
v___y_2799_ = v___y_2818_;
v___y_2800_ = v_val_2822_;
v___y_2801_ = v___y_2819_;
v_msg_2802_ = v___x_2880_;
v___y_2803_ = v___y_2820_;
v___y_2804_ = v___y_2821_;
goto v___jp_2793_;
}
}
else
{
lean_dec(v_val_2862_);
lean_dec_ref(v___x_2842_);
v___y_2738_ = v_env_2829_;
v___y_2739_ = v___y_2815_;
v___y_2740_ = v___x_2827_;
v___y_2741_ = v___y_2816_;
v___y_2742_ = v___y_2817_;
v___y_2743_ = v___y_2818_;
v___y_2744_ = v___y_2819_;
v___y_2745_ = v_val_2822_;
v___y_2746_ = v___y_2820_;
v___y_2747_ = v___y_2821_;
goto v___jp_2737_;
}
}
}
else
{
lean_dec(v___x_2833_);
v___y_2738_ = v_env_2829_;
v___y_2739_ = v___y_2815_;
v___y_2740_ = v___x_2827_;
v___y_2741_ = v___y_2816_;
v___y_2742_ = v___y_2817_;
v___y_2743_ = v___y_2818_;
v___y_2744_ = v___y_2819_;
v___y_2745_ = v_val_2822_;
v___y_2746_ = v___y_2820_;
v___y_2747_ = v___y_2821_;
goto v___jp_2737_;
}
}
}
}
else
{
lean_object* v_a_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2954_; 
lean_dec_ref_known(v___y_2815_, 1);
lean_dec(v___y_2819_);
lean_dec(v___y_2818_);
lean_dec(v___y_2817_);
lean_dec(v___y_2816_);
lean_dec(v_stx_2557_);
lean_dec(v_declName_2556_);
lean_dec_ref(v___x_2554_);
lean_dec(v___x_2553_);
lean_dec_ref(v___f_2551_);
v_a_2947_ = lean_ctor_get(v___x_2823_, 0);
v_isSharedCheck_2954_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2954_ == 0)
{
v___x_2949_ = v___x_2823_;
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_a_2947_);
lean_dec(v___x_2823_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v___x_2952_; 
if (v_isShared_2950_ == 0)
{
v___x_2952_ = v___x_2949_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_a_2947_);
v___x_2952_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
return v___x_2952_;
}
}
}
}
else
{
lean_dec(v___y_2817_);
lean_dec(v_declName_2556_);
lean_dec_ref(v___x_2554_);
lean_dec(v___x_2553_);
lean_dec_ref(v___f_2551_);
v___y_2629_ = v___y_2815_;
v___y_2630_ = v___y_2816_;
v___y_2631_ = v___y_2818_;
v___y_2632_ = v___y_2819_;
v___y_2633_ = v___y_2820_;
v___y_2634_ = v___y_2821_;
goto v___jp_2628_;
}
}
v___jp_2955_:
{
lean_object* v___x_2963_; uint8_t v___x_2964_; 
lean_inc(v_declName_2556_);
v___x_2963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2963_, 0, v_declName_2556_);
v___x_2964_ = l_instBEqOption_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__7(v_a_2962_, v___x_2963_);
lean_dec_ref_known(v___x_2963_, 1);
if (v___x_2964_ == 0)
{
v___y_2815_ = v_a_2962_;
v___y_2816_ = v___y_2958_;
v___y_2817_ = v___y_2959_;
v___y_2818_ = v___y_2960_;
v___y_2819_ = v___y_2961_;
v___y_2820_ = v___y_2957_;
v___y_2821_ = v___y_2956_;
goto v___jp_2814_;
}
else
{
lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v_a_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2978_; 
lean_dec(v_a_2962_);
lean_dec(v___y_2961_);
lean_dec(v___y_2960_);
lean_dec(v___y_2959_);
lean_dec(v___y_2958_);
lean_dec(v_stx_2557_);
lean_dec_ref(v___x_2554_);
lean_dec(v___x_2553_);
lean_dec_ref(v___f_2551_);
v___x_2965_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__61_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__61_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__61_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2966_ = l_Lean_MessageData_ofConstName(v_declName_2556_, v___x_2687_);
v___x_2967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2967_, 0, v___x_2965_);
lean_ctor_set(v___x_2967_, 1, v___x_2966_);
v___x_2968_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__63_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__63_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__63_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2969_, 0, v___x_2967_);
lean_ctor_set(v___x_2969_, 1, v___x_2968_);
v___x_2970_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0___redArg(v___x_2969_, v___y_2957_, v___y_2956_);
v_a_2971_ = lean_ctor_get(v___x_2970_, 0);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2970_);
if (v_isSharedCheck_2978_ == 0)
{
v___x_2973_ = v___x_2970_;
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_a_2971_);
lean_dec(v___x_2970_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v___x_2976_; 
if (v_isShared_2974_ == 0)
{
v___x_2976_ = v___x_2973_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_a_2971_);
v___x_2976_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
return v___x_2976_;
}
}
}
}
v___jp_2979_:
{
if (lean_obj_tag(v___y_2982_) == 0)
{
lean_object* v___x_2986_; 
v___x_2986_ = lean_box(0);
v___y_2956_ = v___y_2985_;
v___y_2957_ = v___y_2984_;
v___y_2958_ = v___y_2980_;
v___y_2959_ = v___y_2981_;
v___y_2960_ = v___y_2982_;
v___y_2961_ = v_since_x3f_2983_;
v_a_2962_ = v___x_2986_;
goto v___jp_2955_;
}
else
{
lean_object* v_val_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
v_val_2987_ = lean_ctor_get(v___y_2982_, 0);
v___x_2988_ = lean_box(0);
lean_inc(v_val_2987_);
v___x_2989_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_val_2987_, v___x_2988_, v___y_2984_, v___y_2985_);
if (lean_obj_tag(v___x_2989_) == 0)
{
lean_object* v_a_2990_; lean_object* v___x_2991_; 
v_a_2990_ = lean_ctor_get(v___x_2989_, 0);
lean_inc(v_a_2990_);
lean_dec_ref_known(v___x_2989_, 1);
v___x_2991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2991_, 0, v_a_2990_);
v___y_2956_ = v___y_2985_;
v___y_2957_ = v___y_2984_;
v___y_2958_ = v___y_2980_;
v___y_2959_ = v___y_2981_;
v___y_2960_ = v___y_2982_;
v___y_2961_ = v_since_x3f_2983_;
v_a_2962_ = v___x_2991_;
goto v___jp_2955_;
}
else
{
lean_object* v_a_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_2999_; 
lean_dec_ref_known(v___y_2982_, 1);
lean_dec(v_since_x3f_2983_);
lean_dec(v___y_2981_);
lean_dec(v___y_2980_);
lean_dec(v_stx_2557_);
lean_dec(v_declName_2556_);
lean_dec_ref(v___x_2554_);
lean_dec(v___x_2553_);
lean_dec_ref(v___f_2551_);
v_a_2992_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_2999_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2994_ = v___x_2989_;
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_a_2992_);
lean_dec(v___x_2989_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2997_; 
if (v_isShared_2995_ == 0)
{
v___x_2997_ = v___x_2994_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_a_2992_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
return v___x_2997_;
}
}
}
}
}
v___jp_3000_:
{
lean_object* v___x_3007_; lean_object* v___x_3008_; uint8_t v___x_3009_; 
v___x_3007_ = lean_unsigned_to_nat(4u);
v___x_3008_ = l_Lean_Syntax_getArg(v_stx_2557_, v___x_3007_);
v___x_3009_ = l_Lean_Syntax_isNone(v___x_3008_);
if (v___x_3009_ == 0)
{
lean_object* v___x_3010_; uint8_t v___x_3011_; 
v___x_3010_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_3008_);
v___x_3011_ = l_Lean_Syntax_matchesNull(v___x_3008_, v___x_3010_);
if (v___x_3011_ == 0)
{
lean_object* v___x_3012_; lean_object* v___x_3013_; 
lean_dec(v___x_3008_);
lean_dec(v_typeChanged_x3f_3004_);
lean_dec(v___y_3003_);
lean_dec(v___y_3002_);
lean_dec(v_stx_2557_);
lean_dec(v_declName_2556_);
lean_dec_ref(v___x_2554_);
lean_dec(v___x_2553_);
lean_dec_ref(v___f_2551_);
v___x_3012_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_3013_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0___redArg(v___x_3012_, v___y_3005_, v___y_3006_);
return v___x_3013_;
}
else
{
lean_object* v___x_3014_; lean_object* v___x_3015_; 
v___x_3014_ = l_Lean_Syntax_getArg(v___x_3008_, v___y_3001_);
lean_dec(v___x_3008_);
v___x_3015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3015_, 0, v___x_3014_);
v___y_2980_ = v___y_3002_;
v___y_2981_ = v_typeChanged_x3f_3004_;
v___y_2982_ = v___y_3003_;
v_since_x3f_2983_ = v___x_3015_;
v___y_2984_ = v___y_3005_;
v___y_2985_ = v___y_3006_;
goto v___jp_2979_;
}
}
else
{
lean_object* v___x_3016_; 
lean_dec(v___x_3008_);
v___x_3016_ = lean_box(0);
v___y_2980_ = v___y_3002_;
v___y_2981_ = v_typeChanged_x3f_3004_;
v___y_2982_ = v___y_3003_;
v_since_x3f_2983_ = v___x_3016_;
v___y_2984_ = v___y_3005_;
v___y_2985_ = v___y_3006_;
goto v___jp_2979_;
}
}
v___jp_3017_:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; uint8_t v___x_3024_; 
v___x_3022_ = lean_unsigned_to_nat(3u);
v___x_3023_ = l_Lean_Syntax_getArg(v_stx_2557_, v___x_3022_);
v___x_3024_ = l_Lean_Syntax_isNone(v___x_3023_);
if (v___x_3024_ == 0)
{
uint8_t v___x_3025_; 
lean_inc(v___x_3023_);
v___x_3025_ = l_Lean_Syntax_matchesNull(v___x_3023_, v___x_2691_);
if (v___x_3025_ == 0)
{
lean_object* v___x_3026_; lean_object* v___x_3027_; 
lean_dec(v___x_3023_);
lean_dec(v_text_x3f_3019_);
lean_dec(v___y_3018_);
lean_dec(v_stx_2557_);
lean_dec(v_declName_2556_);
lean_dec_ref(v___x_2554_);
lean_dec(v___x_2553_);
lean_dec_ref(v___f_2551_);
v___x_3026_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_3027_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0___redArg(v___x_3026_, v___y_3020_, v___y_3021_);
return v___x_3027_;
}
else
{
lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3028_ = l_Lean_Syntax_getArg(v___x_3023_, v___x_2690_);
lean_dec(v___x_3023_);
v___x_3029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3028_);
v___y_3001_ = v___x_3022_;
v___y_3002_ = v_text_x3f_3019_;
v___y_3003_ = v___y_3018_;
v_typeChanged_x3f_3004_ = v___x_3029_;
v___y_3005_ = v___y_3020_;
v___y_3006_ = v___y_3021_;
goto v___jp_3000_;
}
}
else
{
lean_object* v___x_3030_; 
lean_dec(v___x_3023_);
v___x_3030_ = lean_box(0);
v___y_3001_ = v___x_3022_;
v___y_3002_ = v_text_x3f_3019_;
v___y_3003_ = v___y_3018_;
v_typeChanged_x3f_3004_ = v___x_3030_;
v___y_3005_ = v___y_3020_;
v___y_3006_ = v___y_3021_;
goto v___jp_3000_;
}
}
v___jp_3031_:
{
lean_object* v___x_3035_; lean_object* v___x_3036_; uint8_t v___x_3037_; 
v___x_3035_ = lean_unsigned_to_nat(2u);
v___x_3036_ = l_Lean_Syntax_getArg(v_stx_2557_, v___x_3035_);
v___x_3037_ = l_Lean_Syntax_isNone(v___x_3036_);
if (v___x_3037_ == 0)
{
uint8_t v___x_3038_; 
lean_inc(v___x_3036_);
v___x_3038_ = l_Lean_Syntax_matchesNull(v___x_3036_, v___x_2691_);
if (v___x_3038_ == 0)
{
lean_object* v___x_3039_; lean_object* v___x_3040_; 
lean_dec(v___x_3036_);
lean_dec(v_id_x3f_3032_);
lean_dec(v_stx_2557_);
lean_dec(v_declName_2556_);
lean_dec_ref(v___x_2554_);
lean_dec(v___x_2553_);
lean_dec_ref(v___f_2551_);
v___x_3039_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_3040_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0___redArg(v___x_3039_, v___y_3033_, v___y_3034_);
return v___x_3040_;
}
else
{
lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___x_3041_ = l_Lean_Syntax_getArg(v___x_3036_, v___x_2690_);
lean_dec(v___x_3036_);
v___x_3042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3042_, 0, v___x_3041_);
v___y_3018_ = v_id_x3f_3032_;
v_text_x3f_3019_ = v___x_3042_;
v___y_3020_ = v___y_3033_;
v___y_3021_ = v___y_3034_;
goto v___jp_3017_;
}
}
else
{
lean_object* v___x_3043_; 
lean_dec(v___x_3036_);
v___x_3043_ = lean_box(0);
v___y_3018_ = v_id_x3f_3032_;
v_text_x3f_3019_ = v___x_3043_;
v___y_3020_ = v___y_3033_;
v___y_3021_ = v___y_3034_;
goto v___jp_3017_;
}
}
}
v___jp_2561_:
{
lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2565_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2565_, 0, v___y_2563_);
lean_ctor_set(v___x_2565_, 1, v___y_2564_);
lean_ctor_set(v___x_2565_, 2, v___y_2562_);
v___x_2566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2566_, 0, v___x_2565_);
return v___x_2566_;
}
v___jp_2567_:
{
if (lean_obj_tag(v___y_2568_) == 0)
{
lean_object* v___x_2573_; 
v___x_2573_ = l_Lean_Linter_mkSinceHint(v_stx_2557_, v___y_2571_, v___y_2572_);
if (lean_obj_tag(v___x_2573_) == 0)
{
lean_object* v_a_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
v_a_2574_ = lean_ctor_get(v___x_2573_, 0);
lean_inc(v_a_2574_);
lean_dec_ref_known(v___x_2573_, 1);
v___x_2575_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__1_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__1_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__1_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2575_);
lean_ctor_set(v___x_2576_, 1, v_a_2574_);
v___x_2577_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1(v___x_2576_, v___y_2571_, v___y_2572_);
if (lean_obj_tag(v___x_2577_) == 0)
{
lean_dec_ref_known(v___x_2577_, 1);
v___y_2562_ = v___y_2568_;
v___y_2563_ = v___y_2569_;
v___y_2564_ = v___y_2570_;
goto v___jp_2561_;
}
else
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2585_; 
lean_dec(v___y_2570_);
lean_dec(v___y_2569_);
v_a_2578_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2580_ = v___x_2577_;
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2577_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2583_; 
if (v_isShared_2581_ == 0)
{
v___x_2583_ = v___x_2580_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_a_2578_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
}
else
{
lean_object* v_a_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2593_; 
lean_dec(v___y_2570_);
lean_dec(v___y_2569_);
v_a_2586_ = lean_ctor_get(v___x_2573_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2588_ = v___x_2573_;
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_a_2586_);
lean_dec(v___x_2573_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v___x_2591_; 
if (v_isShared_2589_ == 0)
{
v___x_2591_ = v___x_2588_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_a_2586_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
}
}
else
{
lean_dec(v_stx_2557_);
v___y_2562_ = v___y_2568_;
v___y_2563_ = v___y_2569_;
v___y_2564_ = v___y_2570_;
goto v___jp_2561_;
}
}
v___jp_2594_:
{
if (lean_obj_tag(v___y_2599_) == 0)
{
if (lean_obj_tag(v___y_2598_) == 0)
{
lean_object* v___x_2601_; lean_object* v___x_2602_; 
v___x_2601_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__4_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__4_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__4_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2602_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1(v___x_2601_, v___y_2597_, v___y_2595_);
if (lean_obj_tag(v___x_2602_) == 0)
{
lean_dec_ref_known(v___x_2602_, 1);
v___y_2568_ = v___y_2600_;
v___y_2569_ = v___y_2596_;
v___y_2570_ = v___y_2598_;
v___y_2571_ = v___y_2597_;
v___y_2572_ = v___y_2595_;
goto v___jp_2567_;
}
else
{
lean_object* v_a_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2610_; 
lean_dec(v___y_2600_);
lean_dec(v___y_2596_);
lean_dec(v_stx_2557_);
v_a_2603_ = lean_ctor_get(v___x_2602_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2605_ = v___x_2602_;
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_a_2603_);
lean_dec(v___x_2602_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2608_; 
if (v_isShared_2606_ == 0)
{
v___x_2608_ = v___x_2605_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_a_2603_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
}
}
else
{
v___y_2568_ = v___y_2600_;
v___y_2569_ = v___y_2596_;
v___y_2570_ = v___y_2598_;
v___y_2571_ = v___y_2597_;
v___y_2572_ = v___y_2595_;
goto v___jp_2567_;
}
}
else
{
lean_dec_ref_known(v___y_2599_, 1);
v___y_2568_ = v___y_2600_;
v___y_2569_ = v___y_2596_;
v___y_2570_ = v___y_2598_;
v___y_2571_ = v___y_2597_;
v___y_2572_ = v___y_2595_;
goto v___jp_2567_;
}
}
v___jp_2611_:
{
if (lean_obj_tag(v___y_2616_) == 0)
{
lean_object* v___x_2618_; 
v___x_2618_ = lean_box(0);
v___y_2595_ = v___y_2612_;
v___y_2596_ = v___y_2613_;
v___y_2597_ = v___y_2614_;
v___y_2598_ = v___y_2617_;
v___y_2599_ = v___y_2615_;
v___y_2600_ = v___x_2618_;
goto v___jp_2594_;
}
else
{
lean_object* v_val_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2627_; 
v_val_2619_ = lean_ctor_get(v___y_2616_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___y_2616_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2621_ = v___y_2616_;
v_isShared_2622_ = v_isSharedCheck_2627_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_val_2619_);
lean_dec(v___y_2616_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2627_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2623_; lean_object* v___x_2625_; 
v___x_2623_ = l_Lean_TSyntax_getString(v_val_2619_);
lean_dec(v_val_2619_);
if (v_isShared_2622_ == 0)
{
lean_ctor_set(v___x_2621_, 0, v___x_2623_);
v___x_2625_ = v___x_2621_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v___x_2623_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
v___y_2595_ = v___y_2612_;
v___y_2596_ = v___y_2613_;
v___y_2597_ = v___y_2614_;
v___y_2598_ = v___y_2617_;
v___y_2599_ = v___y_2615_;
v___y_2600_ = v___x_2625_;
goto v___jp_2594_;
}
}
}
}
v___jp_2628_:
{
if (lean_obj_tag(v___y_2630_) == 0)
{
lean_object* v___x_2635_; 
v___x_2635_ = lean_box(0);
v___y_2612_ = v___y_2634_;
v___y_2613_ = v___y_2629_;
v___y_2614_ = v___y_2633_;
v___y_2615_ = v___y_2631_;
v___y_2616_ = v___y_2632_;
v___y_2617_ = v___x_2635_;
goto v___jp_2611_;
}
else
{
lean_object* v_val_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2644_; 
v_val_2636_ = lean_ctor_get(v___y_2630_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___y_2630_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2638_ = v___y_2630_;
v_isShared_2639_ = v_isSharedCheck_2644_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_val_2636_);
lean_dec(v___y_2630_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2644_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
lean_object* v___x_2640_; lean_object* v___x_2642_; 
v___x_2640_ = l_Lean_TSyntax_getString(v_val_2636_);
lean_dec(v_val_2636_);
if (v_isShared_2639_ == 0)
{
lean_ctor_set(v___x_2638_, 0, v___x_2640_);
v___x_2642_ = v___x_2638_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v___x_2640_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
v___y_2612_ = v___y_2634_;
v___y_2613_ = v___y_2629_;
v___y_2614_ = v___y_2633_;
v___y_2615_ = v___y_2631_;
v___y_2616_ = v___y_2632_;
v___y_2617_ = v___x_2642_;
goto v___jp_2611_;
}
}
}
}
v___jp_2645_:
{
lean_object* v_type_2655_; lean_object* v_type_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; 
v_type_2655_ = lean_ctor_get(v___y_2646_, 2);
lean_inc_ref(v_type_2655_);
lean_dec_ref(v___y_2646_);
v_type_2656_ = lean_ctor_get(v___y_2649_, 2);
lean_inc_ref(v_type_2656_);
lean_dec_ref(v___y_2649_);
v___x_2657_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2658_ = l_Lean_indentExpr(v_type_2655_);
v___x_2659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2659_, 0, v___x_2657_);
lean_ctor_set(v___x_2659_, 1, v___x_2658_);
v___x_2660_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2661_, 0, v___x_2659_);
lean_ctor_set(v___x_2661_, 1, v___x_2660_);
v___x_2662_ = l_Lean_indentExpr(v_type_2656_);
v___x_2663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2663_, 0, v___x_2661_);
lean_ctor_set(v___x_2663_, 1, v___x_2662_);
v___x_2664_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__10_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__10_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__10_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2665_, 0, v___x_2663_);
lean_ctor_set(v___x_2665_, 1, v___x_2664_);
v___x_2666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2666_, 0, v___x_2665_);
lean_ctor_set(v___x_2666_, 1, v_hint_2652_);
v___x_2667_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1(v___x_2666_, v___y_2653_, v___y_2654_);
if (lean_obj_tag(v___x_2667_) == 0)
{
lean_dec_ref_known(v___x_2667_, 1);
v___y_2629_ = v___y_2647_;
v___y_2630_ = v___y_2648_;
v___y_2631_ = v___y_2650_;
v___y_2632_ = v___y_2651_;
v___y_2633_ = v___y_2653_;
v___y_2634_ = v___y_2654_;
goto v___jp_2628_;
}
else
{
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2675_; 
lean_dec(v___y_2651_);
lean_dec(v___y_2650_);
lean_dec(v___y_2648_);
lean_dec(v___y_2647_);
lean_dec(v_stx_2557_);
v_a_2668_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2670_ = v___x_2667_;
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2667_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2673_; 
if (v_isShared_2671_ == 0)
{
v___x_2673_ = v___x_2670_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_a_2668_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
}
v___jp_2676_:
{
lean_object* v___x_2685_; 
v___x_2685_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__14_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__14_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__14_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___y_2646_ = v___y_2677_;
v___y_2647_ = v___y_2680_;
v___y_2648_ = v___y_2681_;
v___y_2649_ = v___y_2682_;
v___y_2650_ = v___y_2683_;
v___y_2651_ = v___y_2684_;
v_hint_2652_ = v___x_2685_;
v___y_2653_ = v___y_2679_;
v___y_2654_ = v___y_2678_;
goto v___jp_2645_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2____boxed(lean_object* v___x_3052_, lean_object* v___x_3053_, lean_object* v___f_3054_, lean_object* v___x_3055_, lean_object* v___x_3056_, lean_object* v___x_3057_, lean_object* v_a_3058_, lean_object* v_declName_3059_, lean_object* v_stx_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_){
_start:
{
uint8_t v___x_48074__boxed_3064_; lean_object* v_res_3065_; 
v___x_48074__boxed_3064_ = lean_unbox(v___x_3055_);
v_res_3065_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(v___x_3052_, v___x_3053_, v___f_3054_, v___x_48074__boxed_3064_, v___x_3056_, v___x_3057_, v_a_3058_, v_declName_3059_, v_stx_3060_, v___y_3061_, v___y_3062_);
lean_dec(v___y_3062_);
lean_dec_ref(v___y_3061_);
lean_dec_ref(v_a_3058_);
return v_res_3065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3083_; lean_object* v___f_3084_; lean_object* v___f_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; uint8_t v___x_3090_; lean_object* v___x_3091_; 
v___f_3083_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___f_3084_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___f_3085_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_3086_ = lean_box(1);
v___x_3087_ = ((lean_object*)(l_Lean_Linter_instInhabitedDeprecationEntry_default));
v___x_3088_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_));
v___x_3089_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_3090_ = 0;
v___x_3091_ = l_Lean_registerParametricAttributeExt___redArg(v___x_3089_, v___x_3090_, v___f_3083_, v___x_3090_);
if (lean_obj_tag(v___x_3091_) == 0)
{
lean_object* v_a_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___f_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; 
v_a_3092_ = lean_ctor_get(v___x_3091_, 0);
lean_inc_n(v_a_3092_, 2);
lean_dec_ref_known(v___x_3091_, 1);
v___x_3093_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_));
v___x_3094_ = lean_box(v___x_3090_);
v___f_3095_ = lean_alloc_closure((void*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2____boxed), 12, 7);
lean_closure_set(v___f_3095_, 0, v___x_3088_);
lean_closure_set(v___f_3095_, 1, v___x_3093_);
lean_closure_set(v___f_3095_, 2, v___f_3084_);
lean_closure_set(v___f_3095_, 3, v___x_3094_);
lean_closure_set(v___f_3095_, 4, v___x_3086_);
lean_closure_set(v___f_3095_, 5, v___x_3087_);
lean_closure_set(v___f_3095_, 6, v_a_3092_);
v___x_3096_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_3097_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3097_, 0, v___x_3096_);
lean_ctor_set(v___x_3097_, 1, v___f_3095_);
lean_ctor_set(v___x_3097_, 2, v___f_3085_);
lean_ctor_set(v___x_3097_, 3, v___f_3083_);
lean_ctor_set_uint8(v___x_3097_, sizeof(void*)*4, v___x_3090_);
v___x_3098_ = l_Lean_registerParametricAttributeForExt___redArg(v___x_3097_, v_a_3092_);
return v___x_3098_;
}
else
{
lean_object* v_a_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3106_; 
v_a_3099_ = lean_ctor_get(v___x_3091_, 0);
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3101_ = v___x_3091_;
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_a_3099_);
lean_dec(v___x_3091_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3104_; 
if (v_isShared_3102_ == 0)
{
v___x_3104_ = v___x_3101_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_a_3099_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2____boxed(lean_object* v_a_3107_){
_start:
{
lean_object* v_res_3108_; 
v_res_3108_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_();
return v_res_3108_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_3109_, lean_object* v_msg_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_){
_start:
{
lean_object* v___x_3114_; 
v___x_3114_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0___redArg(v_msg_3110_, v___y_3111_, v___y_3112_);
return v___x_3114_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_3115_, lean_object* v_msg_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_){
_start:
{
lean_object* v_res_3120_; 
v_res_3120_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0(v_00_u03b1_3115_, v_msg_3116_, v___y_3117_, v___y_3118_);
lean_dec(v___y_3118_);
lean_dec_ref(v___y_3117_);
return v_res_3120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__3_spec__8(lean_object* v_o_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_){
_start:
{
lean_object* v___x_3125_; 
v___x_3125_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__3_spec__8___redArg(v_o_3121_, v___y_3123_);
return v___x_3125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__3_spec__8___boxed(lean_object* v_o_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_){
_start:
{
lean_object* v_res_3130_; 
v_res_3130_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__3_spec__8(v_o_3126_, v___y_3127_, v___y_3128_);
lean_dec(v___y_3128_);
lean_dec_ref(v___y_3127_);
return v_res_3130_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__4_spec__10(lean_object* v_00_u03b2_3131_){
_start:
{
lean_object* v___x_3132_; 
v___x_3132_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
return v___x_3132_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__4___redArg(){
_start:
{
lean_object* v___x_3134_; 
v___x_3134_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
return v___x_3134_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__4___redArg___boxed(lean_object* v___dummy_3135_){
_start:
{
lean_object* v_res_3136_; 
v_res_3136_ = l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__4___redArg();
return v_res_3136_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__4(lean_object* v_00_u03b2_3137_){
_start:
{
lean_object* v___x_3138_; 
v___x_3138_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
return v___x_3138_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__6(lean_object* v_00_u03b2_3139_, lean_object* v_m_3140_, lean_object* v_a_3141_){
_start:
{
lean_object* v___x_3142_; 
v___x_3142_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__6___redArg(v_m_3140_, v_a_3141_);
return v___x_3142_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__6___boxed(lean_object* v_00_u03b2_3143_, lean_object* v_m_3144_, lean_object* v_a_3145_){
_start:
{
lean_object* v_res_3146_; 
v_res_3146_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__6(v_00_u03b2_3143_, v_m_3144_, v_a_3145_);
lean_dec(v_a_3145_);
lean_dec_ref(v_m_3144_);
return v_res_3146_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8(lean_object* v_00_u03b2_3147_, lean_object* v_x_3148_, lean_object* v_x_3149_){
_start:
{
uint8_t v___x_3150_; 
v___x_3150_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg(v_x_3148_, v_x_3149_);
return v___x_3150_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_3151_, lean_object* v_x_3152_, lean_object* v_x_3153_){
_start:
{
uint8_t v_res_3154_; lean_object* v_r_3155_; 
v_res_3154_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8(v_00_u03b2_3151_, v_x_3152_, v_x_3153_);
lean_dec_ref(v_x_3153_);
lean_dec_ref(v_x_3152_);
v_r_3155_ = lean_box(v_res_3154_);
return v_r_3155_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__6_spec__12(lean_object* v_00_u03b2_3156_, lean_object* v_a_3157_, lean_object* v_x_3158_){
_start:
{
lean_object* v___x_3159_; 
v___x_3159_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg(v_a_3157_, v_x_3158_);
return v___x_3159_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__6_spec__12___boxed(lean_object* v_00_u03b2_3160_, lean_object* v_a_3161_, lean_object* v_x_3162_){
_start:
{
lean_object* v_res_3163_; 
v_res_3163_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__6_spec__12(v_00_u03b2_3160_, v_a_3161_, v_x_3162_);
lean_dec(v_x_3162_);
lean_dec(v_a_3161_);
return v_res_3163_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__19(lean_object* v_00_u03b4_3164_, lean_object* v_t_3165_, lean_object* v_k_3166_){
_start:
{
lean_object* v___x_3167_; 
v___x_3167_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__19___redArg(v_t_3165_, v_k_3166_);
return v___x_3167_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__19___boxed(lean_object* v_00_u03b4_3168_, lean_object* v_t_3169_, lean_object* v_k_3170_){
_start:
{
lean_object* v_res_3171_; 
v_res_3171_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__19(v_00_u03b4_3168_, v_t_3169_, v_k_3170_);
lean_dec(v_k_3170_);
lean_dec(v_t_3169_);
return v_res_3171_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14(lean_object* v_00_u03b2_3172_, lean_object* v_x_3173_, size_t v_x_3174_, lean_object* v_x_3175_){
_start:
{
uint8_t v___x_3176_; 
v___x_3176_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14___redArg(v_x_3173_, v_x_3174_, v_x_3175_);
return v___x_3176_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14___boxed(lean_object* v_00_u03b2_3177_, lean_object* v_x_3178_, lean_object* v_x_3179_, lean_object* v_x_3180_){
_start:
{
size_t v_x_49337__boxed_3181_; uint8_t v_res_3182_; lean_object* v_r_3183_; 
v_x_49337__boxed_3181_ = lean_unbox_usize(v_x_3179_);
lean_dec(v_x_3179_);
v_res_3182_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14(v_00_u03b2_3177_, v_x_3178_, v_x_49337__boxed_3181_, v_x_3180_);
lean_dec_ref(v_x_3180_);
lean_dec_ref(v_x_3178_);
v_r_3183_ = lean_box(v_res_3182_);
return v_r_3183_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22(lean_object* v_givenName_3184_, lean_object* v_auxDeclToFullName_3185_, lean_object* v___x_3186_, lean_object* v_givenNameView_3187_, lean_object* v_as_3188_, lean_object* v_i_3189_, lean_object* v_a_3190_){
_start:
{
lean_object* v___x_3191_; 
v___x_3191_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22___redArg(v_givenName_3184_, v_auxDeclToFullName_3185_, v___x_3186_, v_givenNameView_3187_, v_as_3188_, v_i_3189_);
return v___x_3191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22___boxed(lean_object* v_givenName_3192_, lean_object* v_auxDeclToFullName_3193_, lean_object* v___x_3194_, lean_object* v_givenNameView_3195_, lean_object* v_as_3196_, lean_object* v_i_3197_, lean_object* v_a_3198_){
_start:
{
lean_object* v_res_3199_; 
v_res_3199_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22(v_givenName_3192_, v_auxDeclToFullName_3193_, v___x_3194_, v_givenNameView_3195_, v_as_3196_, v_i_3197_, v_a_3198_);
lean_dec_ref(v_as_3196_);
lean_dec(v_auxDeclToFullName_3193_);
lean_dec(v_givenName_3192_);
return v_res_3199_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__25(lean_object* v_localDecl_x3f_3200_, lean_object* v_givenName_3201_, lean_object* v_as_3202_, lean_object* v_i_3203_, lean_object* v_a_3204_){
_start:
{
lean_object* v___x_3205_; 
v___x_3205_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__25___redArg(v_localDecl_x3f_3200_, v_givenName_3201_, v_as_3202_, v_i_3203_);
return v___x_3205_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__25___boxed(lean_object* v_localDecl_x3f_3206_, lean_object* v_givenName_3207_, lean_object* v_as_3208_, lean_object* v_i_3209_, lean_object* v_a_3210_){
_start:
{
lean_object* v_res_3211_; 
v_res_3211_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__25(v_localDecl_x3f_3206_, v_givenName_3207_, v_as_3208_, v_i_3209_, v_a_3210_);
lean_dec_ref(v_as_3208_);
lean_dec(v_givenName_3207_);
lean_dec(v_localDecl_x3f_3206_);
return v_res_3211_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24_spec__32(lean_object* v_n_u2080_3212_, lean_object* v_filter_3213_, lean_object* v_view_x3f_3214_, lean_object* v_inst_3215_, lean_object* v_R_3216_, lean_object* v_a_3217_, lean_object* v_b_3218_, lean_object* v_c_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_){
_start:
{
lean_object* v___x_3225_; 
v___x_3225_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24_spec__32___redArg(v_n_u2080_3212_, v_filter_3213_, v_view_x3f_3214_, v_a_3217_, v_b_3218_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_);
return v___x_3225_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24_spec__32___boxed(lean_object* v_n_u2080_3226_, lean_object* v_filter_3227_, lean_object* v_view_x3f_3228_, lean_object* v_inst_3229_, lean_object* v_R_3230_, lean_object* v_a_3231_, lean_object* v_b_3232_, lean_object* v_c_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_){
_start:
{
lean_object* v_res_3239_; 
v_res_3239_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24_spec__32(v_n_u2080_3226_, v_filter_3227_, v_view_x3f_3228_, v_inst_3229_, v_R_3230_, v_a_3231_, v_b_3232_, v_c_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
lean_dec(v___y_3237_);
lean_dec_ref(v___y_3236_);
lean_dec(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec(v_n_u2080_3226_);
return v_res_3239_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14_spec__19(lean_object* v_00_u03b2_3240_, lean_object* v_keys_3241_, lean_object* v_vals_3242_, lean_object* v_heq_3243_, lean_object* v_i_3244_, lean_object* v_k_3245_){
_start:
{
uint8_t v___x_3246_; 
v___x_3246_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14_spec__19___redArg(v_keys_3241_, v_i_3244_, v_k_3245_);
return v___x_3246_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14_spec__19___boxed(lean_object* v_00_u03b2_3247_, lean_object* v_keys_3248_, lean_object* v_vals_3249_, lean_object* v_heq_3250_, lean_object* v_i_3251_, lean_object* v_k_3252_){
_start:
{
uint8_t v_res_3253_; lean_object* v_r_3254_; 
v_res_3253_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14_spec__19(v_00_u03b2_3247_, v_keys_3248_, v_vals_3249_, v_heq_3250_, v_i_3251_, v_k_3252_);
lean_dec_ref(v_k_3252_);
lean_dec_ref(v_vals_3249_);
lean_dec_ref(v_keys_3248_);
v_r_3254_ = lean_box(v_res_3253_);
return v_r_3254_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23_spec__26(lean_object* v_givenName_3255_, lean_object* v_auxDeclToFullName_3256_, lean_object* v___x_3257_, lean_object* v_givenNameView_3258_, lean_object* v_as_3259_, lean_object* v_i_3260_, lean_object* v_a_3261_){
_start:
{
lean_object* v___x_3262_; 
v___x_3262_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23_spec__26___redArg(v_givenName_3255_, v_auxDeclToFullName_3256_, v___x_3257_, v_givenNameView_3258_, v_as_3259_, v_i_3260_);
return v___x_3262_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23_spec__26___boxed(lean_object* v_givenName_3263_, lean_object* v_auxDeclToFullName_3264_, lean_object* v___x_3265_, lean_object* v_givenNameView_3266_, lean_object* v_as_3267_, lean_object* v_i_3268_, lean_object* v_a_3269_){
_start:
{
lean_object* v_res_3270_; 
v_res_3270_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23_spec__26(v_givenName_3263_, v_auxDeclToFullName_3264_, v___x_3265_, v_givenNameView_3266_, v_as_3267_, v_i_3268_, v_a_3269_);
lean_dec_ref(v_as_3267_);
lean_dec(v_auxDeclToFullName_3264_);
lean_dec(v_givenName_3263_);
return v_res_3270_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26_spec__30(lean_object* v_localDecl_x3f_3271_, lean_object* v_givenName_3272_, lean_object* v_as_3273_, lean_object* v_i_3274_, lean_object* v_a_3275_){
_start:
{
lean_object* v___x_3276_; 
v___x_3276_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26_spec__30___redArg(v_localDecl_x3f_3271_, v_givenName_3272_, v_as_3273_, v_i_3274_);
return v___x_3276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26_spec__30___boxed(lean_object* v_localDecl_x3f_3277_, lean_object* v_givenName_3278_, lean_object* v_as_3279_, lean_object* v_i_3280_, lean_object* v_a_3281_){
_start:
{
lean_object* v_res_3282_; 
v_res_3282_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26_spec__30(v_localDecl_x3f_3277_, v_givenName_3278_, v_as_3279_, v_i_3280_, v_a_3281_);
lean_dec_ref(v_as_3279_);
lean_dec(v_givenName_3278_);
lean_dec(v_localDecl_x3f_3277_);
return v_res_3282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__39(lean_object* v_opt_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_){
_start:
{
lean_object* v___x_3289_; 
v___x_3289_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__39___redArg(v_opt_3283_, v___y_3286_);
return v___x_3289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__39___boxed(lean_object* v_opt_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_){
_start:
{
lean_object* v_res_3296_; 
v_res_3296_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__39(v_opt_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_);
lean_dec(v___y_3294_);
lean_dec_ref(v___y_3293_);
lean_dec(v___y_3292_);
lean_dec_ref(v___y_3291_);
lean_dec_ref(v_opt_3290_);
return v_res_3296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__45(lean_object* v_opt_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_){
_start:
{
lean_object* v___x_3303_; 
v___x_3303_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__45___redArg(v_opt_3297_, v___y_3300_);
return v___x_3303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__45___boxed(lean_object* v_opt_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_){
_start:
{
lean_object* v_res_3310_; 
v_res_3310_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__45(v_opt_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_);
lean_dec(v___y_3308_);
lean_dec_ref(v___y_3307_);
lean_dec(v___y_3306_);
lean_dec_ref(v___y_3305_);
lean_dec_ref(v_opt_3304_);
return v_res_3310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___redArg___lam__0(lean_object* v_declName_3311_, lean_object* v_entry_3312_, lean_object* v_inst_3313_, lean_object* v_inst_3314_, lean_object* v_inst_3315_, lean_object* v_env_3316_){
_start:
{
lean_object* v___x_3317_; lean_object* v___x_3318_; 
v___x_3317_ = l_Lean_Linter_deprecatedAttr;
v___x_3318_ = l_Lean_ParametricAttribute_setParam___redArg(v___x_3317_, v_env_3316_, v_declName_3311_, v_entry_3312_);
if (lean_obj_tag(v___x_3318_) == 0)
{
lean_object* v_a_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3328_; 
lean_dec_ref(v_inst_3315_);
v_a_3319_ = lean_ctor_get(v___x_3318_, 0);
v_isSharedCheck_3328_ = !lean_is_exclusive(v___x_3318_);
if (v_isSharedCheck_3328_ == 0)
{
v___x_3321_ = v___x_3318_;
v_isShared_3322_ = v_isSharedCheck_3328_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_a_3319_);
lean_dec(v___x_3318_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3328_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
lean_object* v___x_3324_; 
if (v_isShared_3322_ == 0)
{
lean_ctor_set_tag(v___x_3321_, 3);
v___x_3324_ = v___x_3321_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3327_; 
v_reuseFailAlloc_3327_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3327_, 0, v_a_3319_);
v___x_3324_ = v_reuseFailAlloc_3327_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
lean_object* v___x_3325_; lean_object* v___x_3326_; 
v___x_3325_ = l_Lean_MessageData_ofFormat(v___x_3324_);
v___x_3326_ = l_Lean_throwError___redArg(v_inst_3313_, v_inst_3314_, v___x_3325_);
return v___x_3326_;
}
}
}
else
{
lean_object* v_a_3329_; lean_object* v___x_3330_; 
lean_dec_ref(v_inst_3314_);
lean_dec_ref(v_inst_3313_);
v_a_3329_ = lean_ctor_get(v___x_3318_, 0);
lean_inc(v_a_3329_);
lean_dec_ref_known(v___x_3318_, 1);
v___x_3330_ = l_Lean_setEnv___redArg(v_inst_3315_, v_a_3329_);
return v___x_3330_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___redArg(lean_object* v_inst_3331_, lean_object* v_inst_3332_, lean_object* v_inst_3333_, lean_object* v_declName_3334_, lean_object* v_entry_3335_){
_start:
{
lean_object* v_toBind_3336_; lean_object* v_getEnv_3337_; lean_object* v___f_3338_; lean_object* v___x_3339_; 
v_toBind_3336_ = lean_ctor_get(v_inst_3331_, 1);
lean_inc(v_toBind_3336_);
v_getEnv_3337_ = lean_ctor_get(v_inst_3332_, 0);
lean_inc(v_getEnv_3337_);
v___f_3338_ = lean_alloc_closure((void*)(l_Lean_Linter_setDeprecated___redArg___lam__0), 6, 5);
lean_closure_set(v___f_3338_, 0, v_declName_3334_);
lean_closure_set(v___f_3338_, 1, v_entry_3335_);
lean_closure_set(v___f_3338_, 2, v_inst_3331_);
lean_closure_set(v___f_3338_, 3, v_inst_3333_);
lean_closure_set(v___f_3338_, 4, v_inst_3332_);
v___x_3339_ = lean_apply_4(v_toBind_3336_, lean_box(0), lean_box(0), v_getEnv_3337_, v___f_3338_);
return v___x_3339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated(lean_object* v_m_3340_, lean_object* v_inst_3341_, lean_object* v_inst_3342_, lean_object* v_inst_3343_, lean_object* v_declName_3344_, lean_object* v_entry_3345_){
_start:
{
lean_object* v___x_3346_; 
v___x_3346_ = l_Lean_Linter_setDeprecated___redArg(v_inst_3341_, v_inst_3342_, v_inst_3343_, v_declName_3344_, v_entry_3345_);
return v___x_3346_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_isDeprecated(lean_object* v_env_3347_, lean_object* v_declName_3348_){
_start:
{
lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; 
v___x_3349_ = ((lean_object*)(l_Lean_Linter_instInhabitedDeprecationEntry_default));
v___x_3350_ = l_Lean_Linter_deprecatedAttr;
v___x_3351_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_3349_, v___x_3350_, v_env_3347_, v_declName_3348_);
if (lean_obj_tag(v___x_3351_) == 0)
{
uint8_t v___x_3352_; 
v___x_3352_ = 0;
return v___x_3352_;
}
else
{
uint8_t v___x_3353_; 
lean_dec_ref_known(v___x_3351_, 1);
v___x_3353_ = 1;
return v___x_3353_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_isDeprecated___boxed(lean_object* v_env_3354_, lean_object* v_declName_3355_){
_start:
{
uint8_t v_res_3356_; lean_object* v_r_3357_; 
v_res_3356_ = l_Lean_Linter_isDeprecated(v_env_3354_, v_declName_3355_);
v_r_3357_ = lean_box(v_res_3356_);
return v_r_3357_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_isDeprecationWarning___lam__0(lean_object* v_x_3358_){
_start:
{
lean_object* v___x_3359_; uint8_t v___x_3360_; 
v___x_3359_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_3360_ = lean_name_eq(v_x_3358_, v___x_3359_);
return v___x_3360_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_isDeprecationWarning___lam__0___boxed(lean_object* v_x_3361_){
_start:
{
uint8_t v_res_3362_; lean_object* v_r_3363_; 
v_res_3362_ = l_Lean_MessageData_isDeprecationWarning___lam__0(v_x_3361_);
lean_dec(v_x_3361_);
v_r_3363_ = lean_box(v_res_3362_);
return v_r_3363_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_isDeprecationWarning(lean_object* v_msg_3365_){
_start:
{
lean_object* v___f_3366_; uint8_t v___x_3367_; 
v___f_3366_ = ((lean_object*)(l_Lean_MessageData_isDeprecationWarning___closed__0));
v___x_3367_ = l_Lean_MessageData_hasTag(v___f_3366_, v_msg_3365_);
return v___x_3367_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_isDeprecationWarning___boxed(lean_object* v_msg_3368_){
_start:
{
uint8_t v_res_3369_; lean_object* v_r_3370_; 
v_res_3369_ = l_Lean_MessageData_isDeprecationWarning(v_msg_3368_);
v_r_3370_ = lean_box(v_res_3369_);
return v_r_3370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getDeprecatedNewName(lean_object* v_env_3371_, lean_object* v_declName_3372_){
_start:
{
lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; 
v___x_3373_ = ((lean_object*)(l_Lean_Linter_instInhabitedDeprecationEntry_default));
v___x_3374_ = l_Lean_Linter_deprecatedAttr;
v___x_3375_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_3373_, v___x_3374_, v_env_3371_, v_declName_3372_);
if (lean_obj_tag(v___x_3375_) == 0)
{
lean_object* v___x_3376_; 
v___x_3376_ = lean_box(0);
return v___x_3376_;
}
else
{
lean_object* v_val_3377_; lean_object* v_newName_x3f_3378_; 
v_val_3377_ = lean_ctor_get(v___x_3375_, 0);
lean_inc(v_val_3377_);
lean_dec_ref_known(v___x_3375_, 1);
v_newName_x3f_3378_ = lean_ctor_get(v_val_3377_, 0);
lean_inc(v_newName_x3f_3378_);
lean_dec(v_val_3377_);
return v_newName_x3f_3378_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_DeprecationHint_ctorIdx___impl(lean_object* v_x_3379_){
_start:
{
lean_object* v___x_3380_; 
v___x_3380_ = lean_obj_tag_nat(v_x_3379_);
return v___x_3380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_DeprecationHint_ctorIdx___impl___boxed(lean_object* v_x_3381_){
_start:
{
lean_object* v_res_3382_; 
v_res_3382_ = l_Lean_Linter_DeprecationHint_ctorIdx___impl(v_x_3381_);
lean_dec(v_x_3381_);
return v_res_3382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_DeprecationHint_ctorElim___redArg(lean_object* v_t_3383_, lean_object* v_k_3384_){
_start:
{
if (lean_obj_tag(v_t_3383_) == 2)
{
lean_object* v_mk_3385_; lean_object* v___x_3386_; 
v_mk_3385_ = lean_ctor_get(v_t_3383_, 0);
lean_inc_ref(v_mk_3385_);
lean_dec_ref_known(v_t_3383_, 1);
v___x_3386_ = lean_apply_1(v_k_3384_, v_mk_3385_);
return v___x_3386_;
}
else
{
lean_dec(v_t_3383_);
return v_k_3384_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_DeprecationHint_ctorElim(lean_object* v_motive_3387_, lean_object* v_ctorIdx_3388_, lean_object* v_t_3389_, lean_object* v_h_3390_, lean_object* v_k_3391_){
_start:
{
lean_object* v___x_3392_; 
v___x_3392_ = l_Lean_Linter_DeprecationHint_ctorElim___redArg(v_t_3389_, v_k_3391_);
return v___x_3392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_DeprecationHint_ctorElim___boxed(lean_object* v_motive_3393_, lean_object* v_ctorIdx_3394_, lean_object* v_t_3395_, lean_object* v_h_3396_, lean_object* v_k_3397_){
_start:
{
lean_object* v_res_3398_; 
v_res_3398_ = l_Lean_Linter_DeprecationHint_ctorElim(v_motive_3393_, v_ctorIdx_3394_, v_t_3395_, v_h_3396_, v_k_3397_);
lean_dec(v_ctorIdx_3394_);
return v_res_3398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_DeprecationHint_none_elim___redArg(lean_object* v_t_3399_, lean_object* v_none_3400_){
_start:
{
lean_object* v___x_3401_; 
v___x_3401_ = l_Lean_Linter_DeprecationHint_ctorElim___redArg(v_t_3399_, v_none_3400_);
return v___x_3401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_DeprecationHint_none_elim(lean_object* v_motive_3402_, lean_object* v_t_3403_, lean_object* v_h_3404_, lean_object* v_none_3405_){
_start:
{
lean_object* v___x_3406_; 
v___x_3406_ = l_Lean_Linter_DeprecationHint_ctorElim___redArg(v_t_3403_, v_none_3405_);
return v___x_3406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_DeprecationHint_ident_elim___redArg(lean_object* v_t_3407_, lean_object* v_ident_3408_){
_start:
{
lean_object* v___x_3409_; 
v___x_3409_ = l_Lean_Linter_DeprecationHint_ctorElim___redArg(v_t_3407_, v_ident_3408_);
return v___x_3409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_DeprecationHint_ident_elim(lean_object* v_motive_3410_, lean_object* v_t_3411_, lean_object* v_h_3412_, lean_object* v_ident_3413_){
_start:
{
lean_object* v___x_3414_; 
v___x_3414_ = l_Lean_Linter_DeprecationHint_ctorElim___redArg(v_t_3411_, v_ident_3413_);
return v___x_3414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_DeprecationHint_custom_elim___redArg(lean_object* v_t_3415_, lean_object* v_custom_3416_){
_start:
{
lean_object* v___x_3417_; 
v___x_3417_ = l_Lean_Linter_DeprecationHint_ctorElim___redArg(v_t_3415_, v_custom_3416_);
return v___x_3417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_DeprecationHint_custom_elim(lean_object* v_motive_3418_, lean_object* v_t_3419_, lean_object* v_h_3420_, lean_object* v_custom_3421_){
_start:
{
lean_object* v___x_3422_; 
v___x_3422_ = l_Lean_Linter_DeprecationHint_ctorElim___redArg(v_t_3419_, v_custom_3421_);
return v___x_3422_;
}
}
static lean_object* _init_l_Lean_Linter_mkReplacementHint___redArg___closed__1(void){
_start:
{
lean_object* v___x_3424_; lean_object* v___x_3425_; 
v___x_3424_ = ((lean_object*)(l_Lean_Linter_mkReplacementHint___redArg___closed__0));
v___x_3425_ = l_Lean_stringToMessageData(v___x_3424_);
return v___x_3425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_mkReplacementHint___redArg(lean_object* v_ref_3426_, lean_object* v_replacement_3427_, lean_object* v_a_3428_, lean_object* v_a_3429_){
_start:
{
uint8_t v___x_3431_; lean_object* v___x_3432_; 
v___x_3431_ = 1;
v___x_3432_ = l_Lean_Syntax_getRange_x3f(v_ref_3426_, v___x_3431_);
if (lean_obj_tag(v___x_3432_) == 0)
{
lean_object* v___x_3433_; lean_object* v___x_3434_; 
lean_dec_ref(v_replacement_3427_);
lean_dec(v_ref_3426_);
v___x_3433_ = l_Lean_MessageData_nil;
v___x_3434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3434_, 0, v___x_3433_);
return v___x_3434_;
}
else
{
lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3452_; 
v_isSharedCheck_3452_ = !lean_is_exclusive(v___x_3432_);
if (v_isSharedCheck_3452_ == 0)
{
lean_object* v_unused_3453_; 
v_unused_3453_ = lean_ctor_get(v___x_3432_, 0);
lean_dec(v_unused_3453_);
v___x_3436_ = v___x_3432_;
v_isShared_3437_ = v_isSharedCheck_3452_;
goto v_resetjp_3435_;
}
else
{
lean_dec(v___x_3432_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3452_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; uint8_t v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3448_; 
v___x_3438_ = lean_obj_once(&l_Lean_Linter_mkReplacementHint___redArg___closed__1, &l_Lean_Linter_mkReplacementHint___redArg___closed__1_once, _init_l_Lean_Linter_mkReplacementHint___redArg___closed__1);
v___x_3439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3439_, 0, v_replacement_3427_);
v___x_3440_ = lean_box(0);
v___x_3441_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3441_, 0, v___x_3439_);
lean_ctor_set(v___x_3441_, 1, v___x_3440_);
lean_ctor_set(v___x_3441_, 2, v___x_3440_);
lean_ctor_set(v___x_3441_, 3, v___x_3440_);
lean_ctor_set(v___x_3441_, 4, v___x_3440_);
lean_ctor_set(v___x_3441_, 5, v___x_3440_);
v___x_3442_ = 0;
v___x_3443_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3443_, 0, v___x_3441_);
lean_ctor_set(v___x_3443_, 1, v___x_3440_);
lean_ctor_set(v___x_3443_, 2, v___x_3440_);
lean_ctor_set_uint8(v___x_3443_, sizeof(void*)*3, v___x_3442_);
v___x_3444_ = lean_unsigned_to_nat(1u);
v___x_3445_ = lean_mk_empty_array_with_capacity(v___x_3444_);
v___x_3446_ = lean_array_push(v___x_3445_, v___x_3443_);
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 0, v_ref_3426_);
v___x_3448_ = v___x_3436_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v_ref_3426_);
v___x_3448_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
uint8_t v___x_3449_; lean_object* v___x_3450_; 
v___x_3449_ = 0;
v___x_3450_ = l_Lean_MessageData_hint(v___x_3438_, v___x_3446_, v___x_3448_, v___x_3440_, v___x_3449_, v_a_3428_, v_a_3429_);
lean_dec_ref(v___x_3446_);
return v___x_3450_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_mkReplacementHint___redArg___boxed(lean_object* v_ref_3454_, lean_object* v_replacement_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_){
_start:
{
lean_object* v_res_3459_; 
v_res_3459_ = l_Lean_Linter_mkReplacementHint___redArg(v_ref_3454_, v_replacement_3455_, v_a_3456_, v_a_3457_);
lean_dec(v_a_3457_);
lean_dec_ref(v_a_3456_);
return v_res_3459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_mkReplacementHint(lean_object* v_ref_3460_, lean_object* v_replacement_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_){
_start:
{
lean_object* v___x_3467_; 
v___x_3467_ = l_Lean_Linter_mkReplacementHint___redArg(v_ref_3460_, v_replacement_3461_, v_a_3464_, v_a_3465_);
return v___x_3467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_mkReplacementHint___boxed(lean_object* v_ref_3468_, lean_object* v_replacement_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_){
_start:
{
lean_object* v_res_3475_; 
v_res_3475_ = l_Lean_Linter_mkReplacementHint(v_ref_3468_, v_replacement_3469_, v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_);
lean_dec(v_a_3473_);
lean_dec_ref(v_a_3472_);
lean_dec(v_a_3471_);
lean_dec_ref(v_a_3470_);
return v_res_3475_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00List_beq___at___00Lean_Linter_mkIdentHint_spec__0_spec__0(lean_object* v_x_3476_, lean_object* v_x_3477_){
_start:
{
if (lean_obj_tag(v_x_3476_) == 0)
{
if (lean_obj_tag(v_x_3477_) == 0)
{
uint8_t v___x_3478_; 
v___x_3478_ = 1;
return v___x_3478_;
}
else
{
uint8_t v___x_3479_; 
v___x_3479_ = 0;
return v___x_3479_;
}
}
else
{
if (lean_obj_tag(v_x_3477_) == 0)
{
uint8_t v___x_3480_; 
v___x_3480_ = 0;
return v___x_3480_;
}
else
{
lean_object* v_head_3481_; lean_object* v_tail_3482_; lean_object* v_head_3483_; lean_object* v_tail_3484_; uint8_t v___x_3485_; 
v_head_3481_ = lean_ctor_get(v_x_3476_, 0);
v_tail_3482_ = lean_ctor_get(v_x_3476_, 1);
v_head_3483_ = lean_ctor_get(v_x_3477_, 0);
v_tail_3484_ = lean_ctor_get(v_x_3477_, 1);
v___x_3485_ = lean_string_dec_eq(v_head_3481_, v_head_3483_);
if (v___x_3485_ == 0)
{
return v___x_3485_;
}
else
{
v_x_3476_ = v_tail_3482_;
v_x_3477_ = v_tail_3484_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00List_beq___at___00Lean_Linter_mkIdentHint_spec__0_spec__0___boxed(lean_object* v_x_3487_, lean_object* v_x_3488_){
_start:
{
uint8_t v_res_3489_; lean_object* v_r_3490_; 
v_res_3489_ = l_List_beq___at___00List_beq___at___00Lean_Linter_mkIdentHint_spec__0_spec__0(v_x_3487_, v_x_3488_);
lean_dec(v_x_3488_);
lean_dec(v_x_3487_);
v_r_3490_ = lean_box(v_res_3489_);
return v_r_3490_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Linter_mkIdentHint_spec__0(lean_object* v_x_3491_, lean_object* v_x_3492_){
_start:
{
if (lean_obj_tag(v_x_3491_) == 0)
{
if (lean_obj_tag(v_x_3492_) == 0)
{
uint8_t v___x_3493_; 
v___x_3493_ = 1;
return v___x_3493_;
}
else
{
uint8_t v___x_3494_; 
v___x_3494_ = 0;
return v___x_3494_;
}
}
else
{
if (lean_obj_tag(v_x_3492_) == 0)
{
uint8_t v___x_3495_; 
v___x_3495_ = 0;
return v___x_3495_;
}
else
{
lean_object* v_head_3496_; lean_object* v_head_3497_; lean_object* v_tail_3498_; lean_object* v_tail_3499_; lean_object* v_fst_3500_; lean_object* v_snd_3501_; lean_object* v_fst_3502_; lean_object* v_snd_3503_; uint8_t v___x_3504_; 
v_head_3496_ = lean_ctor_get(v_x_3491_, 0);
v_head_3497_ = lean_ctor_get(v_x_3492_, 0);
v_tail_3498_ = lean_ctor_get(v_x_3491_, 1);
v_tail_3499_ = lean_ctor_get(v_x_3492_, 1);
v_fst_3500_ = lean_ctor_get(v_head_3496_, 0);
v_snd_3501_ = lean_ctor_get(v_head_3496_, 1);
v_fst_3502_ = lean_ctor_get(v_head_3497_, 0);
v_snd_3503_ = lean_ctor_get(v_head_3497_, 1);
v___x_3504_ = lean_name_eq(v_fst_3500_, v_fst_3502_);
if (v___x_3504_ == 0)
{
return v___x_3504_;
}
else
{
uint8_t v___x_3505_; 
v___x_3505_ = l_List_beq___at___00List_beq___at___00Lean_Linter_mkIdentHint_spec__0_spec__0(v_snd_3501_, v_snd_3503_);
if (v___x_3505_ == 0)
{
return v___x_3505_;
}
else
{
v_x_3491_ = v_tail_3498_;
v_x_3492_ = v_tail_3499_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Linter_mkIdentHint_spec__0___boxed(lean_object* v_x_3507_, lean_object* v_x_3508_){
_start:
{
uint8_t v_res_3509_; lean_object* v_r_3510_; 
v_res_3509_ = l_List_beq___at___00Lean_Linter_mkIdentHint_spec__0(v_x_3507_, v_x_3508_);
lean_dec(v_x_3508_);
lean_dec(v_x_3507_);
v_r_3510_ = lean_box(v_res_3509_);
return v_r_3510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_mkIdentHint(lean_object* v_declName_3511_, lean_object* v_newName_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_){
_start:
{
lean_object* v_ref_3518_; 
v_ref_3518_ = lean_ctor_get(v_a_3515_, 2);
if (lean_obj_tag(v_ref_3518_) == 3)
{
lean_object* v_val_3519_; uint8_t v___x_3520_; 
v_val_3519_ = lean_ctor_get(v_ref_3518_, 2);
v___x_3520_ = l_Lean_Name_hasMacroScopes(v_val_3519_);
if (v___x_3520_ == 0)
{
uint8_t v___x_3521_; lean_object* v___x_3522_; 
v___x_3521_ = 1;
lean_inc(v_val_3519_);
v___x_3522_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28(v_val_3519_, v___x_3521_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_);
if (lean_obj_tag(v___x_3522_) == 0)
{
lean_object* v_a_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3556_; 
v_a_3523_ = lean_ctor_get(v___x_3522_, 0);
v_isSharedCheck_3556_ = !lean_is_exclusive(v___x_3522_);
if (v_isSharedCheck_3556_ == 0)
{
v___x_3525_ = v___x_3522_;
v_isShared_3526_ = v_isSharedCheck_3556_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_a_3523_);
lean_dec(v___x_3522_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3556_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; uint8_t v___x_3530_; 
v___x_3527_ = lean_box(0);
v___x_3528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3528_, 0, v_declName_3511_);
lean_ctor_set(v___x_3528_, 1, v___x_3527_);
v___x_3529_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3529_, 0, v___x_3528_);
lean_ctor_set(v___x_3529_, 1, v___x_3527_);
v___x_3530_ = l_List_beq___at___00Lean_Linter_mkIdentHint_spec__0(v_a_3523_, v___x_3529_);
lean_dec_ref_known(v___x_3529_, 2);
lean_dec(v_a_3523_);
if (v___x_3530_ == 0)
{
lean_object* v___x_3531_; lean_object* v___x_3533_; 
lean_dec(v_newName_3512_);
v___x_3531_ = l_Lean_MessageData_nil;
if (v_isShared_3526_ == 0)
{
lean_ctor_set(v___x_3525_, 0, v___x_3531_);
v___x_3533_ = v___x_3525_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v___x_3531_);
v___x_3533_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
return v___x_3533_;
}
}
else
{
lean_object* v___x_3535_; 
lean_del_object(v___x_3525_);
v___x_3535_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6(v_newName_3512_, v___x_3520_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_);
if (lean_obj_tag(v___x_3535_) == 0)
{
lean_object* v_a_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3547_; 
v_a_3536_ = lean_ctor_get(v___x_3535_, 0);
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_3535_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3538_ = v___x_3535_;
v_isShared_3539_ = v_isSharedCheck_3547_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_a_3536_);
lean_dec(v___x_3535_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3547_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
if (lean_obj_tag(v_a_3536_) == 1)
{
lean_object* v_val_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; 
lean_del_object(v___x_3538_);
v_val_3540_ = lean_ctor_get(v_a_3536_, 0);
lean_inc(v_val_3540_);
lean_dec_ref_known(v_a_3536_, 1);
v___x_3541_ = l_Lean_Name_toString(v_val_3540_, v___x_3521_);
lean_inc_ref(v_ref_3518_);
v___x_3542_ = l_Lean_Linter_mkReplacementHint___redArg(v_ref_3518_, v___x_3541_, v_a_3515_, v_a_3516_);
return v___x_3542_;
}
else
{
lean_object* v___x_3543_; lean_object* v___x_3545_; 
lean_dec(v_a_3536_);
v___x_3543_ = l_Lean_MessageData_nil;
if (v_isShared_3539_ == 0)
{
lean_ctor_set(v___x_3538_, 0, v___x_3543_);
v___x_3545_ = v___x_3538_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v___x_3543_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
return v___x_3545_;
}
}
}
}
else
{
lean_object* v_a_3548_; lean_object* v___x_3550_; uint8_t v_isShared_3551_; uint8_t v_isSharedCheck_3555_; 
v_a_3548_ = lean_ctor_get(v___x_3535_, 0);
v_isSharedCheck_3555_ = !lean_is_exclusive(v___x_3535_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3550_ = v___x_3535_;
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
else
{
lean_inc(v_a_3548_);
lean_dec(v___x_3535_);
v___x_3550_ = lean_box(0);
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
v_resetjp_3549_:
{
lean_object* v___x_3553_; 
if (v_isShared_3551_ == 0)
{
v___x_3553_ = v___x_3550_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v_a_3548_);
v___x_3553_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
return v___x_3553_;
}
}
}
}
}
}
else
{
lean_object* v_a_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3564_; 
lean_dec(v_newName_3512_);
lean_dec(v_declName_3511_);
v_a_3557_ = lean_ctor_get(v___x_3522_, 0);
v_isSharedCheck_3564_ = !lean_is_exclusive(v___x_3522_);
if (v_isSharedCheck_3564_ == 0)
{
v___x_3559_ = v___x_3522_;
v_isShared_3560_ = v_isSharedCheck_3564_;
goto v_resetjp_3558_;
}
else
{
lean_inc(v_a_3557_);
lean_dec(v___x_3522_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3564_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
lean_object* v___x_3562_; 
if (v_isShared_3560_ == 0)
{
v___x_3562_ = v___x_3559_;
goto v_reusejp_3561_;
}
else
{
lean_object* v_reuseFailAlloc_3563_; 
v_reuseFailAlloc_3563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3563_, 0, v_a_3557_);
v___x_3562_ = v_reuseFailAlloc_3563_;
goto v_reusejp_3561_;
}
v_reusejp_3561_:
{
return v___x_3562_;
}
}
}
}
else
{
lean_object* v___x_3565_; lean_object* v___x_3566_; 
lean_dec(v_newName_3512_);
lean_dec(v_declName_3511_);
v___x_3565_ = l_Lean_MessageData_nil;
v___x_3566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3566_, 0, v___x_3565_);
return v___x_3566_;
}
}
else
{
lean_object* v___x_3567_; lean_object* v___x_3568_; 
lean_dec(v_newName_3512_);
lean_dec(v_declName_3511_);
v___x_3567_ = l_Lean_MessageData_nil;
v___x_3568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3567_);
return v___x_3568_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_mkIdentHint___boxed(lean_object* v_declName_3569_, lean_object* v_newName_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_){
_start:
{
lean_object* v_res_3576_; 
v_res_3576_ = l_Lean_Linter_mkIdentHint(v_declName_3569_, v_newName_3570_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_);
lean_dec(v_a_3574_);
lean_dec_ref(v_a_3573_);
lean_dec(v_a_3572_);
lean_dec_ref(v_a_3571_);
return v_res_3576_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Linter_checkDeprecated_spec__1___redArg(lean_object* v_a_3577_, lean_object* v_b_3578_){
_start:
{
lean_object* v_countdown_3579_; lean_object* v_inner_3580_; lean_object* v___x_3582_; uint8_t v_isShared_3583_; uint8_t v_isSharedCheck_3603_; 
v_countdown_3579_ = lean_ctor_get(v_a_3577_, 0);
v_inner_3580_ = lean_ctor_get(v_a_3577_, 1);
v_isSharedCheck_3603_ = !lean_is_exclusive(v_a_3577_);
if (v_isSharedCheck_3603_ == 0)
{
v___x_3582_ = v_a_3577_;
v_isShared_3583_ = v_isSharedCheck_3603_;
goto v_resetjp_3581_;
}
else
{
lean_inc(v_inner_3580_);
lean_inc(v_countdown_3579_);
lean_dec(v_a_3577_);
v___x_3582_ = lean_box(0);
v_isShared_3583_ = v_isSharedCheck_3603_;
goto v_resetjp_3581_;
}
v_resetjp_3581_:
{
lean_object* v___x_3584_; lean_object* v_it_3586_; lean_object* v_out_3587_; uint8_t v___x_3594_; 
v___x_3584_ = lean_unsigned_to_nat(1u);
v___x_3594_ = lean_nat_dec_eq(v_countdown_3579_, v___x_3584_);
if (v___x_3594_ == 0)
{
switch(lean_obj_tag(v_inner_3580_))
{
case 0:
{
lean_del_object(v___x_3582_);
lean_dec(v_countdown_3579_);
return v_b_3578_;
}
case 1:
{
lean_object* v_pre_3595_; lean_object* v_str_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; 
v_pre_3595_ = lean_ctor_get(v_inner_3580_, 0);
lean_inc(v_pre_3595_);
v_str_3596_ = lean_ctor_get(v_inner_3580_, 1);
lean_inc_ref(v_str_3596_);
lean_dec_ref_known(v_inner_3580_, 2);
v___x_3597_ = lean_box(0);
v___x_3598_ = l_Lean_Name_str___override(v___x_3597_, v_str_3596_);
v_it_3586_ = v_pre_3595_;
v_out_3587_ = v___x_3598_;
goto v___jp_3585_;
}
default: 
{
lean_object* v_pre_3599_; lean_object* v_i_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; 
v_pre_3599_ = lean_ctor_get(v_inner_3580_, 0);
lean_inc(v_pre_3599_);
v_i_3600_ = lean_ctor_get(v_inner_3580_, 1);
lean_inc(v_i_3600_);
lean_dec_ref_known(v_inner_3580_, 2);
v___x_3601_ = lean_box(0);
v___x_3602_ = l_Lean_Name_num___override(v___x_3601_, v_i_3600_);
v_it_3586_ = v_pre_3599_;
v_out_3587_ = v___x_3602_;
goto v___jp_3585_;
}
}
}
else
{
lean_del_object(v___x_3582_);
lean_dec(v_inner_3580_);
lean_dec(v_countdown_3579_);
return v_b_3578_;
}
v___jp_3585_:
{
lean_object* v___x_3588_; lean_object* v___x_3590_; 
v___x_3588_ = lean_nat_sub(v_countdown_3579_, v___x_3584_);
lean_dec(v_countdown_3579_);
if (v_isShared_3583_ == 0)
{
lean_ctor_set(v___x_3582_, 1, v_it_3586_);
lean_ctor_set(v___x_3582_, 0, v___x_3588_);
v___x_3590_ = v___x_3582_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v___x_3588_);
lean_ctor_set(v_reuseFailAlloc_3593_, 1, v_it_3586_);
v___x_3590_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
lean_object* v___x_3591_; 
v___x_3591_ = lean_array_push(v_b_3578_, v_out_3587_);
v_a_3577_ = v___x_3590_;
v_b_3578_ = v___x_3591_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(lean_object* v_o_3604_, lean_object* v___y_3605_){
_start:
{
lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v_env_3609_; lean_object* v___x_3610_; lean_object* v_toEnvExtension_3611_; lean_object* v_asyncMode_3612_; lean_object* v___x_3613_; uint8_t v___x_3614_; lean_object* v___x_3615_; lean_object* v_merged_3616_; lean_object* v___x_3618_; uint8_t v_isShared_3619_; uint8_t v_isSharedCheck_3624_; 
v___x_3607_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_3608_ = lean_st_ref_get(v___y_3605_);
v_env_3609_ = lean_ctor_get(v___x_3608_, 0);
lean_inc_ref(v_env_3609_);
lean_dec(v___x_3608_);
v___x_3610_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_3611_ = lean_ctor_get(v___x_3610_, 0);
v_asyncMode_3612_ = lean_ctor_get(v_toEnvExtension_3611_, 2);
v___x_3613_ = lean_box(0);
v___x_3614_ = 0;
v___x_3615_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3607_, v___x_3610_, v_env_3609_, v_asyncMode_3612_, v___x_3613_, v___x_3614_);
v_merged_3616_ = lean_ctor_get(v___x_3615_, 0);
v_isSharedCheck_3624_ = !lean_is_exclusive(v___x_3615_);
if (v_isSharedCheck_3624_ == 0)
{
lean_object* v_unused_3625_; 
v_unused_3625_ = lean_ctor_get(v___x_3615_, 1);
lean_dec(v_unused_3625_);
v___x_3618_ = v___x_3615_;
v_isShared_3619_ = v_isSharedCheck_3624_;
goto v_resetjp_3617_;
}
else
{
lean_inc(v_merged_3616_);
lean_dec(v___x_3615_);
v___x_3618_ = lean_box(0);
v_isShared_3619_ = v_isSharedCheck_3624_;
goto v_resetjp_3617_;
}
v_resetjp_3617_:
{
lean_object* v___x_3621_; 
if (v_isShared_3619_ == 0)
{
lean_ctor_set(v___x_3618_, 1, v_merged_3616_);
lean_ctor_set(v___x_3618_, 0, v_o_3604_);
v___x_3621_ = v___x_3618_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_o_3604_);
lean_ctor_set(v_reuseFailAlloc_3623_, 1, v_merged_3616_);
v___x_3621_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
lean_object* v___x_3622_; 
v___x_3622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3622_, 0, v___x_3621_);
return v___x_3622_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg___boxed(lean_object* v_o_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_){
_start:
{
lean_object* v_res_3629_; 
v_res_3629_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(v_o_3626_, v___y_3627_);
lean_dec(v___y_3627_);
return v_res_3629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0(lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_){
_start:
{
lean_object* v___x_3635_; lean_object* v___x_3636_; 
v___x_3635_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3632_);
v___x_3636_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(v___x_3635_, v___y_3633_);
return v___x_3636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0___boxed(lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_){
_start:
{
lean_object* v_res_3642_; 
v_res_3642_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0(v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_);
lean_dec(v___y_3640_);
lean_dec_ref(v___y_3639_);
lean_dec(v___y_3638_);
lean_dec_ref(v___y_3637_);
return v_res_3642_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__1(void){
_start:
{
lean_object* v___x_3644_; lean_object* v___x_3645_; 
v___x_3644_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__0));
v___x_3645_ = l_Lean_stringToMessageData(v___x_3644_);
return v___x_3645_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__3(void){
_start:
{
lean_object* v___x_3647_; lean_object* v___x_3648_; 
v___x_3647_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__2));
v___x_3648_ = l_Lean_stringToMessageData(v___x_3647_);
return v___x_3648_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__5(void){
_start:
{
lean_object* v___x_3650_; lean_object* v___x_3651_; 
v___x_3650_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__4));
v___x_3651_ = l_Lean_stringToMessageData(v___x_3650_);
return v___x_3651_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__7(void){
_start:
{
lean_object* v___x_3653_; lean_object* v___x_3654_; 
v___x_3653_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__6));
v___x_3654_ = l_Lean_stringToMessageData(v___x_3653_);
return v___x_3654_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__9(void){
_start:
{
lean_object* v___x_3656_; lean_object* v___x_3657_; 
v___x_3656_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__8));
v___x_3657_ = l_Lean_stringToMessageData(v___x_3656_);
return v___x_3657_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__11(void){
_start:
{
lean_object* v___x_3660_; lean_object* v___x_3661_; 
v___x_3660_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__10));
v___x_3661_ = l_Lean_MessageData_ofFormat(v___x_3660_);
return v___x_3661_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__13(void){
_start:
{
lean_object* v___x_3663_; lean_object* v___x_3664_; 
v___x_3663_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__12));
v___x_3664_ = l_Lean_stringToMessageData(v___x_3663_);
return v___x_3664_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__15(void){
_start:
{
lean_object* v___x_3666_; lean_object* v___x_3667_; 
v___x_3666_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__14));
v___x_3667_ = l_Lean_stringToMessageData(v___x_3666_);
return v___x_3667_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__17(void){
_start:
{
lean_object* v___x_3669_; lean_object* v___x_3670_; 
v___x_3669_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__16));
v___x_3670_ = l_Lean_stringToMessageData(v___x_3669_);
return v___x_3670_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__19(void){
_start:
{
lean_object* v___x_3672_; lean_object* v___x_3673_; 
v___x_3672_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__18));
v___x_3673_ = l_Lean_stringToMessageData(v___x_3672_);
return v___x_3673_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__21(void){
_start:
{
lean_object* v___x_3675_; lean_object* v___x_3676_; 
v___x_3675_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__20));
v___x_3676_ = l_Lean_stringToMessageData(v___x_3675_);
return v___x_3676_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__23(void){
_start:
{
lean_object* v___x_3678_; lean_object* v___x_3679_; 
v___x_3678_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__22));
v___x_3679_ = l_Lean_stringToMessageData(v___x_3678_);
return v___x_3679_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__25(void){
_start:
{
lean_object* v___x_3681_; lean_object* v___x_3682_; 
v___x_3681_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__24));
v___x_3682_ = l_Lean_stringToMessageData(v___x_3681_);
return v___x_3682_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__27(void){
_start:
{
lean_object* v___x_3684_; lean_object* v___x_3685_; 
v___x_3684_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__26));
v___x_3685_ = l_Lean_stringToMessageData(v___x_3684_);
return v___x_3685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkDeprecated(lean_object* v_declName_3686_, lean_object* v_hint_3687_, lean_object* v_a_3688_, lean_object* v_a_3689_, lean_object* v_a_3690_, lean_object* v_a_3691_){
_start:
{
lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v_a_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3892_; 
v___x_3693_ = ((lean_object*)(l_Lean_Linter_instInhabitedDeprecationEntry_default));
v___x_3694_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0(v_a_3688_, v_a_3689_, v_a_3690_, v_a_3691_);
v_a_3695_ = lean_ctor_get(v___x_3694_, 0);
v_isSharedCheck_3892_ = !lean_is_exclusive(v___x_3694_);
if (v_isSharedCheck_3892_ == 0)
{
v___x_3697_ = v___x_3694_;
v_isShared_3698_ = v_isSharedCheck_3892_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_a_3695_);
lean_dec(v___x_3694_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3892_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
lean_object* v___x_3699_; uint8_t v___x_3700_; lean_object* v_extraMsg_3702_; lean_object* v___y_3703_; lean_object* v___y_3704_; lean_object* v___y_3705_; lean_object* v___y_3706_; 
v___x_3699_ = l_Lean_Linter_linter_deprecated;
v___x_3700_ = l_Lean_Linter_getLinterValue(v___x_3699_, v_a_3695_);
lean_dec(v_a_3695_);
if (v___x_3700_ == 0)
{
lean_object* v___x_3716_; lean_object* v___x_3718_; 
lean_dec(v_hint_3687_);
lean_dec(v_declName_3686_);
v___x_3716_ = lean_box(0);
if (v_isShared_3698_ == 0)
{
lean_ctor_set(v___x_3697_, 0, v___x_3716_);
v___x_3718_ = v___x_3697_;
goto v_reusejp_3717_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v___x_3716_);
v___x_3718_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3717_;
}
v_reusejp_3717_:
{
return v___x_3718_;
}
}
else
{
lean_object* v___x_3720_; lean_object* v_env_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; 
v___x_3720_ = lean_st_ref_get(v_a_3691_);
v_env_3721_ = lean_ctor_get(v___x_3720_, 0);
lean_inc_ref(v_env_3721_);
lean_dec(v___x_3720_);
v___x_3722_ = l_Lean_Linter_deprecatedAttr;
lean_inc(v_declName_3686_);
v___x_3723_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_3693_, v___x_3722_, v_env_3721_, v_declName_3686_);
if (lean_obj_tag(v___x_3723_) == 1)
{
lean_object* v_val_3724_; lean_object* v_text_x3f_3725_; 
lean_del_object(v___x_3697_);
v_val_3724_ = lean_ctor_get(v___x_3723_, 0);
lean_inc(v_val_3724_);
lean_dec_ref_known(v___x_3723_, 1);
v_text_x3f_3725_ = lean_ctor_get(v_val_3724_, 1);
if (lean_obj_tag(v_text_x3f_3725_) == 0)
{
lean_object* v_newName_x3f_3726_; 
v_newName_x3f_3726_ = lean_ctor_get(v_val_3724_, 0);
lean_inc(v_newName_x3f_3726_);
lean_dec(v_val_3724_);
if (lean_obj_tag(v_newName_x3f_3726_) == 0)
{
lean_object* v___x_3727_; 
lean_dec(v_hint_3687_);
v___x_3727_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__9);
v_extraMsg_3702_ = v___x_3727_;
v___y_3703_ = v_a_3688_;
v___y_3704_ = v_a_3689_;
v___y_3705_ = v_a_3690_;
v___y_3706_ = v_a_3691_;
goto v___jp_3701_;
}
else
{
lean_object* v_val_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v_env_3735_; lean_object* v___x_3736_; uint8_t v___x_3737_; lean_object* v___x_3738_; 
v_val_3728_ = lean_ctor_get(v_newName_x3f_3726_, 0);
lean_inc_n(v_val_3728_, 2);
lean_dec_ref_known(v_newName_x3f_3726_, 1);
v___x_3729_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__3, &l_Lean_Linter_checkDeprecated___closed__3_once, _init_l_Lean_Linter_checkDeprecated___closed__3);
v___x_3730_ = l_Lean_MessageData_ofConstName(v_val_3728_, v___x_3700_);
lean_inc_ref(v___x_3730_);
v___x_3731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3731_, 0, v___x_3729_);
lean_ctor_set(v___x_3731_, 1, v___x_3730_);
v___x_3732_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__55_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__55_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__55_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_3733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3733_, 0, v___x_3731_);
lean_ctor_set(v___x_3733_, 1, v___x_3732_);
v___x_3734_ = lean_st_ref_get(v_a_3691_);
v_env_3735_ = lean_ctor_get(v___x_3734_, 0);
lean_inc_ref_n(v_env_3735_, 2);
lean_dec(v___x_3734_);
v___x_3736_ = l_Lean_Name_getPrefix(v_declName_3686_);
v___x_3737_ = 0;
lean_inc(v_declName_3686_);
v___x_3738_ = l_Lean_Environment_findConstVal_x3f(v_env_3735_, v_declName_3686_, v___x_3737_);
if (lean_obj_tag(v___x_3738_) == 1)
{
lean_object* v_val_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; 
v_val_3739_ = lean_ctor_get(v___x_3738_, 0);
lean_inc(v_val_3739_);
lean_dec_ref_known(v___x_3738_, 1);
v___x_3740_ = l_Lean_Name_getPrefix(v_val_3728_);
lean_inc(v_val_3728_);
lean_inc_ref(v_env_3735_);
v___x_3741_ = l_Lean_Environment_findConstVal_x3f(v_env_3735_, v_val_3728_, v___x_3737_);
if (lean_obj_tag(v___x_3741_) == 1)
{
lean_object* v_val_3742_; lean_object* v___x_3743_; 
v_val_3742_ = lean_ctor_get(v___x_3741_, 0);
lean_inc(v_val_3742_);
lean_dec_ref_known(v___x_3741_, 1);
v___x_3743_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq(v_val_3739_, v_val_3742_, v_a_3688_, v_a_3689_, v_a_3690_, v_a_3691_);
if (lean_obj_tag(v___x_3743_) == 0)
{
lean_object* v_a_3744_; lean_object* v_msg_3746_; lean_object* v___y_3747_; lean_object* v___y_3748_; lean_object* v___y_3749_; lean_object* v___y_3750_; lean_object* v___y_3776_; lean_object* v___y_3777_; lean_object* v___y_3778_; lean_object* v___y_3779_; lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v___y_3796_; lean_object* v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3803_; lean_object* v___y_3804_; lean_object* v___y_3805_; lean_object* v___y_3806_; lean_object* v___y_3807_; lean_object* v___y_3808_; lean_object* v_msg_3816_; lean_object* v___y_3817_; lean_object* v___y_3818_; lean_object* v___y_3819_; lean_object* v___y_3820_; uint8_t v___x_3864_; 
v_a_3744_ = lean_ctor_get(v___x_3743_, 0);
lean_inc(v_a_3744_);
lean_dec_ref_known(v___x_3743_, 1);
v___x_3864_ = lean_unbox(v_a_3744_);
if (v___x_3864_ == 0)
{
lean_object* v_type_3865_; lean_object* v_type_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; 
v_type_3865_ = lean_ctor_get(v_val_3742_, 2);
lean_inc_ref(v_type_3865_);
lean_dec(v_val_3742_);
v_type_3866_ = lean_ctor_get(v_val_3739_, 2);
lean_inc_ref(v_type_3866_);
lean_dec(v_val_3739_);
v___x_3867_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_3868_ = l_Lean_indentExpr(v_type_3865_);
v___x_3869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3869_, 0, v___x_3867_);
lean_ctor_set(v___x_3869_, 1, v___x_3868_);
v___x_3870_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_3871_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3871_, 0, v___x_3869_);
lean_ctor_set(v___x_3871_, 1, v___x_3870_);
v___x_3872_ = l_Lean_indentExpr(v_type_3866_);
v___x_3873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3873_, 0, v___x_3871_);
lean_ctor_set(v___x_3873_, 1, v___x_3872_);
v___x_3874_ = l_Lean_MessageData_note(v___x_3873_);
v___x_3875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3875_, 0, v___x_3733_);
lean_ctor_set(v___x_3875_, 1, v___x_3874_);
v_msg_3816_ = v___x_3875_;
v___y_3817_ = v_a_3688_;
v___y_3818_ = v_a_3689_;
v___y_3819_ = v_a_3690_;
v___y_3820_ = v_a_3691_;
goto v___jp_3815_;
}
else
{
lean_dec(v_val_3742_);
lean_dec(v_val_3739_);
v_msg_3816_ = v___x_3733_;
v___y_3817_ = v_a_3688_;
v___y_3818_ = v_a_3689_;
v___y_3819_ = v_a_3690_;
v___y_3820_ = v_a_3691_;
goto v___jp_3815_;
}
v___jp_3745_:
{
uint8_t v___x_3751_; 
v___x_3751_ = lean_unbox(v_a_3744_);
lean_dec(v_a_3744_);
if (v___x_3751_ == 0)
{
lean_dec(v_val_3728_);
lean_dec(v_hint_3687_);
v_extraMsg_3702_ = v_msg_3746_;
v___y_3703_ = v___y_3747_;
v___y_3704_ = v___y_3748_;
v___y_3705_ = v___y_3749_;
v___y_3706_ = v___y_3750_;
goto v___jp_3701_;
}
else
{
switch(lean_obj_tag(v_hint_3687_))
{
case 0:
{
lean_dec(v_val_3728_);
v_extraMsg_3702_ = v_msg_3746_;
v___y_3703_ = v___y_3747_;
v___y_3704_ = v___y_3748_;
v___y_3705_ = v___y_3749_;
v___y_3706_ = v___y_3750_;
goto v___jp_3701_;
}
case 1:
{
lean_object* v___x_3752_; 
lean_inc(v_declName_3686_);
v___x_3752_ = l_Lean_Linter_mkIdentHint(v_declName_3686_, v_val_3728_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_);
if (lean_obj_tag(v___x_3752_) == 0)
{
lean_object* v_a_3753_; lean_object* v___x_3754_; 
v_a_3753_ = lean_ctor_get(v___x_3752_, 0);
lean_inc(v_a_3753_);
lean_dec_ref_known(v___x_3752_, 1);
v___x_3754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3754_, 0, v_msg_3746_);
lean_ctor_set(v___x_3754_, 1, v_a_3753_);
v_extraMsg_3702_ = v___x_3754_;
v___y_3703_ = v___y_3747_;
v___y_3704_ = v___y_3748_;
v___y_3705_ = v___y_3749_;
v___y_3706_ = v___y_3750_;
goto v___jp_3701_;
}
else
{
lean_object* v_a_3755_; lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3762_; 
lean_dec_ref(v_msg_3746_);
lean_dec(v_declName_3686_);
v_a_3755_ = lean_ctor_get(v___x_3752_, 0);
v_isSharedCheck_3762_ = !lean_is_exclusive(v___x_3752_);
if (v_isSharedCheck_3762_ == 0)
{
v___x_3757_ = v___x_3752_;
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
else
{
lean_inc(v_a_3755_);
lean_dec(v___x_3752_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
lean_object* v___x_3760_; 
if (v_isShared_3758_ == 0)
{
v___x_3760_ = v___x_3757_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v_a_3755_);
v___x_3760_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
return v___x_3760_;
}
}
}
}
default: 
{
lean_object* v_mk_3763_; lean_object* v___x_3764_; 
v_mk_3763_ = lean_ctor_get(v_hint_3687_, 0);
lean_inc_ref(v_mk_3763_);
lean_dec_ref_known(v_hint_3687_, 1);
lean_inc(v___y_3750_);
lean_inc_ref(v___y_3749_);
lean_inc(v___y_3748_);
lean_inc_ref(v___y_3747_);
v___x_3764_ = lean_apply_6(v_mk_3763_, v_val_3728_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_, lean_box(0));
if (lean_obj_tag(v___x_3764_) == 0)
{
lean_object* v_a_3765_; lean_object* v___x_3766_; 
v_a_3765_ = lean_ctor_get(v___x_3764_, 0);
lean_inc(v_a_3765_);
lean_dec_ref_known(v___x_3764_, 1);
v___x_3766_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3766_, 0, v_msg_3746_);
lean_ctor_set(v___x_3766_, 1, v_a_3765_);
v_extraMsg_3702_ = v___x_3766_;
v___y_3703_ = v___y_3747_;
v___y_3704_ = v___y_3748_;
v___y_3705_ = v___y_3749_;
v___y_3706_ = v___y_3750_;
goto v___jp_3701_;
}
else
{
lean_object* v_a_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3774_; 
lean_dec_ref(v_msg_3746_);
lean_dec(v_declName_3686_);
v_a_3767_ = lean_ctor_get(v___x_3764_, 0);
v_isSharedCheck_3774_ = !lean_is_exclusive(v___x_3764_);
if (v_isSharedCheck_3774_ == 0)
{
v___x_3769_ = v___x_3764_;
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_a_3767_);
lean_dec(v___x_3764_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
lean_object* v___x_3772_; 
if (v_isShared_3770_ == 0)
{
v___x_3772_ = v___x_3769_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v_a_3767_);
v___x_3772_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
return v___x_3772_;
}
}
}
}
}
}
}
v___jp_3775_:
{
lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; 
v___x_3782_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_3783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3783_, 0, v___x_3782_);
lean_ctor_set(v___x_3783_, 1, v___x_3730_);
v___x_3784_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__5, &l_Lean_Linter_checkDeprecated___closed__5_once, _init_l_Lean_Linter_checkDeprecated___closed__5);
v___x_3785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3785_, 0, v___x_3783_);
lean_ctor_set(v___x_3785_, 1, v___x_3784_);
v___x_3786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3786_, 0, v___x_3785_);
lean_ctor_set(v___x_3786_, 1, v___y_3781_);
v___x_3787_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__7, &l_Lean_Linter_checkDeprecated___closed__7_once, _init_l_Lean_Linter_checkDeprecated___closed__7);
v___x_3788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3788_, 0, v___x_3786_);
lean_ctor_set(v___x_3788_, 1, v___x_3787_);
v___x_3789_ = l_Lean_MessageData_ofName(v___x_3740_);
v___x_3790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3790_, 0, v___x_3788_);
lean_ctor_set(v___x_3790_, 1, v___x_3789_);
v___x_3791_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__9, &l_Lean_Linter_checkDeprecated___closed__9_once, _init_l_Lean_Linter_checkDeprecated___closed__9);
v___x_3792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3792_, 0, v___x_3790_);
lean_ctor_set(v___x_3792_, 1, v___x_3791_);
v___x_3793_ = l_Lean_MessageData_note(v___x_3792_);
v___x_3794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3794_, 0, v___y_3777_);
lean_ctor_set(v___x_3794_, 1, v___x_3793_);
v_msg_3746_ = v___x_3794_;
v___y_3747_ = v___y_3779_;
v___y_3748_ = v___y_3776_;
v___y_3749_ = v___y_3780_;
v___y_3750_ = v___y_3778_;
goto v___jp_3745_;
}
v___jp_3795_:
{
lean_object* v___x_3801_; 
v___x_3801_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__11, &l_Lean_Linter_checkDeprecated___closed__11_once, _init_l_Lean_Linter_checkDeprecated___closed__11);
v___y_3776_ = v___y_3796_;
v___y_3777_ = v___y_3797_;
v___y_3778_ = v___y_3798_;
v___y_3779_ = v___y_3799_;
v___y_3780_ = v___y_3800_;
v___y_3781_ = v___x_3801_;
goto v___jp_3775_;
}
v___jp_3802_:
{
lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; 
v___x_3809_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__13, &l_Lean_Linter_checkDeprecated___closed__13_once, _init_l_Lean_Linter_checkDeprecated___closed__13);
v___x_3810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3810_, 0, v___x_3809_);
lean_ctor_set(v___x_3810_, 1, v___y_3808_);
v___x_3811_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__15, &l_Lean_Linter_checkDeprecated___closed__15_once, _init_l_Lean_Linter_checkDeprecated___closed__15);
v___x_3812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3812_, 0, v___x_3810_);
lean_ctor_set(v___x_3812_, 1, v___x_3811_);
v___x_3813_ = l_Lean_MessageData_note(v___x_3812_);
v___x_3814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3814_, 0, v___y_3804_);
lean_ctor_set(v___x_3814_, 1, v___x_3813_);
v_msg_3746_ = v___x_3814_;
v___y_3747_ = v___y_3806_;
v___y_3748_ = v___y_3803_;
v___y_3749_ = v___y_3807_;
v___y_3750_ = v___y_3805_;
goto v___jp_3745_;
}
v___jp_3815_:
{
uint8_t v___x_3821_; 
v___x_3821_ = l_Lean_Name_isAnonymous(v___x_3736_);
if (v___x_3821_ == 0)
{
uint8_t v___x_3822_; 
v___x_3822_ = lean_name_eq(v___x_3736_, v___x_3740_);
lean_dec(v___x_3736_);
if (v___x_3822_ == 0)
{
lean_dec(v___x_3740_);
lean_dec_ref(v_env_3735_);
lean_dec_ref(v___x_3730_);
if (lean_obj_tag(v_declName_3686_) == 1)
{
lean_object* v_str_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; 
v_str_3823_ = lean_ctor_get(v_declName_3686_, 1);
v___x_3824_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__17, &l_Lean_Linter_checkDeprecated___closed__17_once, _init_l_Lean_Linter_checkDeprecated___closed__17);
lean_inc_ref(v_str_3823_);
v___x_3825_ = l_Lean_stringToMessageData(v_str_3823_);
v___x_3826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3826_, 0, v___x_3824_);
lean_ctor_set(v___x_3826_, 1, v___x_3825_);
v___x_3827_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__19, &l_Lean_Linter_checkDeprecated___closed__19_once, _init_l_Lean_Linter_checkDeprecated___closed__19);
v___x_3828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3828_, 0, v___x_3826_);
lean_ctor_set(v___x_3828_, 1, v___x_3827_);
lean_inc(v_val_3728_);
v___x_3829_ = l_Lean_MessageData_ofConstName(v_val_3728_, v___x_3821_);
v___x_3830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3830_, 0, v___x_3828_);
lean_ctor_set(v___x_3830_, 1, v___x_3829_);
v___x_3831_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__21, &l_Lean_Linter_checkDeprecated___closed__21_once, _init_l_Lean_Linter_checkDeprecated___closed__21);
v___x_3832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3832_, 0, v___x_3830_);
lean_ctor_set(v___x_3832_, 1, v___x_3831_);
v___y_3803_ = v___y_3818_;
v___y_3804_ = v_msg_3816_;
v___y_3805_ = v___y_3820_;
v___y_3806_ = v___y_3817_;
v___y_3807_ = v___y_3819_;
v___y_3808_ = v___x_3832_;
goto v___jp_3802_;
}
else
{
lean_object* v___x_3833_; 
v___x_3833_ = l_Lean_MessageData_nil;
v___y_3803_ = v___y_3818_;
v___y_3804_ = v_msg_3816_;
v___y_3805_ = v___y_3820_;
v___y_3806_ = v___y_3817_;
v___y_3807_ = v___y_3819_;
v___y_3808_ = v___x_3833_;
goto v___jp_3802_;
}
}
else
{
uint8_t v___x_3834_; 
lean_inc(v_declName_3686_);
lean_inc_ref(v_env_3735_);
v___x_3834_ = l_Lean_isProtected(v_env_3735_, v_declName_3686_);
if (v___x_3834_ == 0)
{
uint8_t v___x_3835_; 
lean_inc(v_val_3728_);
v___x_3835_ = l_Lean_isProtected(v_env_3735_, v_val_3728_);
if (v___x_3835_ == 0)
{
lean_dec(v___x_3740_);
lean_dec_ref(v___x_3730_);
v_msg_3746_ = v_msg_3816_;
v___y_3747_ = v___y_3817_;
v___y_3748_ = v___y_3818_;
v___y_3749_ = v___y_3819_;
v___y_3750_ = v___y_3820_;
goto v___jp_3745_;
}
else
{
lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; 
v___x_3836_ = l_Lean_Name_revIter(v___x_3740_);
v___x_3837_ = lean_unsigned_to_nat(3u);
v___x_3838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3838_, 0, v___x_3837_);
lean_ctor_set(v___x_3838_, 1, v___x_3836_);
v___x_3839_ = ((lean_object*)(l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14___closed__0));
v___x_3840_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Linter_checkDeprecated_spec__1___redArg(v___x_3838_, v___x_3839_);
v___x_3841_ = lean_array_to_list(v___x_3840_);
if (lean_obj_tag(v___x_3841_) == 1)
{
lean_object* v_tail_3842_; 
v_tail_3842_ = lean_ctor_get(v___x_3841_, 1);
lean_inc(v_tail_3842_);
if (lean_obj_tag(v_tail_3842_) == 1)
{
lean_object* v_tail_3843_; lean_object* v___x_3845_; uint8_t v_isShared_3846_; uint8_t v_isSharedCheck_3862_; 
v_tail_3843_ = lean_ctor_get(v_tail_3842_, 1);
v_isSharedCheck_3862_ = !lean_is_exclusive(v_tail_3842_);
if (v_isSharedCheck_3862_ == 0)
{
lean_object* v_unused_3863_; 
v_unused_3863_ = lean_ctor_get(v_tail_3842_, 0);
lean_dec(v_unused_3863_);
v___x_3845_ = v_tail_3842_;
v_isShared_3846_ = v_isSharedCheck_3862_;
goto v_resetjp_3844_;
}
else
{
lean_inc(v_tail_3843_);
lean_dec(v_tail_3842_);
v___x_3845_ = lean_box(0);
v_isShared_3846_ = v_isSharedCheck_3862_;
goto v_resetjp_3844_;
}
v_resetjp_3844_:
{
if (lean_obj_tag(v_tail_3843_) == 0)
{
lean_object* v_head_3847_; lean_object* v___x_3849_; uint8_t v_isShared_3850_; uint8_t v_isSharedCheck_3860_; 
v_head_3847_ = lean_ctor_get(v___x_3841_, 0);
v_isSharedCheck_3860_ = !lean_is_exclusive(v___x_3841_);
if (v_isSharedCheck_3860_ == 0)
{
lean_object* v_unused_3861_; 
v_unused_3861_ = lean_ctor_get(v___x_3841_, 1);
lean_dec(v_unused_3861_);
v___x_3849_ = v___x_3841_;
v_isShared_3850_ = v_isSharedCheck_3860_;
goto v_resetjp_3848_;
}
else
{
lean_inc(v_head_3847_);
lean_dec(v___x_3841_);
v___x_3849_ = lean_box(0);
v_isShared_3850_ = v_isSharedCheck_3860_;
goto v_resetjp_3848_;
}
v_resetjp_3848_:
{
lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3854_; 
v___x_3851_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__23, &l_Lean_Linter_checkDeprecated___closed__23_once, _init_l_Lean_Linter_checkDeprecated___closed__23);
v___x_3852_ = l_Lean_MessageData_ofName(v_head_3847_);
if (v_isShared_3846_ == 0)
{
lean_ctor_set_tag(v___x_3845_, 7);
lean_ctor_set(v___x_3845_, 1, v___x_3852_);
lean_ctor_set(v___x_3845_, 0, v___x_3851_);
v___x_3854_ = v___x_3845_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3859_; 
v_reuseFailAlloc_3859_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3859_, 0, v___x_3851_);
lean_ctor_set(v_reuseFailAlloc_3859_, 1, v___x_3852_);
v___x_3854_ = v_reuseFailAlloc_3859_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
lean_object* v___x_3855_; lean_object* v___x_3857_; 
v___x_3855_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__25, &l_Lean_Linter_checkDeprecated___closed__25_once, _init_l_Lean_Linter_checkDeprecated___closed__25);
if (v_isShared_3850_ == 0)
{
lean_ctor_set_tag(v___x_3849_, 7);
lean_ctor_set(v___x_3849_, 1, v___x_3855_);
lean_ctor_set(v___x_3849_, 0, v___x_3854_);
v___x_3857_ = v___x_3849_;
goto v_reusejp_3856_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v___x_3854_);
lean_ctor_set(v_reuseFailAlloc_3858_, 1, v___x_3855_);
v___x_3857_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3856_;
}
v_reusejp_3856_:
{
v___y_3776_ = v___y_3818_;
v___y_3777_ = v_msg_3816_;
v___y_3778_ = v___y_3820_;
v___y_3779_ = v___y_3817_;
v___y_3780_ = v___y_3819_;
v___y_3781_ = v___x_3857_;
goto v___jp_3775_;
}
}
}
}
else
{
lean_del_object(v___x_3845_);
lean_dec(v_tail_3843_);
lean_dec_ref_known(v___x_3841_, 2);
v___y_3796_ = v___y_3818_;
v___y_3797_ = v_msg_3816_;
v___y_3798_ = v___y_3820_;
v___y_3799_ = v___y_3817_;
v___y_3800_ = v___y_3819_;
goto v___jp_3795_;
}
}
}
else
{
lean_dec_ref_known(v___x_3841_, 2);
lean_dec(v_tail_3842_);
v___y_3796_ = v___y_3818_;
v___y_3797_ = v_msg_3816_;
v___y_3798_ = v___y_3820_;
v___y_3799_ = v___y_3817_;
v___y_3800_ = v___y_3819_;
goto v___jp_3795_;
}
}
else
{
lean_dec(v___x_3841_);
v___y_3796_ = v___y_3818_;
v___y_3797_ = v_msg_3816_;
v___y_3798_ = v___y_3820_;
v___y_3799_ = v___y_3817_;
v___y_3800_ = v___y_3819_;
goto v___jp_3795_;
}
}
}
else
{
lean_dec(v___x_3740_);
lean_dec_ref(v_env_3735_);
lean_dec_ref(v___x_3730_);
v_msg_3746_ = v_msg_3816_;
v___y_3747_ = v___y_3817_;
v___y_3748_ = v___y_3818_;
v___y_3749_ = v___y_3819_;
v___y_3750_ = v___y_3820_;
goto v___jp_3745_;
}
}
}
else
{
lean_dec(v___x_3740_);
lean_dec(v___x_3736_);
lean_dec_ref(v_env_3735_);
lean_dec_ref(v___x_3730_);
v_msg_3746_ = v_msg_3816_;
v___y_3747_ = v___y_3817_;
v___y_3748_ = v___y_3818_;
v___y_3749_ = v___y_3819_;
v___y_3750_ = v___y_3820_;
goto v___jp_3745_;
}
}
}
else
{
lean_object* v_a_3876_; lean_object* v___x_3878_; uint8_t v_isShared_3879_; uint8_t v_isSharedCheck_3883_; 
lean_dec(v_val_3742_);
lean_dec(v___x_3740_);
lean_dec(v_val_3739_);
lean_dec(v___x_3736_);
lean_dec_ref(v_env_3735_);
lean_dec_ref_known(v___x_3733_, 2);
lean_dec_ref(v___x_3730_);
lean_dec(v_val_3728_);
lean_dec(v_hint_3687_);
lean_dec(v_declName_3686_);
v_a_3876_ = lean_ctor_get(v___x_3743_, 0);
v_isSharedCheck_3883_ = !lean_is_exclusive(v___x_3743_);
if (v_isSharedCheck_3883_ == 0)
{
v___x_3878_ = v___x_3743_;
v_isShared_3879_ = v_isSharedCheck_3883_;
goto v_resetjp_3877_;
}
else
{
lean_inc(v_a_3876_);
lean_dec(v___x_3743_);
v___x_3878_ = lean_box(0);
v_isShared_3879_ = v_isSharedCheck_3883_;
goto v_resetjp_3877_;
}
v_resetjp_3877_:
{
lean_object* v___x_3881_; 
if (v_isShared_3879_ == 0)
{
v___x_3881_ = v___x_3878_;
goto v_reusejp_3880_;
}
else
{
lean_object* v_reuseFailAlloc_3882_; 
v_reuseFailAlloc_3882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3882_, 0, v_a_3876_);
v___x_3881_ = v_reuseFailAlloc_3882_;
goto v_reusejp_3880_;
}
v_reusejp_3880_:
{
return v___x_3881_;
}
}
}
}
else
{
lean_dec(v___x_3741_);
lean_dec(v___x_3740_);
lean_dec(v_val_3739_);
lean_dec(v___x_3736_);
lean_dec_ref(v_env_3735_);
lean_dec_ref(v___x_3730_);
lean_dec(v_val_3728_);
lean_dec(v_hint_3687_);
v_extraMsg_3702_ = v___x_3733_;
v___y_3703_ = v_a_3688_;
v___y_3704_ = v_a_3689_;
v___y_3705_ = v_a_3690_;
v___y_3706_ = v_a_3691_;
goto v___jp_3701_;
}
}
else
{
lean_dec(v___x_3738_);
lean_dec(v___x_3736_);
lean_dec_ref(v_env_3735_);
lean_dec_ref(v___x_3730_);
lean_dec(v_val_3728_);
lean_dec(v_hint_3687_);
v_extraMsg_3702_ = v___x_3733_;
v___y_3703_ = v_a_3688_;
v___y_3704_ = v_a_3689_;
v___y_3705_ = v_a_3690_;
v___y_3706_ = v_a_3691_;
goto v___jp_3701_;
}
}
}
else
{
lean_object* v_val_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; 
lean_inc_ref(v_text_x3f_3725_);
lean_dec(v_val_3724_);
lean_dec(v_hint_3687_);
v_val_3884_ = lean_ctor_get(v_text_x3f_3725_, 0);
lean_inc(v_val_3884_);
lean_dec_ref_known(v_text_x3f_3725_, 1);
v___x_3885_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__27, &l_Lean_Linter_checkDeprecated___closed__27_once, _init_l_Lean_Linter_checkDeprecated___closed__27);
v___x_3886_ = l_Lean_stringToMessageData(v_val_3884_);
v___x_3887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3887_, 0, v___x_3885_);
lean_ctor_set(v___x_3887_, 1, v___x_3886_);
v_extraMsg_3702_ = v___x_3887_;
v___y_3703_ = v_a_3688_;
v___y_3704_ = v_a_3689_;
v___y_3705_ = v_a_3690_;
v___y_3706_ = v_a_3691_;
goto v___jp_3701_;
}
}
else
{
lean_object* v___x_3888_; lean_object* v___x_3890_; 
lean_dec(v___x_3723_);
lean_dec(v_hint_3687_);
lean_dec(v_declName_3686_);
v___x_3888_ = lean_box(0);
if (v_isShared_3698_ == 0)
{
lean_ctor_set(v___x_3697_, 0, v___x_3888_);
v___x_3890_ = v___x_3697_;
goto v_reusejp_3889_;
}
else
{
lean_object* v_reuseFailAlloc_3891_; 
v_reuseFailAlloc_3891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3891_, 0, v___x_3888_);
v___x_3890_ = v_reuseFailAlloc_3891_;
goto v_reusejp_3889_;
}
v_reusejp_3889_:
{
return v___x_3890_;
}
}
}
v___jp_3701_:
{
lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; 
v___x_3707_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_3708_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_3709_ = l_Lean_MessageData_ofConstName(v_declName_3686_, v___x_3700_);
v___x_3710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3710_, 0, v___x_3708_);
lean_ctor_set(v___x_3710_, 1, v___x_3709_);
v___x_3711_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__1, &l_Lean_Linter_checkDeprecated___closed__1_once, _init_l_Lean_Linter_checkDeprecated___closed__1);
v___x_3712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3712_, 0, v___x_3710_);
lean_ctor_set(v___x_3712_, 1, v___x_3711_);
v___x_3713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3713_, 0, v___x_3712_);
lean_ctor_set(v___x_3713_, 1, v_extraMsg_3702_);
v___x_3714_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3714_, 0, v___x_3707_);
lean_ctor_set(v___x_3714_, 1, v___x_3713_);
v___x_3715_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40(v___x_3714_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
return v___x_3715_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkDeprecated___boxed(lean_object* v_declName_3893_, lean_object* v_hint_3894_, lean_object* v_a_3895_, lean_object* v_a_3896_, lean_object* v_a_3897_, lean_object* v_a_3898_, lean_object* v_a_3899_){
_start:
{
lean_object* v_res_3900_; 
v_res_3900_ = l_Lean_Linter_checkDeprecated(v_declName_3893_, v_hint_3894_, v_a_3895_, v_a_3896_, v_a_3897_, v_a_3898_);
lean_dec(v_a_3898_);
lean_dec_ref(v_a_3897_);
lean_dec(v_a_3896_);
lean_dec_ref(v_a_3895_);
return v_res_3900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0(lean_object* v_o_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_){
_start:
{
lean_object* v___x_3907_; 
v___x_3907_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(v_o_3901_, v___y_3905_);
return v___x_3907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___boxed(lean_object* v_o_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_){
_start:
{
lean_object* v_res_3914_; 
v_res_3914_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0(v_o_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_);
lean_dec(v___y_3912_);
lean_dec_ref(v___y_3911_);
lean_dec(v___y_3910_);
lean_dec_ref(v___y_3909_);
return v_res_3914_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Linter_checkDeprecated_spec__1(lean_object* v_inst_3915_, lean_object* v_R_3916_, lean_object* v_a_3917_, lean_object* v_b_3918_){
_start:
{
lean_object* v___x_3919_; 
v___x_3919_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Linter_checkDeprecated_spec__1___redArg(v_a_3917_, v_b_3918_);
return v___x_3919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkDeprecatedAt(lean_object* v_ref_3920_, lean_object* v_declName_3921_, lean_object* v_hint_3922_, lean_object* v_a_3923_, lean_object* v_a_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_){
_start:
{
lean_object* v_toCold_3928_; lean_object* v_currRecDepth_3929_; lean_object* v_ref_3930_; uint16_t v_optionFlags_3931_; uint8_t v_suppressElabErrors_3932_; uint8_t v_checkDeprecated_3933_; uint8_t v_isRecordingDeps_3934_; lean_object* v_ref_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; 
v_toCold_3928_ = lean_ctor_get(v_a_3925_, 0);
v_currRecDepth_3929_ = lean_ctor_get(v_a_3925_, 1);
v_ref_3930_ = lean_ctor_get(v_a_3925_, 2);
v_optionFlags_3931_ = lean_ctor_get_uint16(v_a_3925_, sizeof(void*)*3);
v_suppressElabErrors_3932_ = lean_ctor_get_uint8(v_a_3925_, sizeof(void*)*3 + 2);
v_checkDeprecated_3933_ = lean_ctor_get_uint8(v_a_3925_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3934_ = lean_ctor_get_uint8(v_a_3925_, sizeof(void*)*3 + 4);
v_ref_3935_ = l_Lean_replaceRef(v_ref_3920_, v_ref_3930_);
lean_inc(v_currRecDepth_3929_);
lean_inc_ref(v_toCold_3928_);
v___x_3936_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3936_, 0, v_toCold_3928_);
lean_ctor_set(v___x_3936_, 1, v_currRecDepth_3929_);
lean_ctor_set(v___x_3936_, 2, v_ref_3935_);
lean_ctor_set_uint16(v___x_3936_, sizeof(void*)*3, v_optionFlags_3931_);
lean_ctor_set_uint8(v___x_3936_, sizeof(void*)*3 + 2, v_suppressElabErrors_3932_);
lean_ctor_set_uint8(v___x_3936_, sizeof(void*)*3 + 3, v_checkDeprecated_3933_);
lean_ctor_set_uint8(v___x_3936_, sizeof(void*)*3 + 4, v_isRecordingDeps_3934_);
v___x_3937_ = l_Lean_Core_shouldCheckDeprecated___redArg(v_ref_3920_, v___x_3936_);
if (lean_obj_tag(v___x_3937_) == 0)
{
lean_object* v_a_3938_; lean_object* v___x_3940_; uint8_t v_isShared_3941_; uint8_t v_isSharedCheck_3948_; 
v_a_3938_ = lean_ctor_get(v___x_3937_, 0);
v_isSharedCheck_3948_ = !lean_is_exclusive(v___x_3937_);
if (v_isSharedCheck_3948_ == 0)
{
v___x_3940_ = v___x_3937_;
v_isShared_3941_ = v_isSharedCheck_3948_;
goto v_resetjp_3939_;
}
else
{
lean_inc(v_a_3938_);
lean_dec(v___x_3937_);
v___x_3940_ = lean_box(0);
v_isShared_3941_ = v_isSharedCheck_3948_;
goto v_resetjp_3939_;
}
v_resetjp_3939_:
{
uint8_t v___x_3942_; 
v___x_3942_ = lean_unbox(v_a_3938_);
lean_dec(v_a_3938_);
if (v___x_3942_ == 0)
{
lean_object* v___x_3943_; lean_object* v___x_3945_; 
lean_dec_ref_known(v___x_3936_, 3);
lean_dec(v_hint_3922_);
lean_dec(v_declName_3921_);
v___x_3943_ = lean_box(0);
if (v_isShared_3941_ == 0)
{
lean_ctor_set(v___x_3940_, 0, v___x_3943_);
v___x_3945_ = v___x_3940_;
goto v_reusejp_3944_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v___x_3943_);
v___x_3945_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3944_;
}
v_reusejp_3944_:
{
return v___x_3945_;
}
}
else
{
lean_object* v___x_3947_; 
lean_del_object(v___x_3940_);
v___x_3947_ = l_Lean_Linter_checkDeprecated(v_declName_3921_, v_hint_3922_, v_a_3923_, v_a_3924_, v___x_3936_, v_a_3926_);
lean_dec_ref_known(v___x_3936_, 3);
return v___x_3947_;
}
}
}
else
{
lean_object* v_a_3949_; lean_object* v___x_3951_; uint8_t v_isShared_3952_; uint8_t v_isSharedCheck_3956_; 
lean_dec_ref_known(v___x_3936_, 3);
lean_dec(v_hint_3922_);
lean_dec(v_declName_3921_);
v_a_3949_ = lean_ctor_get(v___x_3937_, 0);
v_isSharedCheck_3956_ = !lean_is_exclusive(v___x_3937_);
if (v_isSharedCheck_3956_ == 0)
{
v___x_3951_ = v___x_3937_;
v_isShared_3952_ = v_isSharedCheck_3956_;
goto v_resetjp_3950_;
}
else
{
lean_inc(v_a_3949_);
lean_dec(v___x_3937_);
v___x_3951_ = lean_box(0);
v_isShared_3952_ = v_isSharedCheck_3956_;
goto v_resetjp_3950_;
}
v_resetjp_3950_:
{
lean_object* v___x_3954_; 
if (v_isShared_3952_ == 0)
{
v___x_3954_ = v___x_3951_;
goto v_reusejp_3953_;
}
else
{
lean_object* v_reuseFailAlloc_3955_; 
v_reuseFailAlloc_3955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3955_, 0, v_a_3949_);
v___x_3954_ = v_reuseFailAlloc_3955_;
goto v_reusejp_3953_;
}
v_reusejp_3953_:
{
return v___x_3954_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkDeprecatedAt___boxed(lean_object* v_ref_3957_, lean_object* v_declName_3958_, lean_object* v_hint_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_){
_start:
{
lean_object* v_res_3965_; 
v_res_3965_ = l_Lean_Linter_checkDeprecatedAt(v_ref_3957_, v_declName_3958_, v_hint_3959_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_);
lean_dec(v_a_3963_);
lean_dec_ref(v_a_3962_);
lean_dec(v_a_3961_);
lean_dec_ref(v_a_3960_);
lean_dec(v_ref_3957_);
return v_res_3965_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_mkListRemovalSuggestion_spec__0(size_t v_sz_3966_, size_t v_i_3967_, lean_object* v_bs_3968_){
_start:
{
uint8_t v___x_3969_; 
v___x_3969_ = lean_usize_dec_lt(v_i_3967_, v_sz_3966_);
if (v___x_3969_ == 0)
{
lean_object* v___x_3970_; 
v___x_3970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3970_, 0, v_bs_3968_);
return v___x_3970_;
}
else
{
lean_object* v_v_3971_; lean_object* v___x_3972_; 
v_v_3971_ = lean_array_uget_borrowed(v_bs_3968_, v_i_3967_);
v___x_3972_ = l_Lean_Syntax_getRange_x3f(v_v_3971_, v___x_3969_);
if (lean_obj_tag(v___x_3972_) == 0)
{
lean_object* v___x_3973_; 
lean_dec_ref(v_bs_3968_);
v___x_3973_ = lean_box(0);
return v___x_3973_;
}
else
{
lean_object* v_val_3974_; lean_object* v___x_3975_; lean_object* v_bs_x27_3976_; size_t v___x_3977_; size_t v___x_3978_; lean_object* v___x_3979_; 
v_val_3974_ = lean_ctor_get(v___x_3972_, 0);
lean_inc(v_val_3974_);
lean_dec_ref_known(v___x_3972_, 1);
v___x_3975_ = lean_unsigned_to_nat(0u);
v_bs_x27_3976_ = lean_array_uset(v_bs_3968_, v_i_3967_, v___x_3975_);
v___x_3977_ = ((size_t)1ULL);
v___x_3978_ = lean_usize_add(v_i_3967_, v___x_3977_);
v___x_3979_ = lean_array_uset(v_bs_x27_3976_, v_i_3967_, v_val_3974_);
v_i_3967_ = v___x_3978_;
v_bs_3968_ = v___x_3979_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_mkListRemovalSuggestion_spec__0___boxed(lean_object* v_sz_3981_, lean_object* v_i_3982_, lean_object* v_bs_3983_){
_start:
{
size_t v_sz_boxed_3984_; size_t v_i_boxed_3985_; lean_object* v_res_3986_; 
v_sz_boxed_3984_ = lean_unbox_usize(v_sz_3981_);
lean_dec(v_sz_3981_);
v_i_boxed_3985_ = lean_unbox_usize(v_i_3982_);
lean_dec(v_i_3982_);
v_res_3986_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_mkListRemovalSuggestion_spec__0(v_sz_boxed_3984_, v_i_boxed_3985_, v_bs_3983_);
return v_res_3986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_mkListRemovalSuggestion___redArg(lean_object* v_whole_3992_, lean_object* v_elems_3993_, lean_object* v_i_3994_, lean_object* v_a_3995_){
_start:
{
lean_object* v_toCold_4000_; lean_object* v_fileMap_4001_; lean_object* v_source_4002_; uint8_t v___x_4003_; lean_object* v___x_4004_; 
v_toCold_4000_ = lean_ctor_get(v_a_3995_, 0);
v_fileMap_4001_ = lean_ctor_get(v_toCold_4000_, 1);
v_source_4002_ = lean_ctor_get(v_fileMap_4001_, 0);
v___x_4003_ = 1;
v___x_4004_ = l_Lean_Syntax_getSubstring_x3f(v_whole_3992_, v___x_4003_, v___x_4003_);
if (lean_obj_tag(v___x_4004_) == 0)
{
lean_dec_ref(v_elems_3993_);
lean_dec(v_whole_3992_);
goto v___jp_3997_;
}
else
{
lean_object* v_val_4005_; lean_object* v___x_4007_; uint8_t v_isShared_4008_; uint8_t v_isSharedCheck_4075_; 
v_val_4005_ = lean_ctor_get(v___x_4004_, 0);
v_isSharedCheck_4075_ = !lean_is_exclusive(v___x_4004_);
if (v_isSharedCheck_4075_ == 0)
{
v___x_4007_ = v___x_4004_;
v_isShared_4008_ = v_isSharedCheck_4075_;
goto v_resetjp_4006_;
}
else
{
lean_inc(v_val_4005_);
lean_dec(v___x_4004_);
v___x_4007_ = lean_box(0);
v_isShared_4008_ = v_isSharedCheck_4075_;
goto v_resetjp_4006_;
}
v_resetjp_4006_:
{
lean_object* v_str_4009_; uint8_t v___x_4010_; 
v_str_4009_ = lean_ctor_get(v_val_4005_, 0);
lean_inc_ref(v_str_4009_);
lean_dec(v_val_4005_);
v___x_4010_ = lean_string_dec_eq(v_str_4009_, v_source_4002_);
lean_dec_ref(v_str_4009_);
if (v___x_4010_ == 0)
{
lean_del_object(v___x_4007_);
lean_dec_ref(v_elems_3993_);
lean_dec(v_whole_3992_);
goto v___jp_3997_;
}
else
{
lean_object* v___x_4011_; 
v___x_4011_ = l_Lean_Syntax_getRange_x3f(v_whole_3992_, v___x_4003_);
if (lean_obj_tag(v___x_4011_) == 1)
{
lean_object* v_val_4012_; lean_object* v___x_4014_; uint8_t v_isShared_4015_; uint8_t v_isSharedCheck_4072_; 
v_val_4012_ = lean_ctor_get(v___x_4011_, 0);
v_isSharedCheck_4072_ = !lean_is_exclusive(v___x_4011_);
if (v_isSharedCheck_4072_ == 0)
{
v___x_4014_ = v___x_4011_;
v_isShared_4015_ = v_isSharedCheck_4072_;
goto v_resetjp_4013_;
}
else
{
lean_inc(v_val_4012_);
lean_dec(v___x_4011_);
v___x_4014_ = lean_box(0);
v_isShared_4015_ = v_isSharedCheck_4072_;
goto v_resetjp_4013_;
}
v_resetjp_4013_:
{
lean_object* v_fst_4017_; lean_object* v_snd_4018_; size_t v_sz_4036_; size_t v___x_4037_; lean_object* v___x_4038_; 
v_sz_4036_ = lean_array_size(v_elems_3993_);
v___x_4037_ = ((size_t)0ULL);
v___x_4038_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_mkListRemovalSuggestion_spec__0(v_sz_4036_, v___x_4037_, v_elems_3993_);
if (lean_obj_tag(v___x_4038_) == 1)
{
lean_object* v_val_4039_; lean_object* v___x_4041_; uint8_t v_isShared_4042_; uint8_t v_isSharedCheck_4069_; 
v_val_4039_ = lean_ctor_get(v___x_4038_, 0);
v_isSharedCheck_4069_ = !lean_is_exclusive(v___x_4038_);
if (v_isSharedCheck_4069_ == 0)
{
v___x_4041_ = v___x_4038_;
v_isShared_4042_ = v_isSharedCheck_4069_;
goto v_resetjp_4040_;
}
else
{
lean_inc(v_val_4039_);
lean_dec(v___x_4038_);
v___x_4041_ = lean_box(0);
v_isShared_4042_ = v_isSharedCheck_4069_;
goto v_resetjp_4040_;
}
v_resetjp_4040_:
{
lean_object* v___x_4043_; uint8_t v___x_4044_; 
v___x_4043_ = lean_array_get_size(v_val_4039_);
v___x_4044_ = lean_nat_dec_lt(v_i_3994_, v___x_4043_);
if (v___x_4044_ == 0)
{
lean_object* v___x_4045_; lean_object* v___x_4046_; 
lean_del_object(v___x_4041_);
lean_dec(v_val_4039_);
lean_del_object(v___x_4014_);
lean_dec(v_val_4012_);
lean_del_object(v___x_4007_);
lean_dec(v_whole_3992_);
v___x_4045_ = lean_box(0);
v___x_4046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4046_, 0, v___x_4045_);
return v___x_4046_;
}
else
{
lean_object* v___x_4047_; uint8_t v___x_4048_; 
v___x_4047_ = lean_unsigned_to_nat(1u);
v___x_4048_ = lean_nat_dec_eq(v___x_4043_, v___x_4047_);
if (v___x_4048_ == 0)
{
lean_object* v___x_4049_; lean_object* v___x_4050_; uint8_t v___x_4051_; 
lean_del_object(v___x_4041_);
v___x_4049_ = lean_array_fget_borrowed(v_val_4039_, v_i_3994_);
v___x_4050_ = lean_nat_add(v_i_3994_, v___x_4047_);
v___x_4051_ = lean_nat_dec_lt(v___x_4050_, v___x_4043_);
if (v___x_4051_ == 0)
{
lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v_stop_4055_; lean_object* v_stop_4056_; 
lean_inc(v___x_4049_);
lean_dec(v___x_4050_);
v___x_4052_ = l_Lean_Syntax_instInhabitedRange_default;
v___x_4053_ = lean_nat_sub(v_i_3994_, v___x_4047_);
v___x_4054_ = lean_array_get(v___x_4052_, v_val_4039_, v___x_4053_);
lean_dec(v___x_4053_);
lean_dec(v_val_4039_);
v_stop_4055_ = lean_ctor_get(v___x_4054_, 1);
lean_inc(v_stop_4055_);
lean_dec(v___x_4054_);
v_stop_4056_ = lean_ctor_get(v___x_4049_, 1);
lean_inc(v_stop_4056_);
lean_dec(v___x_4049_);
v_fst_4017_ = v_stop_4055_;
v_snd_4018_ = v_stop_4056_;
goto v___jp_4016_;
}
else
{
lean_object* v_start_4057_; lean_object* v___x_4058_; lean_object* v_start_4059_; 
v_start_4057_ = lean_ctor_get(v___x_4049_, 0);
lean_inc(v_start_4057_);
v___x_4058_ = lean_array_fget(v_val_4039_, v___x_4050_);
lean_dec(v___x_4050_);
lean_dec(v_val_4039_);
v_start_4059_ = lean_ctor_get(v___x_4058_, 0);
lean_inc(v_start_4059_);
lean_dec(v___x_4058_);
v_fst_4017_ = v_start_4057_;
v_snd_4018_ = v_start_4059_;
goto v___jp_4016_;
}
}
else
{
lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4063_; 
lean_dec(v_val_4039_);
lean_del_object(v___x_4014_);
lean_dec(v_val_4012_);
lean_del_object(v___x_4007_);
v___x_4060_ = lean_box(0);
v___x_4061_ = ((lean_object*)(l_Lean_Linter_mkListRemovalSuggestion___redArg___closed__1));
if (v_isShared_4042_ == 0)
{
lean_ctor_set(v___x_4041_, 0, v_whole_3992_);
v___x_4063_ = v___x_4041_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4068_; 
v_reuseFailAlloc_4068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4068_, 0, v_whole_3992_);
v___x_4063_ = v_reuseFailAlloc_4068_;
goto v_reusejp_4062_;
}
v_reusejp_4062_:
{
uint8_t v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; 
v___x_4064_ = 0;
v___x_4065_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4065_, 0, v___x_4061_);
lean_ctor_set(v___x_4065_, 1, v___x_4063_);
lean_ctor_set(v___x_4065_, 2, v___x_4060_);
lean_ctor_set_uint8(v___x_4065_, sizeof(void*)*3, v___x_4064_);
v___x_4066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4066_, 0, v___x_4065_);
v___x_4067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4067_, 0, v___x_4066_);
return v___x_4067_;
}
}
}
}
}
else
{
lean_object* v___x_4070_; lean_object* v___x_4071_; 
lean_dec(v___x_4038_);
lean_del_object(v___x_4014_);
lean_dec(v_val_4012_);
lean_del_object(v___x_4007_);
lean_dec(v_whole_3992_);
v___x_4070_ = lean_box(0);
v___x_4071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4071_, 0, v___x_4070_);
return v___x_4071_;
}
v___jp_4016_:
{
lean_object* v_start_4019_; lean_object* v_stop_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4028_; 
v_start_4019_ = lean_ctor_get(v_val_4012_, 0);
lean_inc(v_start_4019_);
v_stop_4020_ = lean_ctor_get(v_val_4012_, 1);
lean_inc(v_stop_4020_);
lean_dec(v_val_4012_);
v___x_4021_ = lean_string_utf8_extract(v_source_4002_, v_start_4019_, v_fst_4017_);
lean_dec(v_fst_4017_);
lean_dec(v_start_4019_);
v___x_4022_ = lean_string_utf8_extract(v_source_4002_, v_snd_4018_, v_stop_4020_);
lean_dec(v_stop_4020_);
lean_dec(v_snd_4018_);
v___x_4023_ = lean_string_append(v___x_4021_, v___x_4022_);
lean_dec_ref(v___x_4022_);
v___x_4024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4024_, 0, v___x_4023_);
v___x_4025_ = lean_box(0);
v___x_4026_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4026_, 0, v___x_4024_);
lean_ctor_set(v___x_4026_, 1, v___x_4025_);
lean_ctor_set(v___x_4026_, 2, v___x_4025_);
lean_ctor_set(v___x_4026_, 3, v___x_4025_);
lean_ctor_set(v___x_4026_, 4, v___x_4025_);
lean_ctor_set(v___x_4026_, 5, v___x_4025_);
if (v_isShared_4015_ == 0)
{
lean_ctor_set(v___x_4014_, 0, v_whole_3992_);
v___x_4028_ = v___x_4014_;
goto v_reusejp_4027_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v_whole_3992_);
v___x_4028_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4027_;
}
v_reusejp_4027_:
{
uint8_t v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4032_; 
v___x_4029_ = 0;
v___x_4030_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4030_, 0, v___x_4026_);
lean_ctor_set(v___x_4030_, 1, v___x_4028_);
lean_ctor_set(v___x_4030_, 2, v___x_4025_);
lean_ctor_set_uint8(v___x_4030_, sizeof(void*)*3, v___x_4029_);
if (v_isShared_4008_ == 0)
{
lean_ctor_set(v___x_4007_, 0, v___x_4030_);
v___x_4032_ = v___x_4007_;
goto v_reusejp_4031_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v___x_4030_);
v___x_4032_ = v_reuseFailAlloc_4034_;
goto v_reusejp_4031_;
}
v_reusejp_4031_:
{
lean_object* v___x_4033_; 
v___x_4033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4033_, 0, v___x_4032_);
return v___x_4033_;
}
}
}
}
}
else
{
lean_object* v___x_4073_; lean_object* v___x_4074_; 
lean_dec(v___x_4011_);
lean_del_object(v___x_4007_);
lean_dec_ref(v_elems_3993_);
lean_dec(v_whole_3992_);
v___x_4073_ = lean_box(0);
v___x_4074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4074_, 0, v___x_4073_);
return v___x_4074_;
}
}
}
}
v___jp_3997_:
{
lean_object* v___x_3998_; lean_object* v___x_3999_; 
v___x_3998_ = lean_box(0);
v___x_3999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3999_, 0, v___x_3998_);
return v___x_3999_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_mkListRemovalSuggestion___redArg___boxed(lean_object* v_whole_4076_, lean_object* v_elems_4077_, lean_object* v_i_4078_, lean_object* v_a_4079_, lean_object* v_a_4080_){
_start:
{
lean_object* v_res_4081_; 
v_res_4081_ = l_Lean_Linter_mkListRemovalSuggestion___redArg(v_whole_4076_, v_elems_4077_, v_i_4078_, v_a_4079_);
lean_dec_ref(v_a_4079_);
lean_dec(v_i_4078_);
return v_res_4081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_mkListRemovalSuggestion(lean_object* v_whole_4082_, lean_object* v_elems_4083_, lean_object* v_i_4084_, lean_object* v_a_4085_, lean_object* v_a_4086_){
_start:
{
lean_object* v___x_4088_; 
v___x_4088_ = l_Lean_Linter_mkListRemovalSuggestion___redArg(v_whole_4082_, v_elems_4083_, v_i_4084_, v_a_4085_);
return v___x_4088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_mkListRemovalSuggestion___boxed(lean_object* v_whole_4089_, lean_object* v_elems_4090_, lean_object* v_i_4091_, lean_object* v_a_4092_, lean_object* v_a_4093_, lean_object* v_a_4094_){
_start:
{
lean_object* v_res_4095_; 
v_res_4095_ = l_Lean_Linter_mkListRemovalSuggestion(v_whole_4089_, v_elems_4090_, v_i_4091_, v_a_4092_, v_a_4093_);
lean_dec(v_a_4093_);
lean_dec_ref(v_a_4092_);
lean_dec(v_i_4091_);
return v_res_4095_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_ownerType_x3f_spec__0(lean_object* v_declName_4096_, lean_object* v_as_4097_, size_t v_i_4098_, size_t v_stop_4099_){
_start:
{
uint8_t v___x_4100_; 
v___x_4100_ = lean_usize_dec_eq(v_i_4098_, v_stop_4099_);
if (v___x_4100_ == 0)
{
lean_object* v___x_4101_; lean_object* v_projFn_4102_; uint8_t v___x_4103_; 
v___x_4101_ = lean_array_uget_borrowed(v_as_4097_, v_i_4098_);
v_projFn_4102_ = lean_ctor_get(v___x_4101_, 1);
v___x_4103_ = lean_name_eq(v_projFn_4102_, v_declName_4096_);
if (v___x_4103_ == 0)
{
size_t v___x_4104_; size_t v___x_4105_; 
v___x_4104_ = ((size_t)1ULL);
v___x_4105_ = lean_usize_add(v_i_4098_, v___x_4104_);
v_i_4098_ = v___x_4105_;
goto _start;
}
else
{
return v___x_4103_;
}
}
else
{
uint8_t v___x_4107_; 
v___x_4107_ = 0;
return v___x_4107_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_ownerType_x3f_spec__0___boxed(lean_object* v_declName_4108_, lean_object* v_as_4109_, lean_object* v_i_4110_, lean_object* v_stop_4111_){
_start:
{
size_t v_i_boxed_4112_; size_t v_stop_boxed_4113_; uint8_t v_res_4114_; lean_object* v_r_4115_; 
v_i_boxed_4112_ = lean_unbox_usize(v_i_4110_);
lean_dec(v_i_4110_);
v_stop_boxed_4113_ = lean_unbox_usize(v_stop_4111_);
lean_dec(v_stop_4111_);
v_res_4114_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_ownerType_x3f_spec__0(v_declName_4108_, v_as_4109_, v_i_boxed_4112_, v_stop_boxed_4113_);
lean_dec_ref(v_as_4109_);
lean_dec(v_declName_4108_);
v_r_4115_ = lean_box(v_res_4114_);
return v_r_4115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_ownerType_x3f(lean_object* v_env_4116_, lean_object* v_declName_4117_){
_start:
{
lean_object* v___y_4141_; lean_object* v___x_4158_; 
lean_inc(v_declName_4117_);
lean_inc_ref(v_env_4116_);
v___x_4158_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_4116_, v_declName_4117_);
if (lean_obj_tag(v___x_4158_) == 0)
{
lean_inc(v_declName_4117_);
v___y_4141_ = v_declName_4117_;
goto v___jp_4140_;
}
else
{
lean_object* v_val_4159_; lean_object* v_ctorName_4160_; 
v_val_4159_ = lean_ctor_get(v___x_4158_, 0);
lean_inc(v_val_4159_);
lean_dec_ref_known(v___x_4158_, 1);
v_ctorName_4160_ = lean_ctor_get(v_val_4159_, 0);
lean_inc(v_ctorName_4160_);
lean_dec(v_val_4159_);
v___y_4141_ = v_ctorName_4160_;
goto v___jp_4140_;
}
v___jp_4118_:
{
lean_object* v_structName_4119_; lean_object* v___x_4120_; 
v_structName_4119_ = l_Lean_Name_getPrefix(v_declName_4117_);
lean_inc(v_structName_4119_);
v___x_4120_ = l_Lean_getStructureInfo_x3f(v_env_4116_, v_structName_4119_);
if (lean_obj_tag(v___x_4120_) == 0)
{
lean_object* v___x_4121_; 
lean_dec(v_structName_4119_);
lean_dec(v_declName_4117_);
v___x_4121_ = lean_box(0);
return v___x_4121_;
}
else
{
lean_object* v_val_4122_; lean_object* v___x_4124_; uint8_t v_isShared_4125_; uint8_t v_isSharedCheck_4139_; 
v_val_4122_ = lean_ctor_get(v___x_4120_, 0);
v_isSharedCheck_4139_ = !lean_is_exclusive(v___x_4120_);
if (v_isSharedCheck_4139_ == 0)
{
v___x_4124_ = v___x_4120_;
v_isShared_4125_ = v_isSharedCheck_4139_;
goto v_resetjp_4123_;
}
else
{
lean_inc(v_val_4122_);
lean_dec(v___x_4120_);
v___x_4124_ = lean_box(0);
v_isShared_4125_ = v_isSharedCheck_4139_;
goto v_resetjp_4123_;
}
v_resetjp_4123_:
{
lean_object* v_parentInfo_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; uint8_t v___x_4129_; 
v_parentInfo_4126_ = lean_ctor_get(v_val_4122_, 3);
lean_inc_ref(v_parentInfo_4126_);
lean_dec(v_val_4122_);
v___x_4127_ = lean_unsigned_to_nat(0u);
v___x_4128_ = lean_array_get_size(v_parentInfo_4126_);
v___x_4129_ = lean_nat_dec_lt(v___x_4127_, v___x_4128_);
if (v___x_4129_ == 0)
{
lean_object* v___x_4130_; 
lean_dec_ref(v_parentInfo_4126_);
lean_del_object(v___x_4124_);
lean_dec(v_structName_4119_);
lean_dec(v_declName_4117_);
v___x_4130_ = lean_box(0);
return v___x_4130_;
}
else
{
if (v___x_4129_ == 0)
{
lean_object* v___x_4131_; 
lean_dec_ref(v_parentInfo_4126_);
lean_del_object(v___x_4124_);
lean_dec(v_structName_4119_);
lean_dec(v_declName_4117_);
v___x_4131_ = lean_box(0);
return v___x_4131_;
}
else
{
size_t v___x_4132_; size_t v___x_4133_; uint8_t v___x_4134_; 
v___x_4132_ = ((size_t)0ULL);
v___x_4133_ = lean_usize_of_nat(v___x_4128_);
v___x_4134_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_ownerType_x3f_spec__0(v_declName_4117_, v_parentInfo_4126_, v___x_4132_, v___x_4133_);
lean_dec_ref(v_parentInfo_4126_);
lean_dec(v_declName_4117_);
if (v___x_4134_ == 0)
{
lean_object* v___x_4135_; 
lean_del_object(v___x_4124_);
lean_dec(v_structName_4119_);
v___x_4135_ = lean_box(0);
return v___x_4135_;
}
else
{
lean_object* v___x_4137_; 
if (v_isShared_4125_ == 0)
{
lean_ctor_set(v___x_4124_, 0, v_structName_4119_);
v___x_4137_ = v___x_4124_;
goto v_reusejp_4136_;
}
else
{
lean_object* v_reuseFailAlloc_4138_; 
v_reuseFailAlloc_4138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4138_, 0, v_structName_4119_);
v___x_4137_ = v_reuseFailAlloc_4138_;
goto v_reusejp_4136_;
}
v_reusejp_4136_:
{
return v___x_4137_;
}
}
}
}
}
}
}
v___jp_4140_:
{
uint8_t v___x_4142_; lean_object* v___x_4143_; 
v___x_4142_ = 0;
lean_inc_ref(v_env_4116_);
v___x_4143_ = l_Lean_Environment_findAsync_x3f(v_env_4116_, v___y_4141_, v___x_4142_);
if (lean_obj_tag(v___x_4143_) == 1)
{
lean_object* v_val_4144_; lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4157_; 
v_val_4144_ = lean_ctor_get(v___x_4143_, 0);
v_isSharedCheck_4157_ = !lean_is_exclusive(v___x_4143_);
if (v_isSharedCheck_4157_ == 0)
{
v___x_4146_ = v___x_4143_;
v_isShared_4147_ = v_isSharedCheck_4157_;
goto v_resetjp_4145_;
}
else
{
lean_inc(v_val_4144_);
lean_dec(v___x_4143_);
v___x_4146_ = lean_box(0);
v_isShared_4147_ = v_isSharedCheck_4157_;
goto v_resetjp_4145_;
}
v_resetjp_4145_:
{
uint8_t v_kind_4148_; uint8_t v___x_4149_; uint8_t v___x_4150_; 
v_kind_4148_ = lean_ctor_get_uint8(v_val_4144_, sizeof(void*)*3);
v___x_4149_ = 6;
v___x_4150_ = l_Lean_instBEqConstantKind_beq(v_kind_4148_, v___x_4149_);
if (v___x_4150_ == 0)
{
lean_del_object(v___x_4146_);
lean_dec(v_val_4144_);
goto v___jp_4118_;
}
else
{
lean_object* v___x_4151_; 
v___x_4151_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_4144_);
if (lean_obj_tag(v___x_4151_) == 6)
{
lean_object* v_val_4152_; lean_object* v_induct_4153_; lean_object* v___x_4155_; 
lean_dec(v_declName_4117_);
lean_dec_ref(v_env_4116_);
v_val_4152_ = lean_ctor_get(v___x_4151_, 0);
lean_inc_ref(v_val_4152_);
lean_dec_ref_known(v___x_4151_, 1);
v_induct_4153_ = lean_ctor_get(v_val_4152_, 1);
lean_inc(v_induct_4153_);
lean_dec_ref(v_val_4152_);
if (v_isShared_4147_ == 0)
{
lean_ctor_set(v___x_4146_, 0, v_induct_4153_);
v___x_4155_ = v___x_4146_;
goto v_reusejp_4154_;
}
else
{
lean_object* v_reuseFailAlloc_4156_; 
v_reuseFailAlloc_4156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4156_, 0, v_induct_4153_);
v___x_4155_ = v_reuseFailAlloc_4156_;
goto v_reusejp_4154_;
}
v_reusejp_4154_:
{
return v___x_4155_;
}
}
else
{
lean_dec_ref(v___x_4151_);
lean_del_object(v___x_4146_);
goto v___jp_4118_;
}
}
}
}
else
{
lean_dec(v___x_4143_);
goto v___jp_4118_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_checkDeprecatedAutomationAttr___lam__0(lean_object* v_env_4161_, uint8_t v___x_4162_, lean_object* v_n_4163_){
_start:
{
uint8_t v___x_4164_; 
lean_inc(v_n_4163_);
lean_inc_ref(v_env_4161_);
v___x_4164_ = l_Lean_Linter_isDeprecated(v_env_4161_, v_n_4163_);
if (v___x_4164_ == 0)
{
lean_object* v___x_4165_; 
lean_inc_ref(v_env_4161_);
v___x_4165_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_ownerType_x3f(v_env_4161_, v_n_4163_);
if (lean_obj_tag(v___x_4165_) == 0)
{
lean_dec_ref(v_env_4161_);
return v___x_4164_;
}
else
{
lean_object* v_val_4166_; uint8_t v___x_4167_; 
v_val_4166_ = lean_ctor_get(v___x_4165_, 0);
lean_inc(v_val_4166_);
lean_dec_ref_known(v___x_4165_, 1);
v___x_4167_ = l_Lean_Linter_isDeprecated(v_env_4161_, v_val_4166_);
return v___x_4167_;
}
}
else
{
lean_dec(v_n_4163_);
lean_dec_ref(v_env_4161_);
return v___x_4162_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkDeprecatedAutomationAttr___lam__0___boxed(lean_object* v_env_4168_, lean_object* v___x_4169_, lean_object* v_n_4170_){
_start:
{
uint8_t v___x_3712__boxed_4171_; uint8_t v_res_4172_; lean_object* v_r_4173_; 
v___x_3712__boxed_4171_ = lean_unbox(v___x_4169_);
v_res_4172_ = l_Lean_Linter_checkDeprecatedAutomationAttr___lam__0(v_env_4168_, v___x_3712__boxed_4171_, v_n_4170_);
v_r_4173_ = lean_box(v_res_4172_);
return v_r_4173_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecatedAutomationAttr___closed__1(void){
_start:
{
lean_object* v___x_4175_; lean_object* v___x_4176_; 
v___x_4175_ = ((lean_object*)(l_Lean_Linter_checkDeprecatedAutomationAttr___closed__0));
v___x_4176_ = l_Lean_stringToMessageData(v___x_4175_);
return v___x_4176_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecatedAutomationAttr___closed__3(void){
_start:
{
lean_object* v___x_4178_; lean_object* v___x_4179_; 
v___x_4178_ = ((lean_object*)(l_Lean_Linter_checkDeprecatedAutomationAttr___closed__2));
v___x_4179_ = l_Lean_stringToMessageData(v___x_4178_);
return v___x_4179_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecatedAutomationAttr___closed__5(void){
_start:
{
lean_object* v___x_4181_; lean_object* v___x_4182_; 
v___x_4181_ = ((lean_object*)(l_Lean_Linter_checkDeprecatedAutomationAttr___closed__4));
v___x_4182_ = l_Lean_stringToMessageData(v___x_4181_);
return v___x_4182_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecatedAutomationAttr___closed__7(void){
_start:
{
lean_object* v___x_4184_; lean_object* v___x_4185_; 
v___x_4184_ = ((lean_object*)(l_Lean_Linter_checkDeprecatedAutomationAttr___closed__6));
v___x_4185_ = l_Lean_stringToMessageData(v___x_4184_);
return v___x_4185_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecatedAutomationAttr___closed__9(void){
_start:
{
lean_object* v___x_4187_; lean_object* v___x_4188_; 
v___x_4187_ = ((lean_object*)(l_Lean_Linter_checkDeprecatedAutomationAttr___closed__8));
v___x_4188_ = l_Lean_stringToMessageData(v___x_4187_);
return v___x_4188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkDeprecatedAutomationAttr(lean_object* v_ref_4189_, lean_object* v_declName_4190_, lean_object* v_attrName_4191_, lean_object* v_removal_x3f_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_, lean_object* v_a_4195_, lean_object* v_a_4196_){
_start:
{
lean_object* v_toCold_4198_; lean_object* v_currRecDepth_4199_; lean_object* v_ref_4200_; uint16_t v_optionFlags_4201_; uint8_t v_suppressElabErrors_4202_; uint8_t v_checkDeprecated_4203_; uint8_t v_isRecordingDeps_4204_; lean_object* v_ref_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v_a_4208_; lean_object* v___x_4210_; uint8_t v_isShared_4211_; uint8_t v_isSharedCheck_4308_; 
v_toCold_4198_ = lean_ctor_get(v_a_4195_, 0);
v_currRecDepth_4199_ = lean_ctor_get(v_a_4195_, 1);
v_ref_4200_ = lean_ctor_get(v_a_4195_, 2);
v_optionFlags_4201_ = lean_ctor_get_uint16(v_a_4195_, sizeof(void*)*3);
v_suppressElabErrors_4202_ = lean_ctor_get_uint8(v_a_4195_, sizeof(void*)*3 + 2);
v_checkDeprecated_4203_ = lean_ctor_get_uint8(v_a_4195_, sizeof(void*)*3 + 3);
v_isRecordingDeps_4204_ = lean_ctor_get_uint8(v_a_4195_, sizeof(void*)*3 + 4);
v_ref_4205_ = l_Lean_replaceRef(v_ref_4189_, v_ref_4200_);
lean_inc(v_currRecDepth_4199_);
lean_inc_ref(v_toCold_4198_);
v___x_4206_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_4206_, 0, v_toCold_4198_);
lean_ctor_set(v___x_4206_, 1, v_currRecDepth_4199_);
lean_ctor_set(v___x_4206_, 2, v_ref_4205_);
lean_ctor_set_uint16(v___x_4206_, sizeof(void*)*3, v_optionFlags_4201_);
lean_ctor_set_uint8(v___x_4206_, sizeof(void*)*3 + 2, v_suppressElabErrors_4202_);
lean_ctor_set_uint8(v___x_4206_, sizeof(void*)*3 + 3, v_checkDeprecated_4203_);
lean_ctor_set_uint8(v___x_4206_, sizeof(void*)*3 + 4, v_isRecordingDeps_4204_);
v___x_4207_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0(v_a_4193_, v_a_4194_, v___x_4206_, v_a_4196_);
v_a_4208_ = lean_ctor_get(v___x_4207_, 0);
v_isSharedCheck_4308_ = !lean_is_exclusive(v___x_4207_);
if (v_isSharedCheck_4308_ == 0)
{
v___x_4210_ = v___x_4207_;
v_isShared_4211_ = v_isSharedCheck_4308_;
goto v_resetjp_4209_;
}
else
{
lean_inc(v_a_4208_);
lean_dec(v___x_4207_);
v___x_4210_ = lean_box(0);
v_isShared_4211_ = v_isSharedCheck_4308_;
goto v_resetjp_4209_;
}
v_resetjp_4209_:
{
lean_object* v___x_4212_; uint8_t v___x_4213_; 
v___x_4212_ = l_Lean_Linter_linter_deprecated;
v___x_4213_ = l_Lean_Linter_getLinterValue(v___x_4212_, v_a_4208_);
lean_dec(v_a_4208_);
if (v___x_4213_ == 0)
{
lean_object* v___x_4214_; lean_object* v___x_4216_; 
lean_dec_ref_known(v___x_4206_, 3);
lean_dec(v_removal_x3f_4192_);
lean_dec(v_attrName_4191_);
lean_dec(v_declName_4190_);
lean_dec(v_ref_4189_);
v___x_4214_ = lean_box(0);
if (v_isShared_4211_ == 0)
{
lean_ctor_set(v___x_4210_, 0, v___x_4214_);
v___x_4216_ = v___x_4210_;
goto v_reusejp_4215_;
}
else
{
lean_object* v_reuseFailAlloc_4217_; 
v_reuseFailAlloc_4217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4217_, 0, v___x_4214_);
v___x_4216_ = v_reuseFailAlloc_4217_;
goto v_reusejp_4215_;
}
v_reusejp_4215_:
{
return v___x_4216_;
}
}
else
{
lean_object* v___x_4218_; lean_object* v___x_4219_; uint8_t v___x_4220_; lean_object* v_hint_4222_; lean_object* v___y_4223_; lean_object* v___y_4224_; lean_object* v___y_4225_; lean_object* v___y_4226_; uint8_t v_a_4247_; 
v___x_4218_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___x_4206_);
v___x_4219_ = l_Lean_Linter_linter_deprecated_automationAttr;
v___x_4220_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__5(v___x_4218_, v___x_4219_);
lean_dec_ref(v___x_4218_);
if (v___x_4220_ == 0)
{
lean_object* v___x_4265_; lean_object* v___x_4267_; 
lean_dec_ref_known(v___x_4206_, 3);
lean_dec(v_removal_x3f_4192_);
lean_dec(v_attrName_4191_);
lean_dec(v_declName_4190_);
lean_dec(v_ref_4189_);
v___x_4265_ = lean_box(0);
if (v_isShared_4211_ == 0)
{
lean_ctor_set(v___x_4210_, 0, v___x_4265_);
v___x_4267_ = v___x_4210_;
goto v_reusejp_4266_;
}
else
{
lean_object* v_reuseFailAlloc_4268_; 
v_reuseFailAlloc_4268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4268_, 0, v___x_4265_);
v___x_4267_ = v_reuseFailAlloc_4268_;
goto v_reusejp_4266_;
}
v_reusejp_4266_:
{
return v___x_4267_;
}
}
else
{
lean_object* v___x_4269_; 
v___x_4269_ = l_Lean_Syntax_getHeadInfo(v_ref_4189_);
if (lean_obj_tag(v___x_4269_) == 0)
{
lean_object* v___x_4270_; lean_object* v_env_4271_; uint8_t v___x_4272_; 
lean_dec_ref_known(v___x_4269_, 4);
v___x_4270_ = lean_st_ref_get(v_a_4196_);
v_env_4271_ = lean_ctor_get(v___x_4270_, 0);
lean_inc_ref_n(v_env_4271_, 2);
lean_dec(v___x_4270_);
lean_inc(v_declName_4190_);
v___x_4272_ = l_Lean_Linter_isDeprecated(v_env_4271_, v_declName_4190_);
if (v___x_4272_ == 0)
{
lean_object* v___x_4273_; lean_object* v___x_4275_; 
lean_dec_ref(v_env_4271_);
lean_dec_ref_known(v___x_4206_, 3);
lean_dec(v_removal_x3f_4192_);
lean_dec(v_attrName_4191_);
lean_dec(v_declName_4190_);
lean_dec(v_ref_4189_);
v___x_4273_ = lean_box(0);
if (v_isShared_4211_ == 0)
{
lean_ctor_set(v___x_4210_, 0, v___x_4273_);
v___x_4275_ = v___x_4210_;
goto v_reusejp_4274_;
}
else
{
lean_object* v_reuseFailAlloc_4276_; 
v_reuseFailAlloc_4276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4276_, 0, v___x_4273_);
v___x_4275_ = v_reuseFailAlloc_4276_;
goto v_reusejp_4274_;
}
v_reusejp_4274_:
{
return v___x_4275_;
}
}
else
{
lean_object* v___x_4277_; lean_object* v___f_4278_; lean_object* v___x_4279_; 
lean_del_object(v___x_4210_);
v___x_4277_ = lean_box(v___x_4220_);
v___f_4278_ = lean_alloc_closure((void*)(l_Lean_Linter_checkDeprecatedAutomationAttr___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4278_, 0, v_env_4271_);
lean_closure_set(v___f_4278_, 1, v___x_4277_);
lean_inc(v_declName_4190_);
v___x_4279_ = l_Lean_isAutomationAttrGuardedBy(v_attrName_4191_, v___f_4278_, v_declName_4190_, v_ref_4189_, v___x_4206_, v_a_4196_);
if (lean_obj_tag(v___x_4279_) == 0)
{
lean_object* v_a_4280_; lean_object* v___x_4282_; uint8_t v_isShared_4283_; uint8_t v_isSharedCheck_4290_; 
v_a_4280_ = lean_ctor_get(v___x_4279_, 0);
v_isSharedCheck_4290_ = !lean_is_exclusive(v___x_4279_);
if (v_isSharedCheck_4290_ == 0)
{
v___x_4282_ = v___x_4279_;
v_isShared_4283_ = v_isSharedCheck_4290_;
goto v_resetjp_4281_;
}
else
{
lean_inc(v_a_4280_);
lean_dec(v___x_4279_);
v___x_4282_ = lean_box(0);
v_isShared_4283_ = v_isSharedCheck_4290_;
goto v_resetjp_4281_;
}
v_resetjp_4281_:
{
uint8_t v___x_4284_; 
v___x_4284_ = lean_unbox(v_a_4280_);
if (v___x_4284_ == 0)
{
uint8_t v___x_4285_; 
lean_del_object(v___x_4282_);
v___x_4285_ = lean_unbox(v_a_4280_);
lean_dec(v_a_4280_);
v_a_4247_ = v___x_4285_;
goto v___jp_4246_;
}
else
{
lean_object* v___x_4286_; lean_object* v___x_4288_; 
lean_dec(v_a_4280_);
lean_dec_ref_known(v___x_4206_, 3);
lean_dec(v_removal_x3f_4192_);
lean_dec(v_attrName_4191_);
lean_dec(v_declName_4190_);
v___x_4286_ = lean_box(0);
if (v_isShared_4283_ == 0)
{
lean_ctor_set(v___x_4282_, 0, v___x_4286_);
v___x_4288_ = v___x_4282_;
goto v_reusejp_4287_;
}
else
{
lean_object* v_reuseFailAlloc_4289_; 
v_reuseFailAlloc_4289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4289_, 0, v___x_4286_);
v___x_4288_ = v_reuseFailAlloc_4289_;
goto v_reusejp_4287_;
}
v_reusejp_4287_:
{
return v___x_4288_;
}
}
}
}
else
{
lean_object* v_a_4291_; lean_object* v___x_4293_; uint8_t v_isShared_4294_; uint8_t v_isSharedCheck_4303_; 
v_a_4291_ = lean_ctor_get(v___x_4279_, 0);
v_isSharedCheck_4303_ = !lean_is_exclusive(v___x_4279_);
if (v_isSharedCheck_4303_ == 0)
{
v___x_4293_ = v___x_4279_;
v_isShared_4294_ = v_isSharedCheck_4303_;
goto v_resetjp_4292_;
}
else
{
lean_inc(v_a_4291_);
lean_dec(v___x_4279_);
v___x_4293_ = lean_box(0);
v_isShared_4294_ = v_isSharedCheck_4303_;
goto v_resetjp_4292_;
}
v_resetjp_4292_:
{
uint8_t v___x_4295_; 
v___x_4295_ = l_Lean_Exception_isInterrupt(v_a_4291_);
if (v___x_4295_ == 0)
{
uint8_t v___x_4296_; 
lean_inc(v_a_4291_);
v___x_4296_ = l_Lean_Exception_isRuntime(v_a_4291_);
if (v___x_4296_ == 0)
{
lean_del_object(v___x_4293_);
lean_dec(v_a_4291_);
v_a_4247_ = v___x_4296_;
goto v___jp_4246_;
}
else
{
lean_object* v___x_4298_; 
lean_dec_ref_known(v___x_4206_, 3);
lean_dec(v_removal_x3f_4192_);
lean_dec(v_attrName_4191_);
lean_dec(v_declName_4190_);
if (v_isShared_4294_ == 0)
{
v___x_4298_ = v___x_4293_;
goto v_reusejp_4297_;
}
else
{
lean_object* v_reuseFailAlloc_4299_; 
v_reuseFailAlloc_4299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4299_, 0, v_a_4291_);
v___x_4298_ = v_reuseFailAlloc_4299_;
goto v_reusejp_4297_;
}
v_reusejp_4297_:
{
return v___x_4298_;
}
}
}
else
{
lean_object* v___x_4301_; 
lean_dec_ref_known(v___x_4206_, 3);
lean_dec(v_removal_x3f_4192_);
lean_dec(v_attrName_4191_);
lean_dec(v_declName_4190_);
if (v_isShared_4294_ == 0)
{
v___x_4301_ = v___x_4293_;
goto v_reusejp_4300_;
}
else
{
lean_object* v_reuseFailAlloc_4302_; 
v_reuseFailAlloc_4302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4302_, 0, v_a_4291_);
v___x_4301_ = v_reuseFailAlloc_4302_;
goto v_reusejp_4300_;
}
v_reusejp_4300_:
{
return v___x_4301_;
}
}
}
}
}
}
else
{
lean_object* v___x_4304_; lean_object* v___x_4306_; 
lean_dec(v___x_4269_);
lean_dec_ref_known(v___x_4206_, 3);
lean_dec(v_removal_x3f_4192_);
lean_dec(v_attrName_4191_);
lean_dec(v_declName_4190_);
lean_dec(v_ref_4189_);
v___x_4304_ = lean_box(0);
if (v_isShared_4211_ == 0)
{
lean_ctor_set(v___x_4210_, 0, v___x_4304_);
v___x_4306_ = v___x_4210_;
goto v_reusejp_4305_;
}
else
{
lean_object* v_reuseFailAlloc_4307_; 
v_reuseFailAlloc_4307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4307_, 0, v___x_4304_);
v___x_4306_ = v_reuseFailAlloc_4307_;
goto v_reusejp_4305_;
}
v_reusejp_4305_:
{
return v___x_4306_;
}
}
}
v___jp_4221_:
{
lean_object* v_name_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; 
v_name_4227_ = lean_ctor_get(v___x_4219_, 0);
v___x_4228_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_4229_ = l_Lean_MessageData_ofConstName(v_declName_4190_, v___x_4220_);
v___x_4230_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4230_, 0, v___x_4228_);
lean_ctor_set(v___x_4230_, 1, v___x_4229_);
v___x_4231_ = lean_obj_once(&l_Lean_Linter_checkDeprecatedAutomationAttr___closed__1, &l_Lean_Linter_checkDeprecatedAutomationAttr___closed__1_once, _init_l_Lean_Linter_checkDeprecatedAutomationAttr___closed__1);
v___x_4232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4232_, 0, v___x_4230_);
lean_ctor_set(v___x_4232_, 1, v___x_4231_);
v___x_4233_ = l_Lean_MessageData_ofName(v_attrName_4191_);
v___x_4234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4234_, 0, v___x_4232_);
lean_ctor_set(v___x_4234_, 1, v___x_4233_);
v___x_4235_ = lean_obj_once(&l_Lean_Linter_checkDeprecatedAutomationAttr___closed__3, &l_Lean_Linter_checkDeprecatedAutomationAttr___closed__3_once, _init_l_Lean_Linter_checkDeprecatedAutomationAttr___closed__3);
v___x_4236_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4236_, 0, v___x_4234_);
lean_ctor_set(v___x_4236_, 1, v___x_4235_);
v___x_4237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4237_, 0, v___x_4236_);
lean_ctor_set(v___x_4237_, 1, v_hint_4222_);
v___x_4238_ = lean_obj_once(&l_Lean_Linter_checkDeprecatedAutomationAttr___closed__5, &l_Lean_Linter_checkDeprecatedAutomationAttr___closed__5_once, _init_l_Lean_Linter_checkDeprecatedAutomationAttr___closed__5);
lean_inc(v_name_4227_);
v___x_4239_ = l_Lean_MessageData_ofName(v_name_4227_);
v___x_4240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4240_, 0, v___x_4238_);
lean_ctor_set(v___x_4240_, 1, v___x_4239_);
v___x_4241_ = lean_obj_once(&l_Lean_Linter_checkDeprecatedAutomationAttr___closed__7, &l_Lean_Linter_checkDeprecatedAutomationAttr___closed__7_once, _init_l_Lean_Linter_checkDeprecatedAutomationAttr___closed__7);
v___x_4242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4242_, 0, v___x_4240_);
lean_ctor_set(v___x_4242_, 1, v___x_4241_);
v___x_4243_ = l_Lean_MessageData_note(v___x_4242_);
v___x_4244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4244_, 0, v___x_4237_);
lean_ctor_set(v___x_4244_, 1, v___x_4243_);
v___x_4245_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40(v___x_4244_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_);
lean_dec_ref(v___y_4225_);
return v___x_4245_;
}
v___jp_4246_:
{
if (lean_obj_tag(v_removal_x3f_4192_) == 0)
{
lean_object* v___x_4248_; 
v___x_4248_ = l_Lean_MessageData_nil;
v_hint_4222_ = v___x_4248_;
v___y_4223_ = v_a_4193_;
v___y_4224_ = v_a_4194_;
v___y_4225_ = v___x_4206_;
v___y_4226_ = v_a_4196_;
goto v___jp_4221_;
}
else
{
lean_object* v_val_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; 
v_val_4249_ = lean_ctor_get(v_removal_x3f_4192_, 0);
lean_inc(v_val_4249_);
lean_dec_ref_known(v_removal_x3f_4192_, 1);
v___x_4250_ = lean_obj_once(&l_Lean_Linter_checkDeprecatedAutomationAttr___closed__9, &l_Lean_Linter_checkDeprecatedAutomationAttr___closed__9_once, _init_l_Lean_Linter_checkDeprecatedAutomationAttr___closed__9);
v___x_4251_ = lean_unsigned_to_nat(1u);
v___x_4252_ = lean_mk_empty_array_with_capacity(v___x_4251_);
v___x_4253_ = lean_array_push(v___x_4252_, v_val_4249_);
v___x_4254_ = lean_box(0);
v___x_4255_ = l_Lean_MessageData_hint(v___x_4250_, v___x_4253_, v___x_4254_, v___x_4254_, v_a_4247_, v___x_4206_, v_a_4196_);
lean_dec_ref(v___x_4253_);
if (lean_obj_tag(v___x_4255_) == 0)
{
lean_object* v_a_4256_; 
v_a_4256_ = lean_ctor_get(v___x_4255_, 0);
lean_inc(v_a_4256_);
lean_dec_ref_known(v___x_4255_, 1);
v_hint_4222_ = v_a_4256_;
v___y_4223_ = v_a_4193_;
v___y_4224_ = v_a_4194_;
v___y_4225_ = v___x_4206_;
v___y_4226_ = v_a_4196_;
goto v___jp_4221_;
}
else
{
lean_object* v_a_4257_; lean_object* v___x_4259_; uint8_t v_isShared_4260_; uint8_t v_isSharedCheck_4264_; 
lean_dec_ref_known(v___x_4206_, 3);
lean_dec(v_attrName_4191_);
lean_dec(v_declName_4190_);
v_a_4257_ = lean_ctor_get(v___x_4255_, 0);
v_isSharedCheck_4264_ = !lean_is_exclusive(v___x_4255_);
if (v_isSharedCheck_4264_ == 0)
{
v___x_4259_ = v___x_4255_;
v_isShared_4260_ = v_isSharedCheck_4264_;
goto v_resetjp_4258_;
}
else
{
lean_inc(v_a_4257_);
lean_dec(v___x_4255_);
v___x_4259_ = lean_box(0);
v_isShared_4260_ = v_isSharedCheck_4264_;
goto v_resetjp_4258_;
}
v_resetjp_4258_:
{
lean_object* v___x_4262_; 
if (v_isShared_4260_ == 0)
{
v___x_4262_ = v___x_4259_;
goto v_reusejp_4261_;
}
else
{
lean_object* v_reuseFailAlloc_4263_; 
v_reuseFailAlloc_4263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4263_, 0, v_a_4257_);
v___x_4262_ = v_reuseFailAlloc_4263_;
goto v_reusejp_4261_;
}
v_reusejp_4261_:
{
return v___x_4262_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkDeprecatedAutomationAttr___boxed(lean_object* v_ref_4309_, lean_object* v_declName_4310_, lean_object* v_attrName_4311_, lean_object* v_removal_x3f_4312_, lean_object* v_a_4313_, lean_object* v_a_4314_, lean_object* v_a_4315_, lean_object* v_a_4316_, lean_object* v_a_4317_){
_start:
{
lean_object* v_res_4318_; 
v_res_4318_ = l_Lean_Linter_checkDeprecatedAutomationAttr(v_ref_4309_, v_declName_4310_, v_attrName_4311_, v_removal_x3f_4312_, v_a_4313_, v_a_4314_, v_a_4315_, v_a_4316_);
lean_dec(v_a_4316_);
lean_dec_ref(v_a_4315_);
lean_dec(v_a_4314_);
lean_dec_ref(v_a_4313_);
return v_res_4318_;
}
}
static uint64_t _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4325_; uint64_t v___x_4326_; 
v___x_4325_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2_));
v___x_4326_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4325_);
return v___x_4326_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; 
v___x_4327_ = lean_uint64_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2_);
v___x_4328_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2_));
v___x_4329_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4329_, 0, v___x_4328_);
lean_ctor_set_uint64(v___x_4329_, sizeof(void*)*1, v___x_4327_);
return v___x_4329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2_(lean_object* v___x_4330_, lean_object* v_ref_4331_, lean_object* v_declName_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_){
_start:
{
lean_object* v___x_4336_; uint8_t v___x_4337_; uint8_t v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; 
v___x_4336_ = lean_box(1);
v___x_4337_ = 0;
v___x_4338_ = 1;
v___x_4339_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2_);
v___x_4340_ = lean_unsigned_to_nat(0u);
v___x_4341_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_4342_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__27_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__27_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__27_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_4343_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__28_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_4344_ = lean_box(0);
lean_inc(v___x_4330_);
v___x_4345_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4345_, 0, v___x_4339_);
lean_ctor_set(v___x_4345_, 1, v___x_4330_);
lean_ctor_set(v___x_4345_, 2, v___x_4342_);
lean_ctor_set(v___x_4345_, 3, v___x_4343_);
lean_ctor_set(v___x_4345_, 4, v___x_4344_);
lean_ctor_set(v___x_4345_, 5, v___x_4340_);
lean_ctor_set(v___x_4345_, 6, v___x_4344_);
lean_ctor_set_uint8(v___x_4345_, sizeof(void*)*7, v___x_4337_);
lean_ctor_set_uint8(v___x_4345_, sizeof(void*)*7 + 1, v___x_4337_);
lean_ctor_set_uint8(v___x_4345_, sizeof(void*)*7 + 2, v___x_4337_);
lean_ctor_set_uint8(v___x_4345_, sizeof(void*)*7 + 3, v___x_4338_);
v___x_4346_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_4347_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_4348_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_4349_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4349_, 0, v___x_4346_);
lean_ctor_set(v___x_4349_, 1, v___x_4347_);
lean_ctor_set(v___x_4349_, 2, v___x_4330_);
lean_ctor_set(v___x_4349_, 3, v___x_4341_);
lean_ctor_set(v___x_4349_, 4, v___x_4348_);
v___x_4350_ = lean_st_mk_ref(v___x_4349_);
v___x_4351_ = l_Lean_Linter_checkDeprecatedAt(v_ref_4331_, v_declName_4332_, v___x_4336_, v___x_4345_, v___x_4350_, v___y_4333_, v___y_4334_);
lean_dec_ref_known(v___x_4345_, 7);
if (lean_obj_tag(v___x_4351_) == 0)
{
lean_object* v_a_4352_; lean_object* v___x_4354_; uint8_t v_isShared_4355_; uint8_t v_isSharedCheck_4360_; 
v_a_4352_ = lean_ctor_get(v___x_4351_, 0);
v_isSharedCheck_4360_ = !lean_is_exclusive(v___x_4351_);
if (v_isSharedCheck_4360_ == 0)
{
v___x_4354_ = v___x_4351_;
v_isShared_4355_ = v_isSharedCheck_4360_;
goto v_resetjp_4353_;
}
else
{
lean_inc(v_a_4352_);
lean_dec(v___x_4351_);
v___x_4354_ = lean_box(0);
v_isShared_4355_ = v_isSharedCheck_4360_;
goto v_resetjp_4353_;
}
v_resetjp_4353_:
{
lean_object* v___x_4356_; lean_object* v___x_4358_; 
v___x_4356_ = lean_st_ref_get(v___x_4350_);
lean_dec(v___x_4350_);
lean_dec(v___x_4356_);
if (v_isShared_4355_ == 0)
{
v___x_4358_ = v___x_4354_;
goto v_reusejp_4357_;
}
else
{
lean_object* v_reuseFailAlloc_4359_; 
v_reuseFailAlloc_4359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4359_, 0, v_a_4352_);
v___x_4358_ = v_reuseFailAlloc_4359_;
goto v_reusejp_4357_;
}
v_reusejp_4357_:
{
return v___x_4358_;
}
}
}
else
{
lean_dec(v___x_4350_);
return v___x_4351_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2____boxed(lean_object* v___x_4361_, lean_object* v_ref_4362_, lean_object* v_declName_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_){
_start:
{
lean_object* v_res_4367_; 
v_res_4367_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2_(v___x_4361_, v_ref_4362_, v_declName_4363_, v___y_4364_, v___y_4365_);
lean_dec(v___y_4365_);
lean_dec_ref(v___y_4364_);
lean_dec(v_ref_4362_);
return v_res_4367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; 
v___f_4371_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2_));
v___x_4372_ = l_Lean_Core_checkDeprecatedAtRef;
v___x_4373_ = lean_box(0);
v___x_4374_ = lean_st_ref_swap(v___x_4372_, v___f_4371_);
lean_dec(v___x_4374_);
v___x_4375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4375_, 0, v___x_4373_);
return v___x_4375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2____boxed(lean_object* v_a_4376_){
_start:
{
lean_object* v_res_4377_; 
v_res_4377_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2_();
return v_res_4377_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Init(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_InfoTree_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_ExtraModUses(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Hint(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_MapIdx(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Format(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Zoned(uint8_t builtin);
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
res = runtime_initialize_Std_Time_Format(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Zoned(builtin);
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
res = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_448960154____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_linter_deprecated_automationAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_linter_deprecated_automationAttr);
lean_dec_ref(res);
res = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_deprecatedAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_deprecatedAttr);
lean_dec_ref(res);
res = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
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
lean_object* initialize_Std_Time_Format(uint8_t builtin);
lean_object* initialize_Std_Time_Zoned(uint8_t builtin);
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
res = initialize_Std_Time_Format(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Zoned(builtin);
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
