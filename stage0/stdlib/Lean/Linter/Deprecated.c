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
lean_object* l_Lean_Name_componentsRev(lean_object*);
lean_object* l_Lean_Name_appendCore(lean_object*, lean_object*);
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
lean_object* l_List_get___redArg(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_ParametricAttribute_setParam___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___redArg(lean_object*, lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
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
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Try this: +typeChanged"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24_spec__32___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24_spec__32___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "deprecatedAttr"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(85, 246, 23, 143, 159, 138, 155, 162)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(78, 182, 79, 155, 204, 118, 39, 140)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "mark declaration as deprecated"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24_spec__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24_spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Linter_checkDeprecated___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = " (e.g., from `x."};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__14 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__14_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__15;
static const lean_string_object l_Lean_Linter_checkDeprecated___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "` to `"};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__16 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__16_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__17;
static const lean_string_object l_Lean_Linter_checkDeprecated___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " x`)"};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__18 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__18_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__19;
static const lean_ctor_object l_Lean_Linter_checkDeprecated___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__1_value)}};
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
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
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
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(lean_object* v_x_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2____boxed(lean_object* v_x_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(v_x_391_);
lean_dec_ref(v_x_391_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(lean_object* v_x_393_, lean_object* v_x_394_, lean_object* v_x_395_, lean_object* v___y_396_){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_398_ = lean_box(0);
v___x_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2____boxed(lean_object* v_x_400_, lean_object* v_x_401_, lean_object* v_x_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(v_x_400_, v_x_401_, v_x_402_, v___y_403_);
lean_dec(v___y_403_);
lean_dec_ref(v_x_402_);
lean_dec_ref(v_x_401_);
lean_dec(v_x_400_);
return v_res_405_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(uint8_t v___x_406_, lean_object* v_env_407_, lean_object* v_n_408_, lean_object* v_x_409_){
_start:
{
uint8_t v___x_410_; 
v___x_410_ = l_Lean_Environment_contains(v_env_407_, v_n_408_, v___x_406_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2____boxed(lean_object* v___x_411_, lean_object* v_env_412_, lean_object* v_n_413_, lean_object* v_x_414_){
_start:
{
uint8_t v___x_44842__boxed_415_; uint8_t v_res_416_; lean_object* v_r_417_; 
v___x_44842__boxed_415_ = lean_unbox(v___x_411_);
v_res_416_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(v___x_44842__boxed_415_, v_env_412_, v_n_413_, v_x_414_);
lean_dec_ref(v_x_414_);
v_r_417_ = lean_box(v_res_416_);
return v_r_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__3_spec__8___redArg(lean_object* v_o_418_, lean_object* v___y_419_){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v_env_423_; lean_object* v___x_424_; lean_object* v_toEnvExtension_425_; lean_object* v_asyncMode_426_; lean_object* v___x_427_; uint8_t v___x_428_; lean_object* v___x_429_; lean_object* v_merged_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_438_; 
v___x_421_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_422_ = lean_st_ref_get(v___y_419_);
v_env_423_ = lean_ctor_get(v___x_422_, 0);
lean_inc_ref(v_env_423_);
lean_dec(v___x_422_);
v___x_424_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_425_ = lean_ctor_get(v___x_424_, 0);
v_asyncMode_426_ = lean_ctor_get(v_toEnvExtension_425_, 2);
v___x_427_ = lean_box(0);
v___x_428_ = 0;
v___x_429_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_421_, v___x_424_, v_env_423_, v_asyncMode_426_, v___x_427_, v___x_428_);
v_merged_430_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_438_ == 0)
{
lean_object* v_unused_439_; 
v_unused_439_ = lean_ctor_get(v___x_429_, 1);
lean_dec(v_unused_439_);
v___x_432_ = v___x_429_;
v_isShared_433_ = v_isSharedCheck_438_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_merged_430_);
lean_dec(v___x_429_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_438_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_435_; 
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 1, v_merged_430_);
lean_ctor_set(v___x_432_, 0, v_o_418_);
v___x_435_ = v___x_432_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_o_418_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v_merged_430_);
v___x_435_ = v_reuseFailAlloc_437_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
lean_object* v___x_436_; 
v___x_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
return v___x_436_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__3_spec__8___redArg___boxed(lean_object* v_o_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__3_spec__8___redArg(v_o_440_, v___y_441_);
lean_dec(v___y_441_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__3(lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_444_);
v___x_448_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__3_spec__8___redArg(v___x_447_, v___y_445_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__3___boxed(lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__3(v___y_449_, v___y_450_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
return v_res_452_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_453_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_454_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
return v___x_455_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_456_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_457_ = lean_unsigned_to_nat(0u);
v___x_458_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
lean_ctor_set(v___x_458_, 1, v___x_457_);
lean_ctor_set(v___x_458_, 2, v___x_457_);
lean_ctor_set(v___x_458_, 3, v___x_457_);
lean_ctor_set(v___x_458_, 4, v___x_456_);
lean_ctor_set(v___x_458_, 5, v___x_456_);
lean_ctor_set(v___x_458_, 6, v___x_456_);
lean_ctor_set(v___x_458_, 7, v___x_456_);
lean_ctor_set(v___x_458_, 8, v___x_456_);
lean_ctor_set(v___x_458_, 9, v___x_456_);
lean_ctor_set(v___x_458_, 10, v___x_456_);
return v___x_458_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_459_ = lean_unsigned_to_nat(32u);
v___x_460_ = lean_mk_empty_array_with_capacity(v___x_459_);
v___x_461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
return v___x_461_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_462_ = ((size_t)5ULL);
v___x_463_ = lean_unsigned_to_nat(0u);
v___x_464_ = lean_unsigned_to_nat(32u);
v___x_465_ = lean_mk_empty_array_with_capacity(v___x_464_);
v___x_466_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_467_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_467_, 0, v___x_466_);
lean_ctor_set(v___x_467_, 1, v___x_465_);
lean_ctor_set(v___x_467_, 2, v___x_463_);
lean_ctor_set(v___x_467_, 3, v___x_463_);
lean_ctor_set_usize(v___x_467_, 4, v___x_462_);
return v___x_467_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_468_ = lean_box(1);
v___x_469_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_470_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_471_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
lean_ctor_set(v___x_471_, 1, v___x_469_);
lean_ctor_set(v___x_471_, 2, v___x_468_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_472_, lean_object* v___y_473_, lean_object* v___y_474_){
_start:
{
lean_object* v___x_476_; lean_object* v_toCold_477_; lean_object* v_env_478_; lean_object* v_options_479_; uint8_t v___x_480_; lean_object* v_env_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_476_ = lean_st_ref_get(v___y_474_);
v_toCold_477_ = lean_ctor_get(v___y_473_, 0);
v_env_478_ = lean_ctor_get(v___x_476_, 0);
lean_inc_ref(v_env_478_);
lean_dec(v___x_476_);
v_options_479_ = lean_ctor_get(v_toCold_477_, 2);
v___x_480_ = 0;
v_env_481_ = l_Lean_Environment_setRecordingDeps(v_env_478_, v___x_480_);
v___x_482_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_483_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_479_);
v___x_484_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_484_, 0, v_env_481_);
lean_ctor_set(v___x_484_, 1, v___x_482_);
lean_ctor_set(v___x_484_, 2, v___x_483_);
lean_ctor_set(v___x_484_, 3, v_options_479_);
v___x_485_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_484_);
lean_ctor_set(v___x_485_, 1, v_msgData_472_);
v___x_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0(v_msgData_487_, v___y_488_, v___y_489_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
lean_object* v_ref_496_; lean_object* v___x_497_; lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_506_; 
v_ref_496_ = lean_ctor_get(v___y_493_, 2);
v___x_497_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0(v_msg_492_, v___y_493_, v___y_494_);
v_a_498_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_506_ == 0)
{
v___x_500_ = v___x_497_;
v_isShared_501_ = v_isSharedCheck_506_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_497_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_506_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_502_; lean_object* v___x_504_; 
lean_inc(v_ref_496_);
v___x_502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_502_, 0, v_ref_496_);
lean_ctor_set(v___x_502_, 1, v_a_498_);
if (v_isShared_501_ == 0)
{
lean_ctor_set_tag(v___x_500_, 1);
lean_ctor_set(v___x_500_, 0, v___x_502_);
v___x_504_ = v___x_500_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v___x_502_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0___redArg(v_msg_507_, v___y_508_, v___y_509_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___lam__0(lean_object* v___x_512_, lean_object* v_entry_513_, lean_object* v_s_514_){
_start:
{
lean_object* v_addEntryFn_515_; lean_object* v_importedEntries_516_; lean_object* v_state_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_525_; 
v_addEntryFn_515_ = lean_ctor_get(v___x_512_, 3);
lean_inc(v_addEntryFn_515_);
lean_dec_ref(v___x_512_);
v_importedEntries_516_ = lean_ctor_get(v_s_514_, 0);
v_state_517_ = lean_ctor_get(v_s_514_, 1);
v_isSharedCheck_525_ = !lean_is_exclusive(v_s_514_);
if (v_isSharedCheck_525_ == 0)
{
v___x_519_ = v_s_514_;
v_isShared_520_ = v_isSharedCheck_525_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_state_517_);
lean_inc(v_importedEntries_516_);
lean_dec(v_s_514_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_525_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v_state_521_; lean_object* v___x_523_; 
v_state_521_ = lean_apply_2(v_addEntryFn_515_, v_state_517_, v_entry_513_);
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 1, v_state_521_);
v___x_523_ = v___x_519_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_importedEntries_516_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v_state_521_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14_spec__19___redArg(lean_object* v_keys_526_, lean_object* v_i_527_, lean_object* v_k_528_){
_start:
{
lean_object* v___x_529_; uint8_t v___x_530_; 
v___x_529_ = lean_array_get_size(v_keys_526_);
v___x_530_ = lean_nat_dec_lt(v_i_527_, v___x_529_);
if (v___x_530_ == 0)
{
lean_dec(v_i_527_);
return v___x_530_;
}
else
{
lean_object* v_k_x27_531_; uint8_t v___x_532_; 
v_k_x27_531_ = lean_array_fget_borrowed(v_keys_526_, v_i_527_);
v___x_532_ = l_Lean_instBEqExtraModUse_beq(v_k_528_, v_k_x27_531_);
if (v___x_532_ == 0)
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = lean_unsigned_to_nat(1u);
v___x_534_ = lean_nat_add(v_i_527_, v___x_533_);
lean_dec(v_i_527_);
v_i_527_ = v___x_534_;
goto _start;
}
else
{
lean_dec(v_i_527_);
return v___x_530_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14_spec__19___redArg___boxed(lean_object* v_keys_536_, lean_object* v_i_537_, lean_object* v_k_538_){
_start:
{
uint8_t v_res_539_; lean_object* v_r_540_; 
v_res_539_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14_spec__19___redArg(v_keys_536_, v_i_537_, v_k_538_);
lean_dec_ref(v_k_538_);
lean_dec_ref(v_keys_536_);
v_r_540_ = lean_box(v_res_539_);
return v_r_540_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14___redArg(lean_object* v_x_541_, size_t v_x_542_, lean_object* v_x_543_){
_start:
{
if (lean_obj_tag(v_x_541_) == 0)
{
lean_object* v_es_544_; lean_object* v___x_545_; size_t v___x_546_; size_t v___x_547_; lean_object* v_j_548_; lean_object* v___x_549_; 
v_es_544_ = lean_ctor_get(v_x_541_, 0);
v___x_545_ = lean_box(2);
v___x_546_ = ((size_t)31ULL);
v___x_547_ = lean_usize_land(v_x_542_, v___x_546_);
v_j_548_ = lean_usize_to_nat(v___x_547_);
v___x_549_ = lean_array_get_borrowed(v___x_545_, v_es_544_, v_j_548_);
lean_dec(v_j_548_);
switch(lean_obj_tag(v___x_549_))
{
case 0:
{
lean_object* v_key_550_; uint8_t v___x_551_; 
v_key_550_ = lean_ctor_get(v___x_549_, 0);
v___x_551_ = l_Lean_instBEqExtraModUse_beq(v_x_543_, v_key_550_);
return v___x_551_;
}
case 1:
{
lean_object* v_node_552_; size_t v___x_553_; size_t v___x_554_; 
v_node_552_ = lean_ctor_get(v___x_549_, 0);
v___x_553_ = ((size_t)5ULL);
v___x_554_ = lean_usize_shift_right(v_x_542_, v___x_553_);
v_x_541_ = v_node_552_;
v_x_542_ = v___x_554_;
goto _start;
}
default: 
{
uint8_t v___x_556_; 
v___x_556_ = 0;
return v___x_556_;
}
}
}
else
{
lean_object* v_ks_557_; lean_object* v___x_558_; uint8_t v___x_559_; 
v_ks_557_ = lean_ctor_get(v_x_541_, 0);
v___x_558_ = lean_unsigned_to_nat(0u);
v___x_559_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14_spec__19___redArg(v_ks_557_, v___x_558_, v_x_543_);
return v___x_559_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14___redArg___boxed(lean_object* v_x_560_, lean_object* v_x_561_, lean_object* v_x_562_){
_start:
{
size_t v_x_45058__boxed_563_; uint8_t v_res_564_; lean_object* v_r_565_; 
v_x_45058__boxed_563_ = lean_unbox_usize(v_x_561_);
lean_dec(v_x_561_);
v_res_564_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14___redArg(v_x_560_, v_x_45058__boxed_563_, v_x_562_);
lean_dec_ref(v_x_562_);
lean_dec_ref(v_x_560_);
v_r_565_ = lean_box(v_res_564_);
return v_r_565_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg(lean_object* v_x_566_, lean_object* v_x_567_){
_start:
{
uint64_t v___x_568_; size_t v___x_569_; uint8_t v___x_570_; 
v___x_568_ = l_Lean_instHashableExtraModUse_hash(v_x_567_);
v___x_569_ = lean_uint64_to_usize(v___x_568_);
v___x_570_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14___redArg(v_x_566_, v___x_569_, v_x_567_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_x_571_, lean_object* v_x_572_){
_start:
{
uint8_t v_res_573_; lean_object* v_r_574_; 
v_res_573_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg(v_x_571_, v_x_572_);
lean_dec_ref(v_x_572_);
lean_dec_ref(v_x_571_);
v_r_574_ = lean_box(v_res_573_);
return v_r_574_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0(void){
_start:
{
lean_object* v___x_575_; double v___x_576_; 
v___x_575_ = lean_unsigned_to_nat(0u);
v___x_576_ = lean_float_of_nat(v___x_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__9(lean_object* v_cls_580_, lean_object* v_msg_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
lean_object* v_ref_585_; lean_object* v___x_586_; lean_object* v_a_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_632_; 
v_ref_585_ = lean_ctor_get(v___y_582_, 2);
v___x_586_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0(v_msg_581_, v___y_582_, v___y_583_);
v_a_587_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_632_ == 0)
{
v___x_589_ = v___x_586_;
v_isShared_590_ = v_isSharedCheck_632_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_a_587_);
lean_dec(v___x_586_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_632_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_591_; lean_object* v_traceState_592_; lean_object* v_env_593_; lean_object* v_nextMacroScope_594_; lean_object* v_ngen_595_; lean_object* v_auxDeclNGen_596_; lean_object* v_cache_597_; lean_object* v_recordedDeps_598_; lean_object* v_messages_599_; lean_object* v_infoState_600_; lean_object* v_snapshotTasks_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_631_; 
v___x_591_ = lean_st_ref_take(v___y_583_);
v_traceState_592_ = lean_ctor_get(v___x_591_, 4);
v_env_593_ = lean_ctor_get(v___x_591_, 0);
v_nextMacroScope_594_ = lean_ctor_get(v___x_591_, 1);
v_ngen_595_ = lean_ctor_get(v___x_591_, 2);
v_auxDeclNGen_596_ = lean_ctor_get(v___x_591_, 3);
v_cache_597_ = lean_ctor_get(v___x_591_, 5);
v_recordedDeps_598_ = lean_ctor_get(v___x_591_, 6);
v_messages_599_ = lean_ctor_get(v___x_591_, 7);
v_infoState_600_ = lean_ctor_get(v___x_591_, 8);
v_snapshotTasks_601_ = lean_ctor_get(v___x_591_, 9);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_631_ == 0)
{
v___x_603_ = v___x_591_;
v_isShared_604_ = v_isSharedCheck_631_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_snapshotTasks_601_);
lean_inc(v_infoState_600_);
lean_inc(v_messages_599_);
lean_inc(v_recordedDeps_598_);
lean_inc(v_cache_597_);
lean_inc(v_traceState_592_);
lean_inc(v_auxDeclNGen_596_);
lean_inc(v_ngen_595_);
lean_inc(v_nextMacroScope_594_);
lean_inc(v_env_593_);
lean_dec(v___x_591_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_631_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
uint64_t v_tid_605_; lean_object* v_traces_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_630_; 
v_tid_605_ = lean_ctor_get_uint64(v_traceState_592_, sizeof(void*)*1);
v_traces_606_ = lean_ctor_get(v_traceState_592_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v_traceState_592_);
if (v_isSharedCheck_630_ == 0)
{
v___x_608_ = v_traceState_592_;
v_isShared_609_ = v_isSharedCheck_630_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_traces_606_);
lean_dec(v_traceState_592_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_630_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_610_; lean_object* v___x_611_; double v___x_612_; uint8_t v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_621_; 
v___x_610_ = lean_box(0);
v___x_611_ = lean_box(0);
v___x_612_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0);
v___x_613_ = 0;
v___x_614_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__1));
v___x_615_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_615_, 0, v_cls_580_);
lean_ctor_set(v___x_615_, 1, v___x_611_);
lean_ctor_set(v___x_615_, 2, v___x_614_);
lean_ctor_set_float(v___x_615_, sizeof(void*)*3, v___x_612_);
lean_ctor_set_float(v___x_615_, sizeof(void*)*3 + 8, v___x_612_);
lean_ctor_set_uint8(v___x_615_, sizeof(void*)*3 + 16, v___x_613_);
v___x_616_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__2));
v___x_617_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_617_, 0, v___x_615_);
lean_ctor_set(v___x_617_, 1, v_a_587_);
lean_ctor_set(v___x_617_, 2, v___x_616_);
lean_inc(v_ref_585_);
v___x_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_618_, 0, v_ref_585_);
lean_ctor_set(v___x_618_, 1, v___x_617_);
v___x_619_ = l_Lean_PersistentArray_push___redArg(v_traces_606_, v___x_618_);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 0, v___x_619_);
v___x_621_ = v___x_608_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v___x_619_);
lean_ctor_set_uint64(v_reuseFailAlloc_629_, sizeof(void*)*1, v_tid_605_);
v___x_621_ = v_reuseFailAlloc_629_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
lean_object* v___x_623_; 
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 4, v___x_621_);
v___x_623_ = v___x_603_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_env_593_);
lean_ctor_set(v_reuseFailAlloc_628_, 1, v_nextMacroScope_594_);
lean_ctor_set(v_reuseFailAlloc_628_, 2, v_ngen_595_);
lean_ctor_set(v_reuseFailAlloc_628_, 3, v_auxDeclNGen_596_);
lean_ctor_set(v_reuseFailAlloc_628_, 4, v___x_621_);
lean_ctor_set(v_reuseFailAlloc_628_, 5, v_cache_597_);
lean_ctor_set(v_reuseFailAlloc_628_, 6, v_recordedDeps_598_);
lean_ctor_set(v_reuseFailAlloc_628_, 7, v_messages_599_);
lean_ctor_set(v_reuseFailAlloc_628_, 8, v_infoState_600_);
lean_ctor_set(v_reuseFailAlloc_628_, 9, v_snapshotTasks_601_);
v___x_623_ = v_reuseFailAlloc_628_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
lean_object* v___x_624_; lean_object* v___x_626_; 
v___x_624_ = lean_st_ref_put(v___y_583_, v___x_623_);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 0, v___x_610_);
v___x_626_ = v___x_589_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_610_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__9___boxed(lean_object* v_cls_633_, lean_object* v_msg_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__9(v_cls_633_, v_msg_634_, v___y_635_, v___y_636_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
return v_res_638_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__0(void){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
return v___x_640_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__1(void){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__0);
v___x_642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_641_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
return v___x_642_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__2(void){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_643_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__6(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__5));
v___x_649_ = l_Lean_stringToMessageData(v___x_648_);
return v___x_649_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__8(void){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__7));
v___x_652_ = l_Lean_stringToMessageData(v___x_651_);
return v___x_652_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__9(void){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_653_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__1));
v___x_654_ = l_Lean_stringToMessageData(v___x_653_);
return v___x_654_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__12(void){
_start:
{
lean_object* v_cls_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v_cls_658_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__4));
v___x_659_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__11));
v___x_660_ = l_Lean_Name_append(v___x_659_, v_cls_658_);
return v___x_660_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__14(void){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_662_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__13));
v___x_663_ = l_Lean_stringToMessageData(v___x_662_);
return v___x_663_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__15(void){
_start:
{
lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_664_ = ((lean_object*)(l_Lean_Linter_mkSinceHint___closed__5));
v___x_665_ = l_Lean_stringToMessageData(v___x_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4(lean_object* v_mod_670_, uint8_t v_isMeta_671_, lean_object* v_hint_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v_env_694_; uint8_t v_isExporting_695_; lean_object* v_entry_696_; lean_object* v___x_697_; lean_object* v_env_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; uint8_t v___x_703_; 
v___x_692_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__2);
v___x_693_ = lean_st_ref_get(v___y_674_);
v_env_694_ = lean_ctor_get(v___x_693_, 0);
lean_inc_ref(v_env_694_);
lean_dec(v___x_693_);
v_isExporting_695_ = lean_ctor_get_uint8(v_env_694_, sizeof(void*)*13);
lean_dec_ref(v_env_694_);
lean_inc(v_mod_670_);
v_entry_696_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_696_, 0, v_mod_670_);
lean_ctor_set_uint8(v_entry_696_, sizeof(void*)*1, v_isExporting_695_);
lean_ctor_set_uint8(v_entry_696_, sizeof(void*)*1 + 1, v_isMeta_671_);
v___x_697_ = lean_st_ref_get(v___y_674_);
v_env_698_ = lean_ctor_get(v___x_697_, 0);
lean_inc_ref(v_env_698_);
lean_dec(v___x_697_);
v___x_699_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_700_ = lean_box(1);
v___x_701_ = lean_box(0);
v___x_702_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_692_, v___x_699_, v_env_698_, v___x_700_, v___x_701_);
v___x_703_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg(v___x_702_, v_entry_696_);
lean_dec(v___x_702_);
if (v___x_703_ == 0)
{
lean_object* v_toCold_704_; lean_object* v_options_705_; lean_object* v_inheritedTraceOptions_706_; uint8_t v_hasTrace_707_; lean_object* v___f_708_; uint8_t v___x_709_; lean_object* v___y_711_; 
v_toCold_704_ = lean_ctor_get(v___y_673_, 0);
v_options_705_ = lean_ctor_get(v_toCold_704_, 2);
v_inheritedTraceOptions_706_ = lean_ctor_get(v_toCold_704_, 11);
v_hasTrace_707_ = lean_ctor_get_uint8(v_options_705_, sizeof(void*)*1);
v___f_708_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___lam__0), 3, 2);
lean_closure_set(v___f_708_, 0, v___x_699_);
lean_closure_set(v___f_708_, 1, v_entry_696_);
v___x_709_ = 1;
if (v_hasTrace_707_ == 0)
{
lean_dec(v_hint_672_);
lean_dec(v_mod_670_);
v___y_711_ = v___y_674_;
goto v___jp_710_;
}
else
{
lean_object* v_cls_729_; lean_object* v___y_731_; lean_object* v___y_732_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___x_749_; uint8_t v___x_750_; 
v_cls_729_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__4));
v___x_749_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__12);
v___x_750_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_706_, v_options_705_, v___x_749_);
if (v___x_750_ == 0)
{
lean_dec(v_hint_672_);
lean_dec(v_mod_670_);
v___y_711_ = v___y_674_;
goto v___jp_710_;
}
else
{
lean_object* v___x_751_; lean_object* v___y_753_; 
v___x_751_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__14);
if (v_isExporting_695_ == 0)
{
lean_object* v___x_760_; 
v___x_760_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__18));
v___y_753_ = v___x_760_;
goto v___jp_752_;
}
else
{
lean_object* v___x_761_; 
v___x_761_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__19));
v___y_753_ = v___x_761_;
goto v___jp_752_;
}
v___jp_752_:
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
lean_inc_ref(v___y_753_);
v___x_754_ = l_Lean_stringToMessageData(v___y_753_);
v___x_755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_755_, 0, v___x_751_);
lean_ctor_set(v___x_755_, 1, v___x_754_);
v___x_756_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__15, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__15_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__15);
v___x_757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_757_, 0, v___x_755_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
if (v_isMeta_671_ == 0)
{
lean_object* v___x_758_; 
v___x_758_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__16));
v___y_736_ = v___x_757_;
v___y_737_ = v___x_758_;
goto v___jp_735_;
}
else
{
lean_object* v___x_759_; 
v___x_759_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__17));
v___y_736_ = v___x_757_;
v___y_737_ = v___x_759_;
goto v___jp_735_;
}
}
}
v___jp_730_:
{
lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_733_, 0, v___y_731_);
lean_ctor_set(v___x_733_, 1, v___y_732_);
v___x_734_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__9(v_cls_729_, v___x_733_, v___y_673_, v___y_674_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_dec_ref_known(v___x_734_, 1);
v___y_711_ = v___y_674_;
goto v___jp_710_;
}
else
{
lean_dec_ref(v___f_708_);
return v___x_734_;
}
}
v___jp_735_:
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; uint8_t v___x_744_; 
lean_inc_ref(v___y_737_);
v___x_738_ = l_Lean_stringToMessageData(v___y_737_);
v___x_739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_739_, 0, v___y_736_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
v___x_740_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__6);
v___x_741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_739_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
v___x_742_ = l_Lean_MessageData_ofName(v_mod_670_);
v___x_743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_741_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
v___x_744_ = l_Lean_Name_isAnonymous(v_hint_672_);
if (v___x_744_ == 0)
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_745_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__8);
v___x_746_ = l_Lean_MessageData_ofName(v_hint_672_);
v___x_747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_745_);
lean_ctor_set(v___x_747_, 1, v___x_746_);
v___y_731_ = v___x_743_;
v___y_732_ = v___x_747_;
goto v___jp_730_;
}
else
{
lean_object* v___x_748_; 
lean_dec(v_hint_672_);
v___x_748_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__9);
v___y_731_ = v___x_743_;
v___y_732_ = v___x_748_;
goto v___jp_730_;
}
}
}
v___jp_710_:
{
lean_object* v___x_712_; lean_object* v_toEnvExtension_713_; lean_object* v_env_714_; lean_object* v_nextMacroScope_715_; lean_object* v_ngen_716_; lean_object* v_auxDeclNGen_717_; lean_object* v_traceState_718_; lean_object* v_recordedDeps_719_; lean_object* v_messages_720_; lean_object* v_infoState_721_; lean_object* v_snapshotTasks_722_; lean_object* v_asyncMode_723_; uint8_t v_logWrites_724_; lean_object* v___x_725_; 
v___x_712_ = lean_st_ref_take(v___y_711_);
v_toEnvExtension_713_ = lean_ctor_get(v___x_699_, 0);
v_env_714_ = lean_ctor_get(v___x_712_, 0);
lean_inc_ref(v_env_714_);
v_nextMacroScope_715_ = lean_ctor_get(v___x_712_, 1);
lean_inc(v_nextMacroScope_715_);
v_ngen_716_ = lean_ctor_get(v___x_712_, 2);
lean_inc_ref(v_ngen_716_);
v_auxDeclNGen_717_ = lean_ctor_get(v___x_712_, 3);
lean_inc_ref(v_auxDeclNGen_717_);
v_traceState_718_ = lean_ctor_get(v___x_712_, 4);
lean_inc_ref(v_traceState_718_);
v_recordedDeps_719_ = lean_ctor_get(v___x_712_, 6);
lean_inc_ref(v_recordedDeps_719_);
v_messages_720_ = lean_ctor_get(v___x_712_, 7);
lean_inc_ref(v_messages_720_);
v_infoState_721_ = lean_ctor_get(v___x_712_, 8);
lean_inc_ref(v_infoState_721_);
v_snapshotTasks_722_ = lean_ctor_get(v___x_712_, 9);
lean_inc_ref(v_snapshotTasks_722_);
lean_dec(v___x_712_);
v_asyncMode_723_ = lean_ctor_get(v_toEnvExtension_713_, 2);
v_logWrites_724_ = lean_ctor_get_uint8(v_toEnvExtension_713_, sizeof(void*)*6);
v___x_725_ = lean_box(0);
if (v_logWrites_724_ == 0)
{
lean_object* v___x_726_; 
lean_inc_ref(v_toEnvExtension_713_);
v___x_726_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_713_, v_env_714_, v___f_708_, v_asyncMode_723_, v___x_701_, v___x_709_);
v___y_677_ = v_nextMacroScope_715_;
v___y_678_ = v_recordedDeps_719_;
v___y_679_ = v_snapshotTasks_722_;
v___y_680_ = v___y_711_;
v___y_681_ = v_ngen_716_;
v___y_682_ = v_messages_720_;
v___y_683_ = v_traceState_718_;
v___y_684_ = v___x_725_;
v___y_685_ = v_infoState_721_;
v___y_686_ = v_auxDeclNGen_717_;
v___y_687_ = v___x_726_;
goto v___jp_676_;
}
else
{
lean_object* v___x_727_; lean_object* v___x_728_; 
lean_inc_ref_n(v_toEnvExtension_713_, 2);
v___x_727_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_713_, v_env_714_);
lean_dec_ref(v_env_714_);
v___x_728_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_713_, v___x_727_, v___f_708_, v_asyncMode_723_, v___x_701_, v___x_709_);
v___y_677_ = v_nextMacroScope_715_;
v___y_678_ = v_recordedDeps_719_;
v___y_679_ = v_snapshotTasks_722_;
v___y_680_ = v___y_711_;
v___y_681_ = v_ngen_716_;
v___y_682_ = v_messages_720_;
v___y_683_ = v_traceState_718_;
v___y_684_ = v___x_725_;
v___y_685_ = v_infoState_721_;
v___y_686_ = v_auxDeclNGen_717_;
v___y_687_ = v___x_728_;
goto v___jp_676_;
}
}
}
else
{
lean_object* v___x_762_; lean_object* v___x_763_; 
lean_dec_ref_known(v_entry_696_, 1);
lean_dec(v_hint_672_);
lean_dec(v_mod_670_);
v___x_762_ = lean_box(0);
v___x_763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_763_, 0, v___x_762_);
return v___x_763_;
}
v___jp_676_:
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_688_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__1);
v___x_689_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_689_, 0, v___y_687_);
lean_ctor_set(v___x_689_, 1, v___y_677_);
lean_ctor_set(v___x_689_, 2, v___y_681_);
lean_ctor_set(v___x_689_, 3, v___y_686_);
lean_ctor_set(v___x_689_, 4, v___y_683_);
lean_ctor_set(v___x_689_, 5, v___x_688_);
lean_ctor_set(v___x_689_, 6, v___y_678_);
lean_ctor_set(v___x_689_, 7, v___y_682_);
lean_ctor_set(v___x_689_, 8, v___y_685_);
lean_ctor_set(v___x_689_, 9, v___y_679_);
v___x_690_ = lean_st_ref_put(v___y_680_, v___x_689_);
v___x_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_691_, 0, v___y_684_);
return v___x_691_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___boxed(lean_object* v_mod_764_, lean_object* v_isMeta_765_, lean_object* v_hint_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
uint8_t v_isMeta_boxed_770_; lean_object* v_res_771_; 
v_isMeta_boxed_770_ = lean_unbox(v_isMeta_765_);
v_res_771_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4(v_mod_764_, v_isMeta_boxed_770_, v_hint_766_, v___y_767_, v___y_768_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__5(lean_object* v___x_772_, lean_object* v_declName_773_, lean_object* v_as_774_, size_t v_sz_775_, size_t v_i_776_, lean_object* v_b_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
uint8_t v___x_781_; 
v___x_781_ = lean_usize_dec_lt(v_i_776_, v_sz_775_);
if (v___x_781_ == 0)
{
lean_object* v___x_782_; 
lean_dec(v_declName_773_);
v___x_782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_782_, 0, v_b_777_);
return v___x_782_;
}
else
{
lean_object* v___x_783_; lean_object* v_modules_784_; lean_object* v___x_785_; lean_object* v_a_786_; lean_object* v___x_787_; lean_object* v_toImport_788_; lean_object* v_module_789_; lean_object* v___x_790_; uint8_t v___x_791_; lean_object* v___x_792_; 
v___x_783_ = l_Lean_Environment_header(v___x_772_);
v_modules_784_ = lean_ctor_get(v___x_783_, 3);
lean_inc_ref(v_modules_784_);
lean_dec_ref(v___x_783_);
v___x_785_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_786_ = lean_array_uget_borrowed(v_as_774_, v_i_776_);
v___x_787_ = lean_array_get(v___x_785_, v_modules_784_, v_a_786_);
lean_dec_ref(v_modules_784_);
v_toImport_788_ = lean_ctor_get(v___x_787_, 0);
lean_inc_ref(v_toImport_788_);
lean_dec(v___x_787_);
v_module_789_ = lean_ctor_get(v_toImport_788_, 0);
lean_inc(v_module_789_);
lean_dec_ref(v_toImport_788_);
v___x_790_ = lean_box(0);
v___x_791_ = 0;
lean_inc(v_declName_773_);
v___x_792_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4(v_module_789_, v___x_791_, v_declName_773_, v___y_778_, v___y_779_);
if (lean_obj_tag(v___x_792_) == 0)
{
size_t v___x_793_; size_t v___x_794_; 
lean_dec_ref_known(v___x_792_, 1);
v___x_793_ = ((size_t)1ULL);
v___x_794_ = lean_usize_add(v_i_776_, v___x_793_);
v_i_776_ = v___x_794_;
v_b_777_ = v___x_790_;
goto _start;
}
else
{
lean_dec(v_declName_773_);
return v___x_792_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__5___boxed(lean_object* v___x_796_, lean_object* v_declName_797_, lean_object* v_as_798_, lean_object* v_sz_799_, lean_object* v_i_800_, lean_object* v_b_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
size_t v_sz_boxed_805_; size_t v_i_boxed_806_; lean_object* v_res_807_; 
v_sz_boxed_805_ = lean_unbox_usize(v_sz_799_);
lean_dec(v_sz_799_);
v_i_boxed_806_ = lean_unbox_usize(v_i_800_);
lean_dec(v_i_800_);
v_res_807_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__5(v___x_796_, v_declName_797_, v_as_798_, v_sz_boxed_805_, v_i_boxed_806_, v_b_801_, v___y_802_, v___y_803_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec_ref(v_as_798_);
lean_dec_ref(v___x_796_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg(lean_object* v_a_808_, lean_object* v_x_809_){
_start:
{
if (lean_obj_tag(v_x_809_) == 0)
{
lean_object* v___x_810_; 
v___x_810_ = lean_box(0);
return v___x_810_;
}
else
{
lean_object* v_key_811_; lean_object* v_value_812_; lean_object* v_tail_813_; uint8_t v___x_814_; 
v_key_811_ = lean_ctor_get(v_x_809_, 0);
v_value_812_ = lean_ctor_get(v_x_809_, 1);
v_tail_813_ = lean_ctor_get(v_x_809_, 2);
v___x_814_ = lean_name_eq(v_key_811_, v_a_808_);
if (v___x_814_ == 0)
{
v_x_809_ = v_tail_813_;
goto _start;
}
else
{
lean_object* v___x_816_; 
lean_inc(v_value_812_);
v___x_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_816_, 0, v_value_812_);
return v___x_816_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg___boxed(lean_object* v_a_817_, lean_object* v_x_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg(v_a_817_, v_x_818_);
lean_dec(v_x_818_);
lean_dec(v_a_817_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__6___redArg(lean_object* v_m_820_, lean_object* v_a_821_){
_start:
{
lean_object* v_buckets_822_; lean_object* v___x_823_; uint64_t v___y_825_; 
v_buckets_822_ = lean_ctor_get(v_m_820_, 1);
v___x_823_ = lean_array_get_size(v_buckets_822_);
if (lean_obj_tag(v_a_821_) == 0)
{
uint64_t v___x_839_; 
v___x_839_ = 1723ULL;
v___y_825_ = v___x_839_;
goto v___jp_824_;
}
else
{
uint64_t v_hash_840_; 
v_hash_840_ = lean_ctor_get_uint64(v_a_821_, sizeof(void*)*2);
v___y_825_ = v_hash_840_;
goto v___jp_824_;
}
v___jp_824_:
{
uint64_t v___x_826_; uint64_t v___x_827_; uint64_t v_fold_828_; uint64_t v___x_829_; uint64_t v___x_830_; uint64_t v___x_831_; size_t v___x_832_; size_t v___x_833_; size_t v___x_834_; size_t v___x_835_; size_t v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_826_ = 32ULL;
v___x_827_ = lean_uint64_shift_right(v___y_825_, v___x_826_);
v_fold_828_ = lean_uint64_xor(v___y_825_, v___x_827_);
v___x_829_ = 16ULL;
v___x_830_ = lean_uint64_shift_right(v_fold_828_, v___x_829_);
v___x_831_ = lean_uint64_xor(v_fold_828_, v___x_830_);
v___x_832_ = lean_uint64_to_usize(v___x_831_);
v___x_833_ = lean_usize_of_nat(v___x_823_);
v___x_834_ = ((size_t)1ULL);
v___x_835_ = lean_usize_sub(v___x_833_, v___x_834_);
v___x_836_ = lean_usize_land(v___x_832_, v___x_835_);
v___x_837_ = lean_array_uget_borrowed(v_buckets_822_, v___x_836_);
v___x_838_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg(v_a_821_, v___x_837_);
return v___x_838_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__6___redArg___boxed(lean_object* v_m_841_, lean_object* v_a_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__6___redArg(v_m_841_, v_a_842_);
lean_dec(v_a_842_);
lean_dec_ref(v_m_841_);
return v_res_843_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2___closed__0(void){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l_Std_HashMap_instInhabited___redArg();
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2(lean_object* v_declName_847_, uint8_t v_isMeta_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v_env_857_; lean_object* v___y_859_; lean_object* v___x_872_; 
v___x_852_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2___closed__0);
v___x_853_ = lean_st_ref_get(v___y_850_);
v_env_857_ = lean_ctor_get(v___x_853_, 0);
lean_inc_ref(v_env_857_);
lean_dec(v___x_853_);
v___x_872_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_857_, v_declName_847_);
if (lean_obj_tag(v___x_872_) == 0)
{
lean_dec_ref(v_env_857_);
lean_dec(v_declName_847_);
goto v___jp_854_;
}
else
{
lean_object* v_val_873_; lean_object* v___x_874_; lean_object* v_modules_875_; lean_object* v___x_876_; uint8_t v___x_877_; 
v_val_873_ = lean_ctor_get(v___x_872_, 0);
lean_inc(v_val_873_);
lean_dec_ref_known(v___x_872_, 1);
v___x_874_ = l_Lean_Environment_header(v_env_857_);
v_modules_875_ = lean_ctor_get(v___x_874_, 3);
lean_inc_ref(v_modules_875_);
lean_dec_ref(v___x_874_);
v___x_876_ = lean_array_get_size(v_modules_875_);
v___x_877_ = lean_nat_dec_lt(v_val_873_, v___x_876_);
if (v___x_877_ == 0)
{
lean_dec_ref(v_modules_875_);
lean_dec(v_val_873_);
lean_dec_ref(v_env_857_);
lean_dec(v_declName_847_);
goto v___jp_854_;
}
else
{
lean_object* v___x_878_; lean_object* v___x_879_; uint8_t v___y_881_; 
v___x_878_ = lean_array_fget(v_modules_875_, v_val_873_);
lean_dec(v_val_873_);
lean_dec_ref(v_modules_875_);
v___x_879_ = lean_st_ref_get(v___y_850_);
if (v_isMeta_848_ == 0)
{
lean_dec(v___x_879_);
v___y_881_ = v_isMeta_848_;
goto v___jp_880_;
}
else
{
lean_object* v_env_892_; uint8_t v___x_893_; 
v_env_892_ = lean_ctor_get(v___x_879_, 0);
lean_inc_ref(v_env_892_);
lean_dec(v___x_879_);
lean_inc(v_declName_847_);
v___x_893_ = l_Lean_isMarkedMeta(v_env_892_, v_declName_847_);
if (v___x_893_ == 0)
{
v___y_881_ = v_isMeta_848_;
goto v___jp_880_;
}
else
{
uint8_t v___x_894_; 
v___x_894_ = 0;
v___y_881_ = v___x_894_;
goto v___jp_880_;
}
}
v___jp_880_:
{
lean_object* v_toImport_882_; lean_object* v_module_883_; lean_object* v___x_884_; 
v_toImport_882_ = lean_ctor_get(v___x_878_, 0);
lean_inc_ref(v_toImport_882_);
lean_dec(v___x_878_);
v_module_883_ = lean_ctor_get(v_toImport_882_, 0);
lean_inc(v_module_883_);
lean_dec_ref(v_toImport_882_);
lean_inc(v_declName_847_);
v___x_884_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4(v_module_883_, v___y_881_, v_declName_847_, v___y_849_, v___y_850_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
lean_dec_ref_known(v___x_884_, 1);
v___x_885_ = l_Lean_indirectModUseExt;
v___x_886_ = lean_box(1);
v___x_887_ = lean_box(0);
lean_inc_ref(v_env_857_);
v___x_888_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_852_, v___x_885_, v_env_857_, v___x_886_, v___x_887_);
v___x_889_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__6___redArg(v___x_888_, v_declName_847_);
lean_dec(v___x_888_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v___x_890_; 
v___x_890_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2___closed__1));
v___y_859_ = v___x_890_;
goto v___jp_858_;
}
else
{
lean_object* v_val_891_; 
v_val_891_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_val_891_);
lean_dec_ref_known(v___x_889_, 1);
v___y_859_ = v_val_891_;
goto v___jp_858_;
}
}
else
{
lean_dec_ref(v_env_857_);
lean_dec(v_declName_847_);
return v___x_884_;
}
}
}
}
v___jp_854_:
{
lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_855_ = lean_box(0);
v___x_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
return v___x_856_;
}
v___jp_858_:
{
lean_object* v___x_860_; size_t v_sz_861_; size_t v___x_862_; lean_object* v___x_863_; 
v___x_860_ = lean_box(0);
v_sz_861_ = lean_array_size(v___y_859_);
v___x_862_ = ((size_t)0ULL);
v___x_863_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__5(v_env_857_, v_declName_847_, v___y_859_, v_sz_861_, v___x_862_, v___x_860_, v___y_849_, v___y_850_);
lean_dec_ref(v___y_859_);
lean_dec_ref(v_env_857_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_870_; 
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_870_ == 0)
{
lean_object* v_unused_871_; 
v_unused_871_ = lean_ctor_get(v___x_863_, 0);
lean_dec(v_unused_871_);
v___x_865_ = v___x_863_;
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
else
{
lean_dec(v___x_863_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v___x_860_);
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v___x_860_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
else
{
return v___x_863_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2___boxed(lean_object* v_declName_895_, lean_object* v_isMeta_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
uint8_t v_isMeta_boxed_900_; lean_object* v_res_901_; 
v_isMeta_boxed_900_ = lean_unbox(v_isMeta_896_);
v_res_901_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2(v_declName_895_, v_isMeta_boxed_900_, v___y_897_, v___y_898_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
return v_res_901_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0(uint8_t v_suppressElabErrors_909_, lean_object* v_x_910_){
_start:
{
if (lean_obj_tag(v_x_910_) == 1)
{
lean_object* v_pre_911_; 
v_pre_911_ = lean_ctor_get(v_x_910_, 0);
switch(lean_obj_tag(v_pre_911_))
{
case 1:
{
lean_object* v_pre_912_; 
v_pre_912_ = lean_ctor_get(v_pre_911_, 0);
switch(lean_obj_tag(v_pre_912_))
{
case 0:
{
lean_object* v_str_913_; lean_object* v_str_914_; lean_object* v___x_915_; uint8_t v___x_916_; 
v_str_913_ = lean_ctor_get(v_x_910_, 1);
v_str_914_ = lean_ctor_get(v_pre_911_, 1);
v___x_915_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__0));
v___x_916_ = lean_string_dec_eq(v_str_914_, v___x_915_);
if (v___x_916_ == 0)
{
lean_object* v___x_917_; uint8_t v___x_918_; 
v___x_917_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__1));
v___x_918_ = lean_string_dec_eq(v_str_914_, v___x_917_);
if (v___x_918_ == 0)
{
return v___x_918_;
}
else
{
lean_object* v___x_919_; uint8_t v___x_920_; 
v___x_919_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__2));
v___x_920_ = lean_string_dec_eq(v_str_913_, v___x_919_);
if (v___x_920_ == 0)
{
return v___x_920_;
}
else
{
return v_suppressElabErrors_909_;
}
}
}
else
{
lean_object* v___x_921_; uint8_t v___x_922_; 
v___x_921_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__3));
v___x_922_ = lean_string_dec_eq(v_str_913_, v___x_921_);
if (v___x_922_ == 0)
{
return v___x_922_;
}
else
{
return v_suppressElabErrors_909_;
}
}
}
case 1:
{
lean_object* v_pre_923_; 
v_pre_923_ = lean_ctor_get(v_pre_912_, 0);
if (lean_obj_tag(v_pre_923_) == 0)
{
lean_object* v_str_924_; lean_object* v_str_925_; lean_object* v_str_926_; lean_object* v___x_927_; uint8_t v___x_928_; 
v_str_924_ = lean_ctor_get(v_x_910_, 1);
v_str_925_ = lean_ctor_get(v_pre_911_, 1);
v_str_926_ = lean_ctor_get(v_pre_912_, 1);
v___x_927_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__4));
v___x_928_ = lean_string_dec_eq(v_str_926_, v___x_927_);
if (v___x_928_ == 0)
{
return v___x_928_;
}
else
{
lean_object* v___x_929_; uint8_t v___x_930_; 
v___x_929_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__5));
v___x_930_ = lean_string_dec_eq(v_str_925_, v___x_929_);
if (v___x_930_ == 0)
{
return v___x_930_;
}
else
{
lean_object* v___x_931_; uint8_t v___x_932_; 
v___x_931_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__6));
v___x_932_ = lean_string_dec_eq(v_str_924_, v___x_931_);
if (v___x_932_ == 0)
{
return v___x_932_;
}
else
{
return v_suppressElabErrors_909_;
}
}
}
}
else
{
uint8_t v___x_933_; 
v___x_933_ = 0;
return v___x_933_;
}
}
default: 
{
uint8_t v___x_934_; 
v___x_934_ = 0;
return v___x_934_;
}
}
}
case 0:
{
lean_object* v_str_935_; lean_object* v___x_936_; uint8_t v___x_937_; 
v_str_935_ = lean_ctor_get(v_x_910_, 1);
v___x_936_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__10));
v___x_937_ = lean_string_dec_eq(v_str_935_, v___x_936_);
if (v___x_937_ == 0)
{
return v___x_937_;
}
else
{
return v_suppressElabErrors_909_;
}
}
default: 
{
uint8_t v___x_938_; 
v___x_938_ = 0;
return v___x_938_;
}
}
}
else
{
uint8_t v___x_939_; 
v___x_939_ = 0;
return v___x_939_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___boxed(lean_object* v_suppressElabErrors_940_, lean_object* v_x_941_){
_start:
{
uint8_t v_suppressElabErrors_boxed_942_; uint8_t v_res_943_; lean_object* v_r_944_; 
v_suppressElabErrors_boxed_942_ = lean_unbox(v_suppressElabErrors_940_);
v_res_943_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0(v_suppressElabErrors_boxed_942_, v_x_941_);
lean_dec(v_x_941_);
v_r_944_ = lean_box(v_res_943_);
return v_r_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5(lean_object* v_ref_945_, lean_object* v_msgData_946_, uint8_t v_severity_947_, uint8_t v_isSilent_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
lean_object* v___y_953_; lean_object* v___y_954_; uint8_t v___y_955_; lean_object* v___y_956_; lean_object* v___y_957_; uint8_t v___y_958_; lean_object* v___y_959_; lean_object* v_toCold_960_; lean_object* v___y_961_; lean_object* v___y_990_; lean_object* v___y_991_; uint8_t v___y_992_; lean_object* v___y_993_; lean_object* v___y_994_; uint8_t v___y_995_; uint8_t v___y_996_; lean_object* v___y_997_; uint8_t v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1020_; uint8_t v___y_1021_; uint8_t v___y_1022_; lean_object* v___y_1023_; uint8_t v___y_1027_; uint8_t v___y_1028_; uint8_t v___x_1038_; uint8_t v___y_1040_; uint8_t v___x_1046_; 
v___x_1038_ = 2;
v___x_1046_ = l_Lean_instBEqMessageSeverity_beq(v_severity_947_, v___x_1038_);
if (v___x_1046_ == 0)
{
v___y_1040_ = v___x_1046_;
goto v___jp_1039_;
}
else
{
uint8_t v___x_1047_; 
lean_inc_ref(v_msgData_946_);
v___x_1047_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_946_);
if (v___x_1047_ == 0)
{
v___y_1040_ = v___x_1047_;
goto v___jp_1039_;
}
else
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
lean_dec_ref(v_msgData_946_);
v___x_1048_ = lean_box(0);
v___x_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
return v___x_1049_;
}
}
v___jp_952_:
{
lean_object* v_currNamespace_962_; lean_object* v_openDecls_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v_env_968_; lean_object* v_nextMacroScope_969_; lean_object* v_ngen_970_; lean_object* v_auxDeclNGen_971_; lean_object* v_traceState_972_; lean_object* v_cache_973_; lean_object* v_recordedDeps_974_; lean_object* v_messages_975_; lean_object* v_infoState_976_; lean_object* v_snapshotTasks_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_988_; 
v_currNamespace_962_ = lean_ctor_get(v_toCold_960_, 4);
v_openDecls_963_ = lean_ctor_get(v_toCold_960_, 5);
lean_inc(v_openDecls_963_);
lean_inc(v_currNamespace_962_);
v___x_964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_964_, 0, v_currNamespace_962_);
lean_ctor_set(v___x_964_, 1, v_openDecls_963_);
v___x_965_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_964_);
lean_ctor_set(v___x_965_, 1, v___y_959_);
lean_inc_ref(v___y_954_);
lean_inc_ref(v___y_953_);
v___x_966_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_966_, 0, v___y_953_);
lean_ctor_set(v___x_966_, 1, v___y_957_);
lean_ctor_set(v___x_966_, 2, v___y_956_);
lean_ctor_set(v___x_966_, 3, v___y_954_);
lean_ctor_set(v___x_966_, 4, v___x_965_);
lean_ctor_set_uint8(v___x_966_, sizeof(void*)*5, v___y_958_);
lean_ctor_set_uint8(v___x_966_, sizeof(void*)*5 + 1, v___y_955_);
lean_ctor_set_uint8(v___x_966_, sizeof(void*)*5 + 2, v_isSilent_948_);
v___x_967_ = lean_st_ref_take(v___y_961_);
v_env_968_ = lean_ctor_get(v___x_967_, 0);
v_nextMacroScope_969_ = lean_ctor_get(v___x_967_, 1);
v_ngen_970_ = lean_ctor_get(v___x_967_, 2);
v_auxDeclNGen_971_ = lean_ctor_get(v___x_967_, 3);
v_traceState_972_ = lean_ctor_get(v___x_967_, 4);
v_cache_973_ = lean_ctor_get(v___x_967_, 5);
v_recordedDeps_974_ = lean_ctor_get(v___x_967_, 6);
v_messages_975_ = lean_ctor_get(v___x_967_, 7);
v_infoState_976_ = lean_ctor_get(v___x_967_, 8);
v_snapshotTasks_977_ = lean_ctor_get(v___x_967_, 9);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_988_ == 0)
{
v___x_979_ = v___x_967_;
v_isShared_980_ = v_isSharedCheck_988_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_snapshotTasks_977_);
lean_inc(v_infoState_976_);
lean_inc(v_messages_975_);
lean_inc(v_recordedDeps_974_);
lean_inc(v_cache_973_);
lean_inc(v_traceState_972_);
lean_inc(v_auxDeclNGen_971_);
lean_inc(v_ngen_970_);
lean_inc(v_nextMacroScope_969_);
lean_inc(v_env_968_);
lean_dec(v___x_967_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_988_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_984_; 
v___x_981_ = lean_box(0);
v___x_982_ = l_Lean_MessageLog_add(v___x_966_, v_messages_975_);
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 7, v___x_982_);
v___x_984_ = v___x_979_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_env_968_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v_nextMacroScope_969_);
lean_ctor_set(v_reuseFailAlloc_987_, 2, v_ngen_970_);
lean_ctor_set(v_reuseFailAlloc_987_, 3, v_auxDeclNGen_971_);
lean_ctor_set(v_reuseFailAlloc_987_, 4, v_traceState_972_);
lean_ctor_set(v_reuseFailAlloc_987_, 5, v_cache_973_);
lean_ctor_set(v_reuseFailAlloc_987_, 6, v_recordedDeps_974_);
lean_ctor_set(v_reuseFailAlloc_987_, 7, v___x_982_);
lean_ctor_set(v_reuseFailAlloc_987_, 8, v_infoState_976_);
lean_ctor_set(v_reuseFailAlloc_987_, 9, v_snapshotTasks_977_);
v___x_984_ = v_reuseFailAlloc_987_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = lean_st_ref_put(v___y_961_, v___x_984_);
v___x_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_986_, 0, v___x_981_);
return v___x_986_;
}
}
}
v___jp_989_:
{
lean_object* v_fileName_998_; lean_object* v_fileMap_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1015_; 
v_fileName_998_ = lean_ctor_get(v___y_994_, 0);
v_fileMap_999_ = lean_ctor_get(v___y_994_, 1);
v___x_1000_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_946_);
v___x_1001_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0(v___x_1000_, v___y_949_, v___y_950_);
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1004_ = v___x_1001_;
v_isShared_1005_ = v_isSharedCheck_1015_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_1001_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1015_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
lean_inc_ref_n(v_fileMap_999_, 2);
v___x_1006_ = l_Lean_FileMap_toPosition(v_fileMap_999_, v___y_993_);
lean_dec(v___y_993_);
v___x_1007_ = l_Lean_FileMap_toPosition(v_fileMap_999_, v___y_997_);
lean_dec(v___y_997_);
v___x_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
v___x_1009_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__1));
if (v___y_992_ == 0)
{
lean_del_object(v___x_1004_);
lean_dec_ref(v___y_991_);
v___y_953_ = v_fileName_998_;
v___y_954_ = v___x_1009_;
v___y_955_ = v___y_995_;
v___y_956_ = v___x_1008_;
v___y_957_ = v___x_1006_;
v___y_958_ = v___y_996_;
v___y_959_ = v_a_1002_;
v_toCold_960_ = v___y_990_;
v___y_961_ = v___y_950_;
goto v___jp_952_;
}
else
{
uint8_t v___x_1010_; 
lean_inc(v_a_1002_);
v___x_1010_ = l_Lean_MessageData_hasTag(v___y_991_, v_a_1002_);
if (v___x_1010_ == 0)
{
lean_object* v___x_1011_; lean_object* v___x_1013_; 
lean_dec_ref_known(v___x_1008_, 1);
lean_dec_ref(v___x_1006_);
lean_dec(v_a_1002_);
v___x_1011_ = lean_box(0);
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 0, v___x_1011_);
v___x_1013_ = v___x_1004_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v___x_1011_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
else
{
lean_del_object(v___x_1004_);
v___y_953_ = v_fileName_998_;
v___y_954_ = v___x_1009_;
v___y_955_ = v___y_995_;
v___y_956_ = v___x_1008_;
v___y_957_ = v___x_1006_;
v___y_958_ = v___y_996_;
v___y_959_ = v_a_1002_;
v_toCold_960_ = v___y_990_;
v___y_961_ = v___y_950_;
goto v___jp_952_;
}
}
}
}
v___jp_1016_:
{
lean_object* v___x_1024_; 
v___x_1024_ = l_Lean_Syntax_getTailPos_x3f(v___y_1020_, v___y_1022_);
lean_dec(v___y_1020_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_inc(v___y_1023_);
v___y_990_ = v___y_1018_;
v___y_991_ = v___y_1019_;
v___y_992_ = v___y_1017_;
v___y_993_ = v___y_1023_;
v___y_994_ = v___y_1018_;
v___y_995_ = v___y_1021_;
v___y_996_ = v___y_1022_;
v___y_997_ = v___y_1023_;
goto v___jp_989_;
}
else
{
lean_object* v_val_1025_; 
v_val_1025_ = lean_ctor_get(v___x_1024_, 0);
lean_inc(v_val_1025_);
lean_dec_ref_known(v___x_1024_, 1);
v___y_990_ = v___y_1018_;
v___y_991_ = v___y_1019_;
v___y_992_ = v___y_1017_;
v___y_993_ = v___y_1023_;
v___y_994_ = v___y_1018_;
v___y_995_ = v___y_1021_;
v___y_996_ = v___y_1022_;
v___y_997_ = v_val_1025_;
goto v___jp_989_;
}
}
v___jp_1026_:
{
lean_object* v_toCold_1029_; lean_object* v_ref_1030_; uint8_t v_suppressElabErrors_1031_; lean_object* v___x_1032_; lean_object* v___f_1033_; lean_object* v_ref_1034_; lean_object* v___x_1035_; 
v_toCold_1029_ = lean_ctor_get(v___y_949_, 0);
v_ref_1030_ = lean_ctor_get(v___y_949_, 2);
v_suppressElabErrors_1031_ = lean_ctor_get_uint8(v___y_949_, sizeof(void*)*3 + 2);
v___x_1032_ = lean_box(v_suppressElabErrors_1031_);
v___f_1033_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1033_, 0, v___x_1032_);
v_ref_1034_ = l_Lean_replaceRef(v_ref_945_, v_ref_1030_);
v___x_1035_ = l_Lean_Syntax_getPos_x3f(v_ref_1034_, v___y_1027_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v___x_1036_; 
v___x_1036_ = lean_unsigned_to_nat(0u);
v___y_1017_ = v_suppressElabErrors_1031_;
v___y_1018_ = v_toCold_1029_;
v___y_1019_ = v___f_1033_;
v___y_1020_ = v_ref_1034_;
v___y_1021_ = v___y_1028_;
v___y_1022_ = v___y_1027_;
v___y_1023_ = v___x_1036_;
goto v___jp_1016_;
}
else
{
lean_object* v_val_1037_; 
v_val_1037_ = lean_ctor_get(v___x_1035_, 0);
lean_inc(v_val_1037_);
lean_dec_ref_known(v___x_1035_, 1);
v___y_1017_ = v_suppressElabErrors_1031_;
v___y_1018_ = v_toCold_1029_;
v___y_1019_ = v___f_1033_;
v___y_1020_ = v_ref_1034_;
v___y_1021_ = v___y_1028_;
v___y_1022_ = v___y_1027_;
v___y_1023_ = v_val_1037_;
goto v___jp_1016_;
}
}
v___jp_1039_:
{
uint8_t v___x_1041_; uint8_t v___x_1042_; 
v___x_1041_ = 1;
v___x_1042_ = l_Lean_instBEqMessageSeverity_beq(v_severity_947_, v___x_1041_);
if (v___x_1042_ == 0)
{
v___y_1027_ = v___y_1040_;
v___y_1028_ = v_severity_947_;
goto v___jp_1026_;
}
else
{
lean_object* v___x_1043_; lean_object* v___x_1044_; uint8_t v___x_1045_; 
v___x_1043_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_949_);
v___x_1044_ = l_Lean_warningAsError;
v___x_1045_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__5(v___x_1043_, v___x_1044_);
lean_dec_ref(v___x_1043_);
if (v___x_1045_ == 0)
{
v___y_1027_ = v___y_1040_;
v___y_1028_ = v_severity_947_;
goto v___jp_1026_;
}
else
{
v___y_1027_ = v___y_1040_;
v___y_1028_ = v___x_1038_;
goto v___jp_1026_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___boxed(lean_object* v_ref_1050_, lean_object* v_msgData_1051_, lean_object* v_severity_1052_, lean_object* v_isSilent_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
uint8_t v_severity_boxed_1057_; uint8_t v_isSilent_boxed_1058_; lean_object* v_res_1059_; 
v_severity_boxed_1057_ = lean_unbox(v_severity_1052_);
v_isSilent_boxed_1058_ = lean_unbox(v_isSilent_1053_);
v_res_1059_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5(v_ref_1050_, v_msgData_1051_, v_severity_boxed_1057_, v_isSilent_boxed_1058_, v___y_1054_, v___y_1055_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec(v_ref_1050_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_msgData_1060_, uint8_t v_severity_1061_, uint8_t v_isSilent_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
lean_object* v_ref_1066_; lean_object* v___x_1067_; 
v_ref_1066_ = lean_ctor_get(v___y_1063_, 2);
v___x_1067_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5(v_ref_1066_, v_msgData_1060_, v_severity_1061_, v_isSilent_1062_, v___y_1063_, v___y_1064_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_msgData_1068_, lean_object* v_severity_1069_, lean_object* v_isSilent_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
uint8_t v_severity_boxed_1074_; uint8_t v_isSilent_boxed_1075_; lean_object* v_res_1076_; 
v_severity_boxed_1074_ = lean_unbox(v_severity_1069_);
v_isSilent_boxed_1075_ = lean_unbox(v_isSilent_1070_);
v_res_1076_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2(v_msgData_1068_, v_severity_boxed_1074_, v_isSilent_boxed_1075_, v___y_1071_, v___y_1072_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1(lean_object* v_msgData_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
uint8_t v___x_1081_; uint8_t v___x_1082_; lean_object* v___x_1083_; 
v___x_1081_ = 1;
v___x_1082_ = 0;
v___x_1083_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2(v_msgData_1077_, v___x_1081_, v___x_1082_, v___y_1078_, v___y_1079_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1___boxed(lean_object* v_msgData_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1(v_msgData_1084_, v___y_1085_, v___y_1086_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
return v_res_1088_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__4_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1089_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__4_spec__10___redArg(){
_start:
{
lean_object* v___x_1092_; 
v___x_1092_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__4_spec__10___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__4_spec__10___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__4_spec__10___redArg___closed__0);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__4_spec__10___redArg___boxed(lean_object* v___dummy_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__4_spec__10___redArg();
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__33(lean_object* v_x_1095_){
_start:
{
if (lean_obj_tag(v_x_1095_) == 0)
{
lean_object* v___x_1096_; 
v___x_1096_ = lean_box(0);
return v___x_1096_;
}
else
{
lean_object* v_head_1097_; lean_object* v_tail_1098_; lean_object* v_fst_1099_; uint8_t v___x_1100_; 
v_head_1097_ = lean_ctor_get(v_x_1095_, 0);
v_tail_1098_ = lean_ctor_get(v_x_1095_, 1);
v_fst_1099_ = lean_ctor_get(v_head_1097_, 0);
v___x_1100_ = l_Lean_isPrivateName(v_fst_1099_);
if (v___x_1100_ == 0)
{
v_x_1095_ = v_tail_1098_;
goto _start;
}
else
{
lean_object* v___x_1102_; 
lean_inc(v_head_1097_);
v___x_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1102_, 0, v_head_1097_);
return v___x_1102_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__33___boxed(lean_object* v_x_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__33(v_x_1103_);
lean_dec(v_x_1103_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44_spec__46_spec__49(lean_object* v_msgData_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v___x_1111_; lean_object* v_env_1112_; uint8_t v___x_1113_; lean_object* v_env_1114_; lean_object* v___x_1115_; lean_object* v_toCold_1116_; lean_object* v_mctx_1117_; lean_object* v_lctx_1118_; lean_object* v_options_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1111_ = lean_st_ref_get(v___y_1109_);
v_env_1112_ = lean_ctor_get(v___x_1111_, 0);
lean_inc_ref(v_env_1112_);
lean_dec(v___x_1111_);
v___x_1113_ = 0;
v_env_1114_ = l_Lean_Environment_setRecordingDeps(v_env_1112_, v___x_1113_);
v___x_1115_ = lean_st_ref_get(v___y_1107_);
v_toCold_1116_ = lean_ctor_get(v___y_1108_, 0);
v_mctx_1117_ = lean_ctor_get(v___x_1115_, 0);
lean_inc_ref(v_mctx_1117_);
lean_dec(v___x_1115_);
v_lctx_1118_ = lean_ctor_get(v___y_1106_, 2);
v_options_1119_ = lean_ctor_get(v_toCold_1116_, 2);
lean_inc_ref(v_options_1119_);
lean_inc_ref(v_lctx_1118_);
v___x_1120_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1120_, 0, v_env_1114_);
lean_ctor_set(v___x_1120_, 1, v_mctx_1117_);
lean_ctor_set(v___x_1120_, 2, v_lctx_1118_);
lean_ctor_set(v___x_1120_, 3, v_options_1119_);
v___x_1121_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1120_);
lean_ctor_set(v___x_1121_, 1, v_msgData_1105_);
v___x_1122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1121_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44_spec__46_spec__49___boxed(lean_object* v_msgData_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44_spec__46_spec__49(v_msgData_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46_spec__48_spec__50(lean_object* v_ref_1132_, lean_object* v_msgData_1133_, uint8_t v_severity_1134_, uint8_t v_isSilent_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
lean_object* v_a_1142_; uint8_t v___y_1146_; uint8_t v___y_1147_; lean_object* v___y_1148_; lean_object* v___y_1149_; lean_object* v___y_1150_; lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v_toCold_1153_; lean_object* v___y_1154_; lean_object* v___y_1182_; lean_object* v___y_1183_; uint8_t v___y_1184_; uint8_t v___y_1185_; lean_object* v___y_1186_; uint8_t v___y_1187_; lean_object* v___y_1188_; lean_object* v___y_1189_; uint8_t v___y_1208_; lean_object* v___y_1209_; lean_object* v___y_1210_; uint8_t v___y_1211_; uint8_t v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; uint8_t v___y_1218_; uint8_t v___y_1219_; uint8_t v___x_1229_; uint8_t v___y_1231_; uint8_t v___x_1237_; 
v___x_1229_ = 2;
v___x_1237_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1134_, v___x_1229_);
if (v___x_1237_ == 0)
{
v___y_1231_ = v___x_1237_;
goto v___jp_1230_;
}
else
{
uint8_t v___x_1238_; 
lean_inc_ref(v_msgData_1133_);
v___x_1238_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1133_);
if (v___x_1238_ == 0)
{
v___y_1231_ = v___x_1238_;
goto v___jp_1230_;
}
else
{
lean_object* v___x_1239_; lean_object* v___x_1240_; 
lean_dec_ref(v_msgData_1133_);
v___x_1239_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46_spec__48_spec__50___closed__0));
v___x_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
return v___x_1240_;
}
}
v___jp_1141_:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1143_, 0, v_a_1142_);
v___x_1144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1143_);
return v___x_1144_;
}
v___jp_1145_:
{
lean_object* v_currNamespace_1155_; lean_object* v_openDecls_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v_env_1161_; lean_object* v_nextMacroScope_1162_; lean_object* v_ngen_1163_; lean_object* v_auxDeclNGen_1164_; lean_object* v_traceState_1165_; lean_object* v_cache_1166_; lean_object* v_recordedDeps_1167_; lean_object* v_messages_1168_; lean_object* v_infoState_1169_; lean_object* v_snapshotTasks_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1180_; 
v_currNamespace_1155_ = lean_ctor_get(v_toCold_1153_, 4);
v_openDecls_1156_ = lean_ctor_get(v_toCold_1153_, 5);
lean_inc(v_openDecls_1156_);
lean_inc(v_currNamespace_1155_);
v___x_1157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1157_, 0, v_currNamespace_1155_);
lean_ctor_set(v___x_1157_, 1, v_openDecls_1156_);
v___x_1158_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1157_);
lean_ctor_set(v___x_1158_, 1, v___y_1148_);
lean_inc_ref(v___y_1150_);
lean_inc_ref(v___y_1149_);
v___x_1159_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1159_, 0, v___y_1149_);
lean_ctor_set(v___x_1159_, 1, v___y_1151_);
lean_ctor_set(v___x_1159_, 2, v___y_1152_);
lean_ctor_set(v___x_1159_, 3, v___y_1150_);
lean_ctor_set(v___x_1159_, 4, v___x_1158_);
lean_ctor_set_uint8(v___x_1159_, sizeof(void*)*5, v___y_1147_);
lean_ctor_set_uint8(v___x_1159_, sizeof(void*)*5 + 1, v___y_1146_);
lean_ctor_set_uint8(v___x_1159_, sizeof(void*)*5 + 2, v_isSilent_1135_);
v___x_1160_ = lean_st_ref_take(v___y_1154_);
v_env_1161_ = lean_ctor_get(v___x_1160_, 0);
v_nextMacroScope_1162_ = lean_ctor_get(v___x_1160_, 1);
v_ngen_1163_ = lean_ctor_get(v___x_1160_, 2);
v_auxDeclNGen_1164_ = lean_ctor_get(v___x_1160_, 3);
v_traceState_1165_ = lean_ctor_get(v___x_1160_, 4);
v_cache_1166_ = lean_ctor_get(v___x_1160_, 5);
v_recordedDeps_1167_ = lean_ctor_get(v___x_1160_, 6);
v_messages_1168_ = lean_ctor_get(v___x_1160_, 7);
v_infoState_1169_ = lean_ctor_get(v___x_1160_, 8);
v_snapshotTasks_1170_ = lean_ctor_get(v___x_1160_, 9);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1172_ = v___x_1160_;
v_isShared_1173_ = v_isSharedCheck_1180_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_snapshotTasks_1170_);
lean_inc(v_infoState_1169_);
lean_inc(v_messages_1168_);
lean_inc(v_recordedDeps_1167_);
lean_inc(v_cache_1166_);
lean_inc(v_traceState_1165_);
lean_inc(v_auxDeclNGen_1164_);
lean_inc(v_ngen_1163_);
lean_inc(v_nextMacroScope_1162_);
lean_inc(v_env_1161_);
lean_dec(v___x_1160_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1180_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1177_; 
v___x_1174_ = lean_box(0);
v___x_1175_ = l_Lean_MessageLog_add(v___x_1159_, v_messages_1168_);
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 7, v___x_1175_);
v___x_1177_ = v___x_1172_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_env_1161_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v_nextMacroScope_1162_);
lean_ctor_set(v_reuseFailAlloc_1179_, 2, v_ngen_1163_);
lean_ctor_set(v_reuseFailAlloc_1179_, 3, v_auxDeclNGen_1164_);
lean_ctor_set(v_reuseFailAlloc_1179_, 4, v_traceState_1165_);
lean_ctor_set(v_reuseFailAlloc_1179_, 5, v_cache_1166_);
lean_ctor_set(v_reuseFailAlloc_1179_, 6, v_recordedDeps_1167_);
lean_ctor_set(v_reuseFailAlloc_1179_, 7, v___x_1175_);
lean_ctor_set(v_reuseFailAlloc_1179_, 8, v_infoState_1169_);
lean_ctor_set(v_reuseFailAlloc_1179_, 9, v_snapshotTasks_1170_);
v___x_1177_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
lean_object* v___x_1178_; 
v___x_1178_ = lean_st_ref_put(v___y_1154_, v___x_1177_);
v_a_1142_ = v___x_1174_;
goto v___jp_1141_;
}
}
}
v___jp_1181_:
{
lean_object* v_fileName_1190_; lean_object* v_fileMap_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1206_; 
v_fileName_1190_ = lean_ctor_get(v___y_1186_, 0);
v_fileMap_1191_ = lean_ctor_get(v___y_1186_, 1);
v___x_1192_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1133_);
v___x_1193_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44_spec__46_spec__49(v___x_1192_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
v_a_1194_ = lean_ctor_get(v___x_1193_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1196_ = v___x_1193_;
v_isShared_1197_ = v_isSharedCheck_1206_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1193_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1206_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1201_; 
lean_inc_ref_n(v_fileMap_1191_, 2);
v___x_1198_ = l_Lean_FileMap_toPosition(v_fileMap_1191_, v___y_1188_);
lean_dec(v___y_1188_);
v___x_1199_ = l_Lean_FileMap_toPosition(v_fileMap_1191_, v___y_1189_);
lean_dec(v___y_1189_);
if (v_isShared_1197_ == 0)
{
lean_ctor_set_tag(v___x_1196_, 1);
lean_ctor_set(v___x_1196_, 0, v___x_1199_);
v___x_1201_ = v___x_1196_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1199_);
v___x_1201_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
lean_object* v___x_1202_; 
v___x_1202_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__1));
if (v___y_1184_ == 0)
{
lean_dec_ref(v___y_1182_);
v___y_1146_ = v___y_1185_;
v___y_1147_ = v___y_1187_;
v___y_1148_ = v_a_1194_;
v___y_1149_ = v_fileName_1190_;
v___y_1150_ = v___x_1202_;
v___y_1151_ = v___x_1198_;
v___y_1152_ = v___x_1201_;
v_toCold_1153_ = v___y_1183_;
v___y_1154_ = v___y_1139_;
goto v___jp_1145_;
}
else
{
uint8_t v___x_1203_; 
lean_inc(v_a_1194_);
v___x_1203_ = l_Lean_MessageData_hasTag(v___y_1182_, v_a_1194_);
if (v___x_1203_ == 0)
{
lean_object* v___x_1204_; 
lean_dec_ref(v___x_1201_);
lean_dec_ref(v___x_1198_);
lean_dec(v_a_1194_);
v___x_1204_ = lean_box(0);
v_a_1142_ = v___x_1204_;
goto v___jp_1141_;
}
else
{
v___y_1146_ = v___y_1185_;
v___y_1147_ = v___y_1187_;
v___y_1148_ = v_a_1194_;
v___y_1149_ = v_fileName_1190_;
v___y_1150_ = v___x_1202_;
v___y_1151_ = v___x_1198_;
v___y_1152_ = v___x_1201_;
v_toCold_1153_ = v___y_1183_;
v___y_1154_ = v___y_1139_;
goto v___jp_1145_;
}
}
}
}
}
v___jp_1207_:
{
lean_object* v___x_1215_; 
v___x_1215_ = l_Lean_Syntax_getTailPos_x3f(v___y_1213_, v___y_1212_);
lean_dec(v___y_1213_);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_inc(v___y_1214_);
v___y_1182_ = v___y_1209_;
v___y_1183_ = v___y_1210_;
v___y_1184_ = v___y_1208_;
v___y_1185_ = v___y_1211_;
v___y_1186_ = v___y_1210_;
v___y_1187_ = v___y_1212_;
v___y_1188_ = v___y_1214_;
v___y_1189_ = v___y_1214_;
goto v___jp_1181_;
}
else
{
lean_object* v_val_1216_; 
v_val_1216_ = lean_ctor_get(v___x_1215_, 0);
lean_inc(v_val_1216_);
lean_dec_ref_known(v___x_1215_, 1);
v___y_1182_ = v___y_1209_;
v___y_1183_ = v___y_1210_;
v___y_1184_ = v___y_1208_;
v___y_1185_ = v___y_1211_;
v___y_1186_ = v___y_1210_;
v___y_1187_ = v___y_1212_;
v___y_1188_ = v___y_1214_;
v___y_1189_ = v_val_1216_;
goto v___jp_1181_;
}
}
v___jp_1217_:
{
lean_object* v_toCold_1220_; lean_object* v_ref_1221_; uint8_t v_suppressElabErrors_1222_; lean_object* v___x_1223_; lean_object* v___f_1224_; lean_object* v_ref_1225_; lean_object* v___x_1226_; 
v_toCold_1220_ = lean_ctor_get(v___y_1138_, 0);
v_ref_1221_ = lean_ctor_get(v___y_1138_, 2);
v_suppressElabErrors_1222_ = lean_ctor_get_uint8(v___y_1138_, sizeof(void*)*3 + 2);
v___x_1223_ = lean_box(v_suppressElabErrors_1222_);
v___f_1224_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1224_, 0, v___x_1223_);
v_ref_1225_ = l_Lean_replaceRef(v_ref_1132_, v_ref_1221_);
v___x_1226_ = l_Lean_Syntax_getPos_x3f(v_ref_1225_, v___y_1218_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_object* v___x_1227_; 
v___x_1227_ = lean_unsigned_to_nat(0u);
v___y_1208_ = v_suppressElabErrors_1222_;
v___y_1209_ = v___f_1224_;
v___y_1210_ = v_toCold_1220_;
v___y_1211_ = v___y_1219_;
v___y_1212_ = v___y_1218_;
v___y_1213_ = v_ref_1225_;
v___y_1214_ = v___x_1227_;
goto v___jp_1207_;
}
else
{
lean_object* v_val_1228_; 
v_val_1228_ = lean_ctor_get(v___x_1226_, 0);
lean_inc(v_val_1228_);
lean_dec_ref_known(v___x_1226_, 1);
v___y_1208_ = v_suppressElabErrors_1222_;
v___y_1209_ = v___f_1224_;
v___y_1210_ = v_toCold_1220_;
v___y_1211_ = v___y_1219_;
v___y_1212_ = v___y_1218_;
v___y_1213_ = v_ref_1225_;
v___y_1214_ = v_val_1228_;
goto v___jp_1207_;
}
}
v___jp_1230_:
{
uint8_t v___x_1232_; uint8_t v___x_1233_; 
v___x_1232_ = 1;
v___x_1233_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1134_, v___x_1232_);
if (v___x_1233_ == 0)
{
v___y_1218_ = v___y_1231_;
v___y_1219_ = v_severity_1134_;
goto v___jp_1217_;
}
else
{
lean_object* v___x_1234_; lean_object* v___x_1235_; uint8_t v___x_1236_; 
v___x_1234_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1138_);
v___x_1235_ = l_Lean_warningAsError;
v___x_1236_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__5(v___x_1234_, v___x_1235_);
lean_dec_ref(v___x_1234_);
if (v___x_1236_ == 0)
{
v___y_1218_ = v___y_1231_;
v___y_1219_ = v_severity_1134_;
goto v___jp_1217_;
}
else
{
v___y_1218_ = v___y_1231_;
v___y_1219_ = v___x_1229_;
goto v___jp_1217_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46_spec__48_spec__50___boxed(lean_object* v_ref_1241_, lean_object* v_msgData_1242_, lean_object* v_severity_1243_, lean_object* v_isSilent_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
uint8_t v_severity_boxed_1250_; uint8_t v_isSilent_boxed_1251_; lean_object* v_res_1252_; 
v_severity_boxed_1250_ = lean_unbox(v_severity_1243_);
v_isSilent_boxed_1251_ = lean_unbox(v_isSilent_1244_);
v_res_1252_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46_spec__48_spec__50(v_ref_1241_, v_msgData_1242_, v_severity_boxed_1250_, v_isSilent_boxed_1251_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec(v_ref_1241_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46_spec__48(lean_object* v_msgData_1253_, uint8_t v_severity_1254_, uint8_t v_isSilent_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
lean_object* v_ref_1261_; lean_object* v___x_1262_; 
v_ref_1261_ = lean_ctor_get(v___y_1258_, 2);
v___x_1262_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46_spec__48_spec__50(v_ref_1261_, v_msgData_1253_, v_severity_1254_, v_isSilent_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46_spec__48___boxed(lean_object* v_msgData_1263_, lean_object* v_severity_1264_, lean_object* v_isSilent_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
uint8_t v_severity_boxed_1271_; uint8_t v_isSilent_boxed_1272_; lean_object* v_res_1273_; 
v_severity_boxed_1271_ = lean_unbox(v_severity_1264_);
v_isSilent_boxed_1272_ = lean_unbox(v_isSilent_1265_);
v_res_1273_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46_spec__48(v_msgData_1263_, v_severity_boxed_1271_, v_isSilent_boxed_1272_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46(lean_object* v_msgData_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
uint8_t v___x_1280_; uint8_t v___x_1281_; lean_object* v___x_1282_; 
v___x_1280_ = 1;
v___x_1281_ = 0;
v___x_1282_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46_spec__48(v_msgData_1274_, v___x_1280_, v___x_1281_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46___boxed(lean_object* v_msgData_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46(v_msgData_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__45___redArg(lean_object* v_opt_1290_, lean_object* v___y_1291_){
_start:
{
lean_object* v___x_1293_; uint8_t v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1293_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1291_);
v___x_1294_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__5(v___x_1293_, v_opt_1290_);
lean_dec_ref(v___x_1293_);
v___x_1295_ = lean_box(v___x_1294_);
v___x_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1295_);
v___x_1297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1297_, 0, v___x_1296_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__45___redArg___boxed(lean_object* v_opt_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__45___redArg(v_opt_1298_, v___y_1299_);
lean_dec_ref(v___y_1299_);
lean_dec_ref(v_opt_1298_);
return v_res_1301_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___closed__1(void){
_start:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1303_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___closed__0));
v___x_1304_ = l_Lean_stringToMessageData(v___x_1303_);
return v___x_1304_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___closed__3(void){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1306_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___closed__2));
v___x_1307_ = l_Lean_stringToMessageData(v___x_1306_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42(lean_object* v_id_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v___x_1314_; lean_object* v_env_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1338_; 
v___x_1314_ = lean_st_ref_get(v___y_1312_);
v_env_1315_ = lean_ctor_get(v___x_1314_, 0);
lean_inc_ref(v_env_1315_);
lean_dec(v___x_1314_);
v___x_1316_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1317_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__45___redArg(v___x_1316_, v___y_1311_);
v_a_1318_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1320_ = v___x_1317_;
v_isShared_1321_ = v_isSharedCheck_1338_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1317_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1338_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
uint8_t v_isExporting_1327_; 
v_isExporting_1327_ = lean_ctor_get_uint8(v_env_1315_, sizeof(void*)*13);
lean_dec_ref(v_env_1315_);
if (v_isExporting_1327_ == 0)
{
lean_dec(v_a_1318_);
lean_dec(v_id_1308_);
goto v___jp_1322_;
}
else
{
lean_object* v_val_1328_; uint8_t v___x_1329_; 
v_val_1328_ = lean_ctor_get(v_a_1318_, 0);
lean_inc(v_val_1328_);
lean_dec(v_a_1318_);
v___x_1329_ = l_Lean_isPrivateName(v_id_1308_);
if (v___x_1329_ == 0)
{
lean_dec(v_val_1328_);
lean_dec(v_id_1308_);
goto v___jp_1322_;
}
else
{
uint8_t v___x_1330_; 
v___x_1330_ = lean_unbox(v_val_1328_);
lean_dec(v_val_1328_);
if (v___x_1330_ == 0)
{
lean_dec(v_id_1308_);
goto v___jp_1322_;
}
else
{
lean_object* v___x_1331_; uint8_t v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
lean_del_object(v___x_1320_);
v___x_1331_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___closed__1);
v___x_1332_ = 0;
v___x_1333_ = l_Lean_MessageData_ofConstName(v_id_1308_, v___x_1332_);
v___x_1334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1331_);
lean_ctor_set(v___x_1334_, 1, v___x_1333_);
v___x_1335_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___closed__3);
v___x_1336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1334_);
lean_ctor_set(v___x_1336_, 1, v___x_1335_);
v___x_1337_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46(v___x_1336_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_);
return v___x_1337_;
}
}
}
v___jp_1322_:
{
lean_object* v___x_1323_; lean_object* v___x_1325_; 
v___x_1323_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46_spec__48_spec__50___closed__0));
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 0, v___x_1323_);
v___x_1325_ = v___x_1320_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v___x_1323_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___boxed(lean_object* v_id_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42(v_id_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36(lean_object* v_id_1346_, uint8_t v_enableLog_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v___x_1353_; lean_object* v_toCold_1354_; lean_object* v_env_1355_; lean_object* v_currNamespace_1356_; lean_object* v_openDecls_1357_; lean_object* v___x_1358_; lean_object* v_res_1359_; lean_object* v___x_1363_; 
v___x_1353_ = lean_st_ref_get(v___y_1351_);
v_toCold_1354_ = lean_ctor_get(v___y_1350_, 0);
v_env_1355_ = lean_ctor_get(v___x_1353_, 0);
lean_inc_ref(v_env_1355_);
lean_dec(v___x_1353_);
v_currNamespace_1356_ = lean_ctor_get(v_toCold_1354_, 4);
v_openDecls_1357_ = lean_ctor_get(v_toCold_1354_, 5);
v___x_1358_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1350_);
lean_inc(v_openDecls_1357_);
lean_inc(v_currNamespace_1356_);
v_res_1359_ = l_Lean_ResolveName_resolveGlobalName(v_env_1355_, v___x_1358_, v_currNamespace_1356_, v_openDecls_1357_, v_id_1346_);
lean_dec_ref(v___x_1358_);
v___x_1363_ = lean_st_ref_get(v___y_1351_);
if (v_enableLog_1347_ == 0)
{
lean_dec(v___x_1363_);
goto v___jp_1360_;
}
else
{
lean_object* v_env_1364_; uint8_t v_isExporting_1365_; 
v_env_1364_ = lean_ctor_get(v___x_1363_, 0);
lean_inc_ref(v_env_1364_);
lean_dec(v___x_1363_);
v_isExporting_1365_ = lean_ctor_get_uint8(v_env_1364_, sizeof(void*)*13);
lean_dec_ref(v_env_1364_);
if (v_isExporting_1365_ == 0)
{
goto v___jp_1360_;
}
else
{
lean_object* v___x_1366_; 
v___x_1366_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__33(v_res_1359_);
if (lean_obj_tag(v___x_1366_) == 1)
{
lean_object* v_val_1367_; lean_object* v_fst_1368_; lean_object* v___x_1369_; 
v_val_1367_ = lean_ctor_get(v___x_1366_, 0);
lean_inc(v_val_1367_);
lean_dec_ref_known(v___x_1366_, 1);
v_fst_1368_ = lean_ctor_get(v_val_1367_, 0);
lean_inc(v_fst_1368_);
lean_dec(v_val_1367_);
v___x_1369_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42(v_fst_1368_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1378_; 
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1372_ = v___x_1369_;
v_isShared_1373_ = v_isSharedCheck_1378_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1369_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1378_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
if (lean_obj_tag(v_a_1370_) == 0)
{
lean_object* v___x_1374_; lean_object* v___x_1376_; 
lean_dec(v_res_1359_);
v___x_1374_ = lean_box(0);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 0, v___x_1374_);
v___x_1376_ = v___x_1372_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1374_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
else
{
lean_dec_ref_known(v_a_1370_, 1);
lean_del_object(v___x_1372_);
goto v___jp_1360_;
}
}
}
else
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1386_; 
lean_dec(v_res_1359_);
v_a_1379_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1381_ = v___x_1369_;
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1369_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1384_; 
if (v_isShared_1382_ == 0)
{
v___x_1384_ = v___x_1381_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_a_1379_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
}
else
{
lean_dec(v___x_1366_);
goto v___jp_1360_;
}
}
}
v___jp_1360_:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1361_, 0, v_res_1359_);
v___x_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1361_);
return v___x_1362_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36___boxed(lean_object* v_id_1387_, lean_object* v_enableLog_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_){
_start:
{
uint8_t v_enableLog_boxed_1394_; lean_object* v_res_1395_; 
v_enableLog_boxed_1394_ = lean_unbox(v_enableLog_1388_);
v_res_1395_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36(v_id_1387_, v_enableLog_boxed_1394_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_);
lean_dec(v___y_1392_);
lean_dec_ref(v___y_1391_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24___lam__0(lean_object* v___x_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v___x_1402_; 
v___x_1402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1396_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24___lam__0___boxed(lean_object* v___x_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24___lam__0(v___x_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27(lean_object* v_n_u2080_1414_, lean_object* v_filter_1415_, lean_object* v_view_x3f_1416_, lean_object* v_n_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1493_; 
if (lean_obj_tag(v_view_x3f_1416_) == 1)
{
lean_object* v_val_1520_; lean_object* v_imported_1521_; lean_object* v_ctx_1522_; lean_object* v_scopes_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1531_; 
v_val_1520_ = lean_ctor_get(v_view_x3f_1416_, 0);
lean_inc(v_val_1520_);
lean_dec_ref_known(v_view_x3f_1416_, 1);
v_imported_1521_ = lean_ctor_get(v_val_1520_, 1);
v_ctx_1522_ = lean_ctor_get(v_val_1520_, 2);
v_scopes_1523_ = lean_ctor_get(v_val_1520_, 3);
v_isSharedCheck_1531_ = !lean_is_exclusive(v_val_1520_);
if (v_isSharedCheck_1531_ == 0)
{
lean_object* v_unused_1532_; 
v_unused_1532_ = lean_ctor_get(v_val_1520_, 0);
lean_dec(v_unused_1532_);
v___x_1525_ = v_val_1520_;
v_isShared_1526_ = v_isSharedCheck_1531_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_scopes_1523_);
lean_inc(v_ctx_1522_);
lean_inc(v_imported_1521_);
lean_dec(v_val_1520_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1531_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1528_; 
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 0, v_n_1417_);
v___x_1528_ = v___x_1525_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_n_1417_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v_imported_1521_);
lean_ctor_set(v_reuseFailAlloc_1530_, 2, v_ctx_1522_);
lean_ctor_set(v_reuseFailAlloc_1530_, 3, v_scopes_1523_);
v___x_1528_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
lean_object* v___x_1529_; 
v___x_1529_ = l_Lean_MacroScopesView_review(v___x_1528_);
v___y_1493_ = v___x_1529_;
goto v___jp_1492_;
}
}
}
else
{
lean_dec(v_view_x3f_1416_);
v___y_1493_ = v_n_1417_;
goto v___jp_1492_;
}
v___jp_1423_:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1424_ = lean_box(0);
v___x_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1424_);
return v___x_1425_;
}
v___jp_1426_:
{
lean_object* v___x_1429_; 
lean_inc_ref(v___y_1428_);
lean_inc(v___y_1421_);
lean_inc_ref(v___y_1420_);
lean_inc(v___y_1419_);
lean_inc_ref(v___y_1418_);
v___x_1429_ = lean_apply_5(v___y_1428_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, lean_box(0));
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1449_; 
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1432_ = v___x_1429_;
v_isShared_1433_ = v_isSharedCheck_1449_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1429_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1449_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
if (lean_obj_tag(v_a_1430_) == 0)
{
lean_object* v___x_1434_; lean_object* v___x_1436_; 
lean_dec(v___y_1427_);
v___x_1434_ = lean_box(0);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 0, v___x_1434_);
v___x_1436_ = v___x_1432_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1434_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
else
{
lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1447_; 
v_isSharedCheck_1447_ = !lean_is_exclusive(v_a_1430_);
if (v_isSharedCheck_1447_ == 0)
{
lean_object* v_unused_1448_; 
v_unused_1448_ = lean_ctor_get(v_a_1430_, 0);
lean_dec(v_unused_1448_);
v___x_1439_ = v_a_1430_;
v_isShared_1440_ = v_isSharedCheck_1447_;
goto v_resetjp_1438_;
}
else
{
lean_dec(v_a_1430_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1447_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1442_; 
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 0, v___y_1427_);
v___x_1442_ = v___x_1439_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___y_1427_);
v___x_1442_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
lean_object* v___x_1444_; 
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 0, v___x_1442_);
v___x_1444_ = v___x_1432_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1442_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
}
}
else
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
lean_dec(v___y_1427_);
v_a_1450_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1452_ = v___x_1429_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1429_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1450_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
v___jp_1458_:
{
lean_object* v___x_1461_; 
lean_inc_ref(v___y_1460_);
lean_inc(v___y_1421_);
lean_inc_ref(v___y_1420_);
lean_inc(v___y_1419_);
lean_inc_ref(v___y_1418_);
v___x_1461_ = lean_apply_5(v___y_1460_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, lean_box(0));
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v_a_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1483_; 
v_a_1462_ = lean_ctor_get(v___x_1461_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1464_ = v___x_1461_;
v_isShared_1465_ = v_isSharedCheck_1483_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_a_1462_);
lean_dec(v___x_1461_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1483_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
if (lean_obj_tag(v_a_1462_) == 0)
{
lean_object* v___x_1466_; lean_object* v___x_1468_; 
lean_dec(v___y_1459_);
lean_dec_ref(v_filter_1415_);
v___x_1466_ = lean_box(0);
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 0, v___x_1466_);
v___x_1468_ = v___x_1464_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v___x_1466_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
else
{
lean_object* v___x_1470_; 
lean_dec_ref_known(v_a_1462_, 1);
lean_del_object(v___x_1464_);
lean_inc(v___y_1421_);
lean_inc_ref(v___y_1420_);
lean_inc(v___y_1419_);
lean_inc_ref(v___y_1418_);
lean_inc(v___y_1459_);
v___x_1470_ = lean_apply_6(v_filter_1415_, v___y_1459_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, lean_box(0));
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_a_1471_; uint8_t v___x_1472_; 
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
lean_inc(v_a_1471_);
lean_dec_ref_known(v___x_1470_, 1);
v___x_1472_ = lean_unbox(v_a_1471_);
lean_dec(v_a_1471_);
if (v___x_1472_ == 0)
{
lean_object* v___f_1473_; 
v___f_1473_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27___closed__0));
v___y_1427_ = v___y_1459_;
v___y_1428_ = v___f_1473_;
goto v___jp_1426_;
}
else
{
lean_object* v___f_1474_; 
v___f_1474_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27___closed__1));
v___y_1427_ = v___y_1459_;
v___y_1428_ = v___f_1474_;
goto v___jp_1426_;
}
}
else
{
lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1482_; 
lean_dec(v___y_1459_);
v_a_1475_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1477_ = v___x_1470_;
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v___x_1470_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1480_; 
if (v_isShared_1478_ == 0)
{
v___x_1480_ = v___x_1477_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_a_1475_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
}
}
}
else
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1491_; 
lean_dec(v___y_1459_);
lean_dec_ref(v_filter_1415_);
v_a_1484_ = lean_ctor_get(v___x_1461_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1486_ = v___x_1461_;
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v___x_1461_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1489_; 
if (v_isShared_1487_ == 0)
{
v___x_1489_ = v___x_1486_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_a_1484_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
}
v___jp_1492_:
{
uint8_t v___x_1494_; lean_object* v___x_1495_; 
v___x_1494_ = 0;
lean_inc(v___y_1493_);
v___x_1495_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36(v___y_1493_, v___x_1494_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1511_; 
v_a_1496_ = lean_ctor_get(v___x_1495_, 0);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1498_ = v___x_1495_;
v_isShared_1499_ = v_isSharedCheck_1511_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v___x_1495_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1511_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
if (lean_obj_tag(v_a_1496_) == 0)
{
lean_object* v___x_1500_; lean_object* v___x_1502_; 
lean_dec(v___y_1493_);
lean_dec_ref(v_filter_1415_);
v___x_1500_ = lean_box(0);
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 0, v___x_1500_);
v___x_1502_ = v___x_1498_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v___x_1500_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
else
{
lean_object* v_val_1504_; 
lean_del_object(v___x_1498_);
v_val_1504_ = lean_ctor_get(v_a_1496_, 0);
lean_inc(v_val_1504_);
lean_dec_ref_known(v_a_1496_, 1);
if (lean_obj_tag(v_val_1504_) == 1)
{
lean_object* v_head_1505_; lean_object* v_tail_1506_; 
v_head_1505_ = lean_ctor_get(v_val_1504_, 0);
lean_inc(v_head_1505_);
v_tail_1506_ = lean_ctor_get(v_val_1504_, 1);
lean_inc(v_tail_1506_);
lean_dec_ref_known(v_val_1504_, 2);
if (lean_obj_tag(v_tail_1506_) == 0)
{
lean_object* v_fst_1507_; uint8_t v___x_1508_; 
v_fst_1507_ = lean_ctor_get(v_head_1505_, 0);
lean_inc(v_fst_1507_);
lean_dec(v_head_1505_);
v___x_1508_ = lean_name_eq(v_fst_1507_, v_n_u2080_1414_);
lean_dec(v_fst_1507_);
if (v___x_1508_ == 0)
{
lean_object* v___f_1509_; 
v___f_1509_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27___closed__0));
v___y_1459_ = v___y_1493_;
v___y_1460_ = v___f_1509_;
goto v___jp_1458_;
}
else
{
lean_object* v___f_1510_; 
v___f_1510_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27___closed__1));
v___y_1459_ = v___y_1493_;
v___y_1460_ = v___f_1510_;
goto v___jp_1458_;
}
}
else
{
lean_dec(v_tail_1506_);
lean_dec(v_head_1505_);
lean_dec(v___y_1493_);
lean_dec_ref(v_filter_1415_);
goto v___jp_1423_;
}
}
else
{
lean_dec(v_val_1504_);
lean_dec(v___y_1493_);
lean_dec_ref(v_filter_1415_);
goto v___jp_1423_;
}
}
}
}
else
{
lean_object* v_a_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1519_; 
lean_dec(v___y_1493_);
lean_dec_ref(v_filter_1415_);
v_a_1512_ = lean_ctor_get(v___x_1495_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1514_ = v___x_1495_;
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_a_1512_);
lean_dec(v___x_1495_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1517_; 
if (v_isShared_1515_ == 0)
{
v___x_1517_ = v___x_1514_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_a_1512_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27___boxed(lean_object* v_n_u2080_1533_, lean_object* v_filter_1534_, lean_object* v_view_x3f_1535_, lean_object* v_n_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
lean_object* v_res_1542_; 
v_res_1542_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27(v_n_u2080_1533_, v_filter_1534_, v_view_x3f_1535_, v_n_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v_n_u2080_1533_);
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24_spec__32___redArg(lean_object* v_n_u2080_1543_, lean_object* v_filter_1544_, lean_object* v_view_x3f_1545_, lean_object* v_as_x27_1546_, lean_object* v_b_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
if (lean_obj_tag(v_as_x27_1546_) == 0)
{
lean_object* v___x_1553_; lean_object* v___x_1554_; 
lean_dec(v_view_x3f_1545_);
lean_dec_ref(v_filter_1544_);
v___x_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1553_, 0, v_b_1547_);
v___x_1554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1553_);
return v___x_1554_;
}
else
{
lean_object* v_head_1555_; lean_object* v_tail_1556_; lean_object* v_snd_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1595_; 
v_head_1555_ = lean_ctor_get(v_as_x27_1546_, 0);
v_tail_1556_ = lean_ctor_get(v_as_x27_1546_, 1);
v_snd_1557_ = lean_ctor_get(v_b_1547_, 1);
v_isSharedCheck_1595_ = !lean_is_exclusive(v_b_1547_);
if (v_isSharedCheck_1595_ == 0)
{
lean_object* v_unused_1596_; 
v_unused_1596_ = lean_ctor_get(v_b_1547_, 0);
lean_dec(v_unused_1596_);
v___x_1559_ = v_b_1547_;
v_isShared_1560_ = v_isSharedCheck_1595_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_snd_1557_);
lean_dec(v_b_1547_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1595_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1561_ = lean_box(0);
v___x_1562_ = l_Lean_Name_appendCore(v_head_1555_, v_snd_1557_);
lean_inc(v___x_1562_);
lean_inc(v_view_x3f_1545_);
lean_inc_ref(v_filter_1544_);
v___x_1563_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27(v_n_u2080_1543_, v_filter_1544_, v_view_x3f_1545_, v___x_1562_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1586_; 
v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1566_ = v___x_1563_;
v_isShared_1567_ = v_isSharedCheck_1586_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1563_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1586_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
if (lean_obj_tag(v_a_1564_) == 0)
{
lean_object* v___x_1569_; 
lean_del_object(v___x_1566_);
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 1, v___x_1562_);
lean_ctor_set(v___x_1559_, 0, v___x_1561_);
v___x_1569_ = v___x_1559_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1561_);
lean_ctor_set(v_reuseFailAlloc_1571_, 1, v___x_1562_);
v___x_1569_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
v_as_x27_1546_ = v_tail_1556_;
v_b_1547_ = v___x_1569_;
goto _start;
}
}
else
{
lean_object* v___x_1573_; 
lean_dec(v_view_x3f_1545_);
lean_dec_ref(v_filter_1544_);
lean_inc_ref(v_a_1564_);
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 1, v___x_1562_);
lean_ctor_set(v___x_1559_, 0, v_a_1564_);
v___x_1573_ = v___x_1559_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_a_1564_);
lean_ctor_set(v_reuseFailAlloc_1585_, 1, v___x_1562_);
v___x_1573_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1583_; 
v_isSharedCheck_1583_ = !lean_is_exclusive(v_a_1564_);
if (v_isSharedCheck_1583_ == 0)
{
lean_object* v_unused_1584_; 
v_unused_1584_ = lean_ctor_get(v_a_1564_, 0);
lean_dec(v_unused_1584_);
v___x_1575_ = v_a_1564_;
v_isShared_1576_ = v_isSharedCheck_1583_;
goto v_resetjp_1574_;
}
else
{
lean_dec(v_a_1564_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1583_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1578_; 
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 0, v___x_1573_);
v___x_1578_ = v___x_1575_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v___x_1573_);
v___x_1578_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
lean_object* v___x_1580_; 
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 0, v___x_1578_);
v___x_1580_ = v___x_1566_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v___x_1578_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1594_; 
lean_dec(v___x_1562_);
lean_del_object(v___x_1559_);
lean_dec(v_view_x3f_1545_);
lean_dec_ref(v_filter_1544_);
v_a_1587_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1589_ = v___x_1563_;
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v___x_1563_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1592_; 
if (v_isShared_1590_ == 0)
{
v___x_1592_ = v___x_1589_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1587_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24_spec__32___redArg___boxed(lean_object* v_n_u2080_1597_, lean_object* v_filter_1598_, lean_object* v_view_x3f_1599_, lean_object* v_as_x27_1600_, lean_object* v_b_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24_spec__32___redArg(v_n_u2080_1597_, v_filter_1598_, v_view_x3f_1599_, v_as_x27_1600_, v_b_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_dec(v_as_x27_1600_);
lean_dec(v_n_u2080_1597_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24(lean_object* v_n_u2080_1611_, lean_object* v_filter_1612_, lean_object* v_view_x3f_1613_, lean_object* v_n_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_){
_start:
{
lean_object* v___y_1621_; uint8_t v___x_1662_; 
v___x_1662_ = l_Lean_Name_hasMacroScopes(v_n_1614_);
if (v___x_1662_ == 0)
{
lean_object* v___f_1663_; 
v___f_1663_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27___closed__1));
v___y_1621_ = v___f_1663_;
goto v___jp_1620_;
}
else
{
lean_object* v___f_1664_; 
v___f_1664_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27___closed__0));
v___y_1621_ = v___f_1664_;
goto v___jp_1620_;
}
v___jp_1620_:
{
lean_object* v___x_1622_; 
lean_inc_ref(v___y_1621_);
lean_inc(v___y_1618_);
lean_inc_ref(v___y_1617_);
lean_inc(v___y_1616_);
lean_inc_ref(v___y_1615_);
v___x_1622_ = lean_apply_5(v___y_1621_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, lean_box(0));
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1653_; 
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1625_ = v___x_1622_;
v_isShared_1626_ = v_isSharedCheck_1653_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1622_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1653_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
if (lean_obj_tag(v_a_1623_) == 0)
{
lean_object* v___x_1627_; lean_object* v___x_1629_; 
lean_dec(v_n_1614_);
lean_dec(v_view_x3f_1613_);
lean_dec_ref(v_filter_1612_);
v___x_1627_ = lean_box(0);
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 0, v___x_1627_);
v___x_1629_ = v___x_1625_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v___x_1627_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
else
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
lean_dec_ref_known(v_a_1623_, 1);
lean_del_object(v___x_1625_);
v___x_1631_ = l_Lean_privateToUserName(v_n_1614_);
v___x_1632_ = l_Lean_Name_componentsRev(v___x_1631_);
v___x_1633_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24___closed__0));
v___x_1634_ = l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24_spec__32___redArg(v_n_u2080_1611_, v_filter_1612_, v_view_x3f_1613_, v___x_1632_, v___x_1633_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_);
lean_dec(v___x_1632_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1644_; 
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1637_ = v___x_1634_;
v_isShared_1638_ = v_isSharedCheck_1644_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1634_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1644_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v_val_1639_; lean_object* v_fst_1640_; lean_object* v___x_1642_; 
v_val_1639_ = lean_ctor_get(v_a_1635_, 0);
lean_inc(v_val_1639_);
lean_dec(v_a_1635_);
v_fst_1640_ = lean_ctor_get(v_val_1639_, 0);
lean_inc(v_fst_1640_);
lean_dec(v_val_1639_);
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 0, v_fst_1640_);
v___x_1642_ = v___x_1637_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_fst_1640_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
else
{
lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1652_; 
v_a_1645_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1647_ = v___x_1634_;
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_dec(v___x_1634_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1650_; 
if (v_isShared_1648_ == 0)
{
v___x_1650_ = v___x_1647_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_a_1645_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
}
}
}
else
{
lean_object* v_a_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1661_; 
lean_dec(v_n_1614_);
lean_dec(v_view_x3f_1613_);
lean_dec_ref(v_filter_1612_);
v_a_1654_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1656_ = v___x_1622_;
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_a_1654_);
lean_dec(v___x_1622_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1659_; 
if (v_isShared_1657_ == 0)
{
v___x_1659_ = v___x_1656_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_a_1654_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24___boxed(lean_object* v_n_u2080_1665_, lean_object* v_filter_1666_, lean_object* v_view_x3f_1667_, lean_object* v_n_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24(v_n_u2080_1665_, v_filter_1666_, v_view_x3f_1667_, v_n_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
lean_dec(v_n_u2080_1665_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__25(lean_object* v_n_u2080_1675_, lean_object* v_filter_1676_, lean_object* v_as_1677_, lean_object* v_i_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v___x_1684_; uint8_t v___x_1685_; 
v___x_1684_ = lean_array_get_size(v_as_1677_);
v___x_1685_ = lean_nat_dec_lt(v_i_1678_, v___x_1684_);
if (v___x_1685_ == 0)
{
lean_object* v___x_1686_; lean_object* v___x_1687_; 
lean_dec(v_i_1678_);
lean_dec_ref(v_filter_1676_);
v___x_1686_ = lean_box(0);
v___x_1687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1686_);
return v___x_1687_;
}
else
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1688_ = lean_box(0);
v___x_1689_ = lean_array_fget_borrowed(v_as_1677_, v_i_1678_);
lean_inc(v___x_1689_);
lean_inc_ref(v_filter_1676_);
v___x_1690_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24(v_n_u2080_1675_, v_filter_1676_, v___x_1688_, v___x_1689_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v_a_1691_; 
v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
if (lean_obj_tag(v_a_1691_) == 0)
{
lean_object* v___x_1692_; lean_object* v___x_1693_; 
lean_dec_ref_known(v___x_1690_, 1);
v___x_1692_ = lean_unsigned_to_nat(1u);
v___x_1693_ = lean_nat_add(v_i_1678_, v___x_1692_);
lean_dec(v_i_1678_);
v_i_1678_ = v___x_1693_;
goto _start;
}
else
{
lean_dec(v_i_1678_);
lean_dec_ref(v_filter_1676_);
return v___x_1690_;
}
}
else
{
lean_dec(v_i_1678_);
lean_dec_ref(v_filter_1676_);
return v___x_1690_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__25___boxed(lean_object* v_n_u2080_1695_, lean_object* v_filter_1696_, lean_object* v_as_1697_, lean_object* v_i_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__25(v_n_u2080_1695_, v_filter_1696_, v_as_1697_, v_i_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec_ref(v_as_1697_);
lean_dec(v_n_u2080_1695_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__26(lean_object* v_n_u2081_1705_, lean_object* v_as_1706_, size_t v_i_1707_, size_t v_stop_1708_, lean_object* v_b_1709_){
_start:
{
lean_object* v___y_1711_; uint8_t v___x_1715_; 
v___x_1715_ = lean_usize_dec_eq(v_i_1707_, v_stop_1708_);
if (v___x_1715_ == 0)
{
lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; uint8_t v___x_1719_; 
v___x_1716_ = lean_array_uget_borrowed(v_as_1706_, v_i_1707_);
v___x_1717_ = l_Lean_Name_getPrefix(v___x_1716_);
v___x_1718_ = l_Lean_Name_getPrefix(v_n_u2081_1705_);
v___x_1719_ = l_Lean_Name_isPrefixOf(v___x_1717_, v___x_1718_);
lean_dec(v___x_1718_);
lean_dec(v___x_1717_);
if (v___x_1719_ == 0)
{
v___y_1711_ = v_b_1709_;
goto v___jp_1710_;
}
else
{
lean_object* v___x_1720_; 
lean_inc(v___x_1716_);
v___x_1720_ = lean_array_push(v_b_1709_, v___x_1716_);
v___y_1711_ = v___x_1720_;
goto v___jp_1710_;
}
}
else
{
return v_b_1709_;
}
v___jp_1710_:
{
size_t v___x_1712_; size_t v___x_1713_; 
v___x_1712_ = ((size_t)1ULL);
v___x_1713_ = lean_usize_add(v_i_1707_, v___x_1712_);
v_i_1707_ = v___x_1713_;
v_b_1709_ = v___y_1711_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__26___boxed(lean_object* v_n_u2081_1721_, lean_object* v_as_1722_, lean_object* v_i_1723_, lean_object* v_stop_1724_, lean_object* v_b_1725_){
_start:
{
size_t v_i_boxed_1726_; size_t v_stop_boxed_1727_; lean_object* v_res_1728_; 
v_i_boxed_1726_ = lean_unbox_usize(v_i_1723_);
lean_dec(v_i_1723_);
v_stop_boxed_1727_ = lean_unbox_usize(v_stop_1724_);
lean_dec(v_stop_1724_);
v_res_1728_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__26(v_n_u2081_1721_, v_as_1722_, v_i_boxed_1726_, v_stop_boxed_1727_, v_b_1725_);
lean_dec_ref(v_as_1722_);
lean_dec(v_n_u2081_1721_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14(lean_object* v_n_u2080_1731_, uint8_t v_fullNames_1732_, uint8_t v_allowHorizAliases_1733_, lean_object* v_filter_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v_view_1740_; lean_object* v_name_1741_; lean_object* v_n_u2081_1742_; 
lean_inc(v_n_u2080_1731_);
v_view_1740_ = l_Lean_extractMacroScopes(v_n_u2080_1731_);
v_name_1741_ = lean_ctor_get(v_view_1740_, 0);
lean_inc(v_name_1741_);
v_n_u2081_1742_ = l_Lean_privateToUserName(v_name_1741_);
if (v_fullNames_1732_ == 0)
{
lean_object* v___x_1743_; lean_object* v_aliases_1745_; lean_object* v_env_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1743_ = lean_st_ref_get(v___y_1738_);
v_env_1760_ = lean_ctor_get(v___x_1743_, 0);
lean_inc_ref(v_env_1760_);
lean_dec(v___x_1743_);
lean_inc(v_n_u2080_1731_);
v___x_1761_ = l_Lean_getRevAliases(v_env_1760_, v_n_u2080_1731_);
v___x_1762_ = lean_array_mk(v___x_1761_);
if (v_allowHorizAliases_1733_ == 0)
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; uint8_t v___x_1766_; 
v___x_1763_ = lean_unsigned_to_nat(0u);
v___x_1764_ = lean_array_get_size(v___x_1762_);
v___x_1765_ = ((lean_object*)(l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14___closed__0));
v___x_1766_ = lean_nat_dec_lt(v___x_1763_, v___x_1764_);
if (v___x_1766_ == 0)
{
lean_dec_ref(v___x_1762_);
v_aliases_1745_ = v___x_1765_;
goto v___jp_1744_;
}
else
{
size_t v___x_1767_; size_t v___x_1768_; lean_object* v___x_1769_; 
v___x_1767_ = ((size_t)0ULL);
v___x_1768_ = lean_usize_of_nat(v___x_1764_);
v___x_1769_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__26(v_n_u2081_1742_, v___x_1762_, v___x_1767_, v___x_1768_, v___x_1765_);
lean_dec_ref(v___x_1762_);
v_aliases_1745_ = v___x_1769_;
goto v___jp_1744_;
}
}
else
{
v_aliases_1745_ = v___x_1762_;
goto v___jp_1744_;
}
v___jp_1744_:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; 
v___x_1746_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_filter_1734_);
v___x_1747_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__25(v_n_u2080_1731_, v_filter_1734_, v_aliases_1745_, v___x_1746_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
lean_dec_ref(v_aliases_1745_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v_a_1748_; 
v_a_1748_ = lean_ctor_get(v___x_1747_, 0);
if (lean_obj_tag(v_a_1748_) == 0)
{
lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1758_; 
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1758_ == 0)
{
lean_object* v_unused_1759_; 
v_unused_1759_ = lean_ctor_get(v___x_1747_, 0);
lean_dec(v_unused_1759_);
v___x_1750_ = v___x_1747_;
v_isShared_1751_ = v_isSharedCheck_1758_;
goto v_resetjp_1749_;
}
else
{
lean_dec(v___x_1747_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1758_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1753_; 
if (v_isShared_1751_ == 0)
{
lean_ctor_set_tag(v___x_1750_, 1);
lean_ctor_set(v___x_1750_, 0, v_view_1740_);
v___x_1753_ = v___x_1750_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_view_1740_);
v___x_1753_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1754_ = l_Lean_rootNamespace;
v___x_1755_ = l_Lean_Name_append(v___x_1754_, v_n_u2081_1742_);
v___x_1756_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24(v_n_u2080_1731_, v_filter_1734_, v___x_1753_, v___x_1755_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
lean_dec(v_n_u2080_1731_);
return v___x_1756_;
}
}
}
else
{
lean_dec(v_n_u2081_1742_);
lean_dec_ref(v_view_1740_);
lean_dec_ref(v_filter_1734_);
lean_dec(v_n_u2080_1731_);
return v___x_1747_;
}
}
else
{
lean_dec(v_n_u2081_1742_);
lean_dec_ref(v_view_1740_);
lean_dec_ref(v_filter_1734_);
lean_dec(v_n_u2080_1731_);
return v___x_1747_;
}
}
}
else
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1770_, 0, v_view_1740_);
lean_inc(v_n_u2081_1742_);
lean_inc_ref(v___x_1770_);
lean_inc_ref(v_filter_1734_);
v___x_1771_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27(v_n_u2080_1731_, v_filter_1734_, v___x_1770_, v_n_u2081_1742_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v_a_1772_; 
v_a_1772_ = lean_ctor_get(v___x_1771_, 0);
if (lean_obj_tag(v_a_1772_) == 0)
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
lean_dec_ref_known(v___x_1771_, 1);
v___x_1773_ = l_Lean_rootNamespace;
v___x_1774_ = l_Lean_Name_append(v___x_1773_, v_n_u2081_1742_);
v___x_1775_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27(v_n_u2080_1731_, v_filter_1734_, v___x_1770_, v___x_1774_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
lean_dec(v_n_u2080_1731_);
return v___x_1775_;
}
else
{
lean_dec_ref_known(v___x_1770_, 1);
lean_dec(v_n_u2081_1742_);
lean_dec_ref(v_filter_1734_);
lean_dec(v_n_u2080_1731_);
return v___x_1771_;
}
}
else
{
lean_dec_ref_known(v___x_1770_, 1);
lean_dec(v_n_u2081_1742_);
lean_dec_ref(v_filter_1734_);
lean_dec(v_n_u2080_1731_);
return v___x_1771_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14___boxed(lean_object* v_n_u2080_1776_, lean_object* v_fullNames_1777_, lean_object* v_allowHorizAliases_1778_, lean_object* v_filter_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_){
_start:
{
uint8_t v_fullNames_boxed_1785_; uint8_t v_allowHorizAliases_boxed_1786_; lean_object* v_res_1787_; 
v_fullNames_boxed_1785_ = lean_unbox(v_fullNames_1777_);
v_allowHorizAliases_boxed_1786_ = lean_unbox(v_allowHorizAliases_1778_);
v_res_1787_ = l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14(v_n_u2080_1776_, v_fullNames_boxed_1785_, v_allowHorizAliases_boxed_1786_, v_filter_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
return v_res_1787_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__29(lean_object* v_snd_1788_, lean_object* v_x_1789_){
_start:
{
if (lean_obj_tag(v_x_1789_) == 0)
{
uint8_t v___x_1790_; 
v___x_1790_ = 0;
return v___x_1790_;
}
else
{
lean_object* v_head_1791_; lean_object* v_tail_1792_; lean_object* v_snd_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; uint8_t v___x_1796_; 
v_head_1791_ = lean_ctor_get(v_x_1789_, 0);
v_tail_1792_ = lean_ctor_get(v_x_1789_, 1);
v_snd_1793_ = lean_ctor_get(v_head_1791_, 1);
v___x_1794_ = l_List_lengthTR___redArg(v_snd_1793_);
v___x_1795_ = l_List_lengthTR___redArg(v_snd_1788_);
v___x_1796_ = lean_nat_dec_lt(v___x_1794_, v___x_1795_);
lean_dec(v___x_1795_);
lean_dec(v___x_1794_);
if (v___x_1796_ == 0)
{
v_x_1789_ = v_tail_1792_;
goto _start;
}
else
{
return v___x_1796_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__29___boxed(lean_object* v_snd_1798_, lean_object* v_x_1799_){
_start:
{
uint8_t v_res_1800_; lean_object* v_r_1801_; 
v_res_1800_ = l_List_any___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__29(v_snd_1798_, v_x_1799_);
lean_dec(v_x_1799_);
lean_dec(v_snd_1798_);
v_r_1801_ = lean_box(v_res_1800_);
return v_r_1801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__39___redArg(lean_object* v_opt_1802_, lean_object* v___y_1803_){
_start:
{
lean_object* v___x_1805_; uint8_t v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1805_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1803_);
v___x_1806_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__5(v___x_1805_, v_opt_1802_);
lean_dec_ref(v___x_1805_);
v___x_1807_ = lean_box(v___x_1806_);
v___x_1808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1807_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__39___redArg___boxed(lean_object* v_opt_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__39___redArg(v_opt_1809_, v___y_1810_);
lean_dec_ref(v___y_1810_);
lean_dec_ref(v_opt_1809_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44_spec__46(lean_object* v_ref_1813_, lean_object* v_msgData_1814_, uint8_t v_severity_1815_, uint8_t v_isSilent_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_){
_start:
{
uint8_t v___y_1823_; uint8_t v___y_1824_; lean_object* v___y_1825_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v_toCold_1830_; lean_object* v___y_1831_; lean_object* v___y_1860_; lean_object* v___y_1861_; uint8_t v___y_1862_; uint8_t v___y_1863_; lean_object* v___y_1864_; uint8_t v___y_1865_; lean_object* v___y_1866_; lean_object* v___y_1867_; lean_object* v___y_1887_; uint8_t v___y_1888_; lean_object* v___y_1889_; uint8_t v___y_1890_; uint8_t v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1893_; uint8_t v___y_1897_; uint8_t v___y_1898_; uint8_t v___x_1908_; uint8_t v___y_1910_; uint8_t v___x_1916_; 
v___x_1908_ = 2;
v___x_1916_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1815_, v___x_1908_);
if (v___x_1916_ == 0)
{
v___y_1910_ = v___x_1916_;
goto v___jp_1909_;
}
else
{
uint8_t v___x_1917_; 
lean_inc_ref(v_msgData_1814_);
v___x_1917_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1814_);
if (v___x_1917_ == 0)
{
v___y_1910_ = v___x_1917_;
goto v___jp_1909_;
}
else
{
lean_object* v___x_1918_; lean_object* v___x_1919_; 
lean_dec_ref(v_msgData_1814_);
v___x_1918_ = lean_box(0);
v___x_1919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1918_);
return v___x_1919_;
}
}
v___jp_1822_:
{
lean_object* v_currNamespace_1832_; lean_object* v_openDecls_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v_env_1838_; lean_object* v_nextMacroScope_1839_; lean_object* v_ngen_1840_; lean_object* v_auxDeclNGen_1841_; lean_object* v_traceState_1842_; lean_object* v_cache_1843_; lean_object* v_recordedDeps_1844_; lean_object* v_messages_1845_; lean_object* v_infoState_1846_; lean_object* v_snapshotTasks_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1858_; 
v_currNamespace_1832_ = lean_ctor_get(v_toCold_1830_, 4);
v_openDecls_1833_ = lean_ctor_get(v_toCold_1830_, 5);
lean_inc(v_openDecls_1833_);
lean_inc(v_currNamespace_1832_);
v___x_1834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1834_, 0, v_currNamespace_1832_);
lean_ctor_set(v___x_1834_, 1, v_openDecls_1833_);
v___x_1835_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1834_);
lean_ctor_set(v___x_1835_, 1, v___y_1829_);
lean_inc_ref(v___y_1826_);
lean_inc_ref(v___y_1828_);
v___x_1836_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1836_, 0, v___y_1828_);
lean_ctor_set(v___x_1836_, 1, v___y_1827_);
lean_ctor_set(v___x_1836_, 2, v___y_1825_);
lean_ctor_set(v___x_1836_, 3, v___y_1826_);
lean_ctor_set(v___x_1836_, 4, v___x_1835_);
lean_ctor_set_uint8(v___x_1836_, sizeof(void*)*5, v___y_1823_);
lean_ctor_set_uint8(v___x_1836_, sizeof(void*)*5 + 1, v___y_1824_);
lean_ctor_set_uint8(v___x_1836_, sizeof(void*)*5 + 2, v_isSilent_1816_);
v___x_1837_ = lean_st_ref_take(v___y_1831_);
v_env_1838_ = lean_ctor_get(v___x_1837_, 0);
v_nextMacroScope_1839_ = lean_ctor_get(v___x_1837_, 1);
v_ngen_1840_ = lean_ctor_get(v___x_1837_, 2);
v_auxDeclNGen_1841_ = lean_ctor_get(v___x_1837_, 3);
v_traceState_1842_ = lean_ctor_get(v___x_1837_, 4);
v_cache_1843_ = lean_ctor_get(v___x_1837_, 5);
v_recordedDeps_1844_ = lean_ctor_get(v___x_1837_, 6);
v_messages_1845_ = lean_ctor_get(v___x_1837_, 7);
v_infoState_1846_ = lean_ctor_get(v___x_1837_, 8);
v_snapshotTasks_1847_ = lean_ctor_get(v___x_1837_, 9);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1849_ = v___x_1837_;
v_isShared_1850_ = v_isSharedCheck_1858_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_snapshotTasks_1847_);
lean_inc(v_infoState_1846_);
lean_inc(v_messages_1845_);
lean_inc(v_recordedDeps_1844_);
lean_inc(v_cache_1843_);
lean_inc(v_traceState_1842_);
lean_inc(v_auxDeclNGen_1841_);
lean_inc(v_ngen_1840_);
lean_inc(v_nextMacroScope_1839_);
lean_inc(v_env_1838_);
lean_dec(v___x_1837_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1858_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1854_; 
v___x_1851_ = lean_box(0);
v___x_1852_ = l_Lean_MessageLog_add(v___x_1836_, v_messages_1845_);
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 7, v___x_1852_);
v___x_1854_ = v___x_1849_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_env_1838_);
lean_ctor_set(v_reuseFailAlloc_1857_, 1, v_nextMacroScope_1839_);
lean_ctor_set(v_reuseFailAlloc_1857_, 2, v_ngen_1840_);
lean_ctor_set(v_reuseFailAlloc_1857_, 3, v_auxDeclNGen_1841_);
lean_ctor_set(v_reuseFailAlloc_1857_, 4, v_traceState_1842_);
lean_ctor_set(v_reuseFailAlloc_1857_, 5, v_cache_1843_);
lean_ctor_set(v_reuseFailAlloc_1857_, 6, v_recordedDeps_1844_);
lean_ctor_set(v_reuseFailAlloc_1857_, 7, v___x_1852_);
lean_ctor_set(v_reuseFailAlloc_1857_, 8, v_infoState_1846_);
lean_ctor_set(v_reuseFailAlloc_1857_, 9, v_snapshotTasks_1847_);
v___x_1854_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1855_ = lean_st_ref_put(v___y_1831_, v___x_1854_);
v___x_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1851_);
return v___x_1856_;
}
}
}
v___jp_1859_:
{
lean_object* v_fileName_1868_; lean_object* v_fileMap_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1885_; 
v_fileName_1868_ = lean_ctor_get(v___y_1864_, 0);
v_fileMap_1869_ = lean_ctor_get(v___y_1864_, 1);
v___x_1870_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1814_);
v___x_1871_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44_spec__46_spec__49(v___x_1870_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
v_a_1872_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1874_ = v___x_1871_;
v_isShared_1875_ = v_isSharedCheck_1885_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v___x_1871_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1885_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
lean_inc_ref_n(v_fileMap_1869_, 2);
v___x_1876_ = l_Lean_FileMap_toPosition(v_fileMap_1869_, v___y_1866_);
lean_dec(v___y_1866_);
v___x_1877_ = l_Lean_FileMap_toPosition(v_fileMap_1869_, v___y_1867_);
lean_dec(v___y_1867_);
v___x_1878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1877_);
v___x_1879_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__1));
if (v___y_1865_ == 0)
{
lean_del_object(v___x_1874_);
lean_dec_ref(v___y_1861_);
v___y_1823_ = v___y_1862_;
v___y_1824_ = v___y_1863_;
v___y_1825_ = v___x_1878_;
v___y_1826_ = v___x_1879_;
v___y_1827_ = v___x_1876_;
v___y_1828_ = v_fileName_1868_;
v___y_1829_ = v_a_1872_;
v_toCold_1830_ = v___y_1860_;
v___y_1831_ = v___y_1820_;
goto v___jp_1822_;
}
else
{
uint8_t v___x_1880_; 
lean_inc(v_a_1872_);
v___x_1880_ = l_Lean_MessageData_hasTag(v___y_1861_, v_a_1872_);
if (v___x_1880_ == 0)
{
lean_object* v___x_1881_; lean_object* v___x_1883_; 
lean_dec_ref_known(v___x_1878_, 1);
lean_dec_ref(v___x_1876_);
lean_dec(v_a_1872_);
v___x_1881_ = lean_box(0);
if (v_isShared_1875_ == 0)
{
lean_ctor_set(v___x_1874_, 0, v___x_1881_);
v___x_1883_ = v___x_1874_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v___x_1881_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
return v___x_1883_;
}
}
else
{
lean_del_object(v___x_1874_);
v___y_1823_ = v___y_1862_;
v___y_1824_ = v___y_1863_;
v___y_1825_ = v___x_1878_;
v___y_1826_ = v___x_1879_;
v___y_1827_ = v___x_1876_;
v___y_1828_ = v_fileName_1868_;
v___y_1829_ = v_a_1872_;
v_toCold_1830_ = v___y_1860_;
v___y_1831_ = v___y_1820_;
goto v___jp_1822_;
}
}
}
}
v___jp_1886_:
{
lean_object* v___x_1894_; 
v___x_1894_ = l_Lean_Syntax_getTailPos_x3f(v___y_1892_, v___y_1890_);
lean_dec(v___y_1892_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_inc(v___y_1893_);
v___y_1860_ = v___y_1887_;
v___y_1861_ = v___y_1889_;
v___y_1862_ = v___y_1890_;
v___y_1863_ = v___y_1891_;
v___y_1864_ = v___y_1887_;
v___y_1865_ = v___y_1888_;
v___y_1866_ = v___y_1893_;
v___y_1867_ = v___y_1893_;
goto v___jp_1859_;
}
else
{
lean_object* v_val_1895_; 
v_val_1895_ = lean_ctor_get(v___x_1894_, 0);
lean_inc(v_val_1895_);
lean_dec_ref_known(v___x_1894_, 1);
v___y_1860_ = v___y_1887_;
v___y_1861_ = v___y_1889_;
v___y_1862_ = v___y_1890_;
v___y_1863_ = v___y_1891_;
v___y_1864_ = v___y_1887_;
v___y_1865_ = v___y_1888_;
v___y_1866_ = v___y_1893_;
v___y_1867_ = v_val_1895_;
goto v___jp_1859_;
}
}
v___jp_1896_:
{
lean_object* v_toCold_1899_; lean_object* v_ref_1900_; uint8_t v_suppressElabErrors_1901_; lean_object* v___x_1902_; lean_object* v___f_1903_; lean_object* v_ref_1904_; lean_object* v___x_1905_; 
v_toCold_1899_ = lean_ctor_get(v___y_1819_, 0);
v_ref_1900_ = lean_ctor_get(v___y_1819_, 2);
v_suppressElabErrors_1901_ = lean_ctor_get_uint8(v___y_1819_, sizeof(void*)*3 + 2);
v___x_1902_ = lean_box(v_suppressElabErrors_1901_);
v___f_1903_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1903_, 0, v___x_1902_);
v_ref_1904_ = l_Lean_replaceRef(v_ref_1813_, v_ref_1900_);
v___x_1905_ = l_Lean_Syntax_getPos_x3f(v_ref_1904_, v___y_1897_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v___x_1906_; 
v___x_1906_ = lean_unsigned_to_nat(0u);
v___y_1887_ = v_toCold_1899_;
v___y_1888_ = v_suppressElabErrors_1901_;
v___y_1889_ = v___f_1903_;
v___y_1890_ = v___y_1897_;
v___y_1891_ = v___y_1898_;
v___y_1892_ = v_ref_1904_;
v___y_1893_ = v___x_1906_;
goto v___jp_1886_;
}
else
{
lean_object* v_val_1907_; 
v_val_1907_ = lean_ctor_get(v___x_1905_, 0);
lean_inc(v_val_1907_);
lean_dec_ref_known(v___x_1905_, 1);
v___y_1887_ = v_toCold_1899_;
v___y_1888_ = v_suppressElabErrors_1901_;
v___y_1889_ = v___f_1903_;
v___y_1890_ = v___y_1897_;
v___y_1891_ = v___y_1898_;
v___y_1892_ = v_ref_1904_;
v___y_1893_ = v_val_1907_;
goto v___jp_1886_;
}
}
v___jp_1909_:
{
uint8_t v___x_1911_; uint8_t v___x_1912_; 
v___x_1911_ = 1;
v___x_1912_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1815_, v___x_1911_);
if (v___x_1912_ == 0)
{
v___y_1897_ = v___y_1910_;
v___y_1898_ = v_severity_1815_;
goto v___jp_1896_;
}
else
{
lean_object* v___x_1913_; lean_object* v___x_1914_; uint8_t v___x_1915_; 
v___x_1913_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1819_);
v___x_1914_ = l_Lean_warningAsError;
v___x_1915_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__5(v___x_1913_, v___x_1914_);
lean_dec_ref(v___x_1913_);
if (v___x_1915_ == 0)
{
v___y_1897_ = v___y_1910_;
v___y_1898_ = v_severity_1815_;
goto v___jp_1896_;
}
else
{
v___y_1897_ = v___y_1910_;
v___y_1898_ = v___x_1908_;
goto v___jp_1896_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44_spec__46___boxed(lean_object* v_ref_1920_, lean_object* v_msgData_1921_, lean_object* v_severity_1922_, lean_object* v_isSilent_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_){
_start:
{
uint8_t v_severity_boxed_1929_; uint8_t v_isSilent_boxed_1930_; lean_object* v_res_1931_; 
v_severity_boxed_1929_ = lean_unbox(v_severity_1922_);
v_isSilent_boxed_1930_ = lean_unbox(v_isSilent_1923_);
v_res_1931_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44_spec__46(v_ref_1920_, v_msgData_1921_, v_severity_boxed_1929_, v_isSilent_boxed_1930_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
lean_dec(v___y_1927_);
lean_dec_ref(v___y_1926_);
lean_dec(v___y_1925_);
lean_dec_ref(v___y_1924_);
lean_dec(v_ref_1920_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44(lean_object* v_msgData_1932_, uint8_t v_severity_1933_, uint8_t v_isSilent_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v_ref_1940_; lean_object* v___x_1941_; 
v_ref_1940_ = lean_ctor_get(v___y_1937_, 2);
v___x_1941_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44_spec__46(v_ref_1940_, v_msgData_1932_, v_severity_1933_, v_isSilent_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
return v___x_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44___boxed(lean_object* v_msgData_1942_, lean_object* v_severity_1943_, lean_object* v_isSilent_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_){
_start:
{
uint8_t v_severity_boxed_1950_; uint8_t v_isSilent_boxed_1951_; lean_object* v_res_1952_; 
v_severity_boxed_1950_ = lean_unbox(v_severity_1943_);
v_isSilent_boxed_1951_ = lean_unbox(v_isSilent_1944_);
v_res_1952_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44(v_msgData_1942_, v_severity_boxed_1950_, v_isSilent_boxed_1951_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40(lean_object* v_msgData_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_){
_start:
{
uint8_t v___x_1959_; uint8_t v___x_1960_; lean_object* v___x_1961_; 
v___x_1959_ = 1;
v___x_1960_ = 0;
v___x_1961_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44(v_msgData_1953_, v___x_1959_, v___x_1960_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40___boxed(lean_object* v_msgData_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40(v_msgData_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34(lean_object* v_id_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v___x_1975_; lean_object* v_env_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v_a_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1998_; 
v___x_1975_ = lean_st_ref_get(v___y_1973_);
v_env_1976_ = lean_ctor_get(v___x_1975_, 0);
lean_inc_ref(v_env_1976_);
lean_dec(v___x_1975_);
v___x_1977_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1978_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__39___redArg(v___x_1977_, v___y_1972_);
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1981_ = v___x_1978_;
v_isShared_1982_ = v_isSharedCheck_1998_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_a_1979_);
lean_dec(v___x_1978_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1998_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
uint8_t v_isExporting_1988_; 
v_isExporting_1988_ = lean_ctor_get_uint8(v_env_1976_, sizeof(void*)*13);
lean_dec_ref(v_env_1976_);
if (v_isExporting_1988_ == 0)
{
lean_dec(v_a_1979_);
lean_dec(v_id_1969_);
goto v___jp_1983_;
}
else
{
uint8_t v___x_1989_; 
v___x_1989_ = l_Lean_isPrivateName(v_id_1969_);
if (v___x_1989_ == 0)
{
lean_dec(v_a_1979_);
lean_dec(v_id_1969_);
goto v___jp_1983_;
}
else
{
uint8_t v___x_1990_; 
v___x_1990_ = lean_unbox(v_a_1979_);
lean_dec(v_a_1979_);
if (v___x_1990_ == 0)
{
lean_dec(v_id_1969_);
goto v___jp_1983_;
}
else
{
lean_object* v___x_1991_; uint8_t v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; 
lean_del_object(v___x_1981_);
v___x_1991_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___closed__1);
v___x_1992_ = 0;
v___x_1993_ = l_Lean_MessageData_ofConstName(v_id_1969_, v___x_1992_);
v___x_1994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1991_);
lean_ctor_set(v___x_1994_, 1, v___x_1993_);
v___x_1995_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___closed__3);
v___x_1996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1994_);
lean_ctor_set(v___x_1996_, 1, v___x_1995_);
v___x_1997_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40(v___x_1996_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
return v___x_1997_;
}
}
}
v___jp_1983_:
{
lean_object* v___x_1984_; lean_object* v___x_1986_; 
v___x_1984_ = lean_box(0);
if (v_isShared_1982_ == 0)
{
lean_ctor_set(v___x_1981_, 0, v___x_1984_);
v___x_1986_ = v___x_1981_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v___x_1984_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34___boxed(lean_object* v_id_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_){
_start:
{
lean_object* v_res_2005_; 
v_res_2005_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34(v_id_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28(lean_object* v_id_2006_, uint8_t v_enableLog_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_){
_start:
{
lean_object* v___x_2013_; lean_object* v_toCold_2014_; lean_object* v_env_2015_; lean_object* v_currNamespace_2016_; lean_object* v_openDecls_2017_; lean_object* v___x_2018_; lean_object* v_res_2019_; lean_object* v___x_2020_; 
v___x_2013_ = lean_st_ref_get(v___y_2011_);
v_toCold_2014_ = lean_ctor_get(v___y_2010_, 0);
v_env_2015_ = lean_ctor_get(v___x_2013_, 0);
lean_inc_ref(v_env_2015_);
lean_dec(v___x_2013_);
v_currNamespace_2016_ = lean_ctor_get(v_toCold_2014_, 4);
v_openDecls_2017_ = lean_ctor_get(v_toCold_2014_, 5);
v___x_2018_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2010_);
lean_inc(v_openDecls_2017_);
lean_inc(v_currNamespace_2016_);
v_res_2019_ = l_Lean_ResolveName_resolveGlobalName(v_env_2015_, v___x_2018_, v_currNamespace_2016_, v_openDecls_2017_, v_id_2006_);
lean_dec_ref(v___x_2018_);
v___x_2020_ = lean_st_ref_get(v___y_2011_);
if (v_enableLog_2007_ == 0)
{
lean_object* v___x_2021_; 
lean_dec(v___x_2020_);
v___x_2021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2021_, 0, v_res_2019_);
return v___x_2021_;
}
else
{
lean_object* v_env_2022_; uint8_t v_isExporting_2023_; 
v_env_2022_ = lean_ctor_get(v___x_2020_, 0);
lean_inc_ref(v_env_2022_);
lean_dec(v___x_2020_);
v_isExporting_2023_ = lean_ctor_get_uint8(v_env_2022_, sizeof(void*)*13);
lean_dec_ref(v_env_2022_);
if (v_isExporting_2023_ == 0)
{
lean_object* v___x_2024_; 
v___x_2024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2024_, 0, v_res_2019_);
return v___x_2024_;
}
else
{
lean_object* v___x_2025_; 
v___x_2025_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__33(v_res_2019_);
if (lean_obj_tag(v___x_2025_) == 1)
{
lean_object* v_val_2026_; lean_object* v_fst_2027_; lean_object* v___x_2028_; 
v_val_2026_ = lean_ctor_get(v___x_2025_, 0);
lean_inc(v_val_2026_);
lean_dec_ref_known(v___x_2025_, 1);
v_fst_2027_ = lean_ctor_get(v_val_2026_, 0);
lean_inc(v_fst_2027_);
lean_dec(v_val_2026_);
v___x_2028_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34(v_fst_2027_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_);
if (lean_obj_tag(v___x_2028_) == 0)
{
lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2035_; 
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2035_ == 0)
{
lean_object* v_unused_2036_; 
v_unused_2036_ = lean_ctor_get(v___x_2028_, 0);
lean_dec(v_unused_2036_);
v___x_2030_ = v___x_2028_;
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
else
{
lean_dec(v___x_2028_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 0, v_res_2019_);
v___x_2033_ = v___x_2030_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_res_2019_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
else
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2044_; 
lean_dec(v_res_2019_);
v_a_2037_ = lean_ctor_get(v___x_2028_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2039_ = v___x_2028_;
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_2028_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2042_; 
if (v_isShared_2040_ == 0)
{
v___x_2042_ = v___x_2039_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_a_2037_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
else
{
lean_object* v___x_2045_; 
lean_dec(v___x_2025_);
v___x_2045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2045_, 0, v_res_2019_);
return v___x_2045_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28___boxed(lean_object* v_id_2046_, lean_object* v_enableLog_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_){
_start:
{
uint8_t v_enableLog_boxed_2053_; lean_object* v_res_2054_; 
v_enableLog_boxed_2053_ = lean_unbox(v_enableLog_2047_);
v_res_2054_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28(v_id_2046_, v_enableLog_boxed_2053_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22(lean_object* v_view_2055_, lean_object* v_findLocalDecl_x3f_2056_, lean_object* v_n_2057_, lean_object* v_projs_2058_, lean_object* v_auxDecl_x3f_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_){
_start:
{
lean_object* v___y_2066_; lean_object* v___y_2067_; lean_object* v_auxDecl_x3f_2073_; lean_object* v_imported_2104_; lean_object* v_ctx_2105_; lean_object* v_scopes_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
v_imported_2104_ = lean_ctor_get(v_view_2055_, 1);
v_ctx_2105_ = lean_ctor_get(v_view_2055_, 2);
v_scopes_2106_ = lean_ctor_get(v_view_2055_, 3);
lean_inc(v_scopes_2106_);
lean_inc(v_ctx_2105_);
lean_inc(v_imported_2104_);
lean_inc(v_n_2057_);
v___x_2107_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2107_, 0, v_n_2057_);
lean_ctor_set(v___x_2107_, 1, v_imported_2104_);
lean_ctor_set(v___x_2107_, 2, v_ctx_2105_);
lean_ctor_set(v___x_2107_, 3, v_scopes_2106_);
lean_inc_ref(v_findLocalDecl_x3f_2056_);
v___x_2108_ = lean_apply_1(v_findLocalDecl_x3f_2056_, v___x_2107_);
if (lean_obj_tag(v___x_2108_) == 1)
{
lean_object* v_val_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2124_; 
v_val_2109_ = lean_ctor_get(v___x_2108_, 0);
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2111_ = v___x_2108_;
v_isShared_2112_ = v_isSharedCheck_2124_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_val_2109_);
lean_dec(v___x_2108_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2124_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
uint8_t v___x_2113_; 
v___x_2113_ = l_Lean_LocalDecl_isAuxDecl(v_val_2109_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2117_; 
lean_dec(v_auxDecl_x3f_2059_);
lean_dec(v_n_2057_);
lean_dec_ref(v_findLocalDecl_x3f_2056_);
lean_dec_ref(v_view_2055_);
v___x_2114_ = l_Lean_LocalDecl_toExpr(v_val_2109_);
v___x_2115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
lean_ctor_set(v___x_2115_, 1, v_projs_2058_);
if (v_isShared_2112_ == 0)
{
lean_ctor_set(v___x_2111_, 0, v___x_2115_);
v___x_2117_ = v___x_2111_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___x_2115_);
v___x_2117_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
lean_object* v___x_2118_; 
v___x_2118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
return v___x_2118_;
}
}
else
{
if (lean_obj_tag(v_auxDecl_x3f_2059_) == 0)
{
lean_object* v___x_2120_; lean_object* v___x_2122_; 
lean_inc(v_projs_2058_);
v___x_2120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2120_, 0, v_val_2109_);
lean_ctor_set(v___x_2120_, 1, v_projs_2058_);
if (v_isShared_2112_ == 0)
{
lean_ctor_set(v___x_2111_, 0, v___x_2120_);
v___x_2122_ = v___x_2111_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v___x_2120_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
v_auxDecl_x3f_2073_ = v___x_2122_;
goto v___jp_2072_;
}
}
else
{
lean_del_object(v___x_2111_);
lean_dec(v_val_2109_);
v_auxDecl_x3f_2073_ = v_auxDecl_x3f_2059_;
goto v___jp_2072_;
}
}
}
}
else
{
lean_dec(v___x_2108_);
v_auxDecl_x3f_2073_ = v_auxDecl_x3f_2059_;
goto v___jp_2072_;
}
v___jp_2065_:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2068_ = l_Lean_LocalDecl_toExpr(v___y_2067_);
v___x_2069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2068_);
lean_ctor_set(v___x_2069_, 1, v___y_2066_);
v___x_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2069_);
v___x_2071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2070_);
return v___x_2071_;
}
v___jp_2072_:
{
if (lean_obj_tag(v_n_2057_) == 1)
{
lean_object* v_pre_2074_; lean_object* v_str_2075_; lean_object* v___x_2076_; 
v_pre_2074_ = lean_ctor_get(v_n_2057_, 0);
lean_inc(v_pre_2074_);
v_str_2075_ = lean_ctor_get(v_n_2057_, 1);
lean_inc_ref(v_str_2075_);
lean_dec_ref_known(v_n_2057_, 2);
v___x_2076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2076_, 0, v_str_2075_);
lean_ctor_set(v___x_2076_, 1, v_projs_2058_);
v_n_2057_ = v_pre_2074_;
v_projs_2058_ = v___x_2076_;
v_auxDecl_x3f_2059_ = v_auxDecl_x3f_2073_;
goto _start;
}
else
{
lean_dec(v_projs_2058_);
lean_dec(v_n_2057_);
lean_dec_ref(v_findLocalDecl_x3f_2056_);
if (lean_obj_tag(v_auxDecl_x3f_2073_) == 1)
{
lean_object* v_val_2078_; lean_object* v_fst_2079_; lean_object* v_snd_2080_; uint8_t v___x_2081_; 
v_val_2078_ = lean_ctor_get(v_auxDecl_x3f_2073_, 0);
lean_inc(v_val_2078_);
lean_dec_ref_known(v_auxDecl_x3f_2073_, 1);
v_fst_2079_ = lean_ctor_get(v_val_2078_, 0);
lean_inc(v_fst_2079_);
v_snd_2080_ = lean_ctor_get(v_val_2078_, 1);
lean_inc(v_snd_2080_);
lean_dec(v_val_2078_);
v___x_2081_ = l_List_isEmpty___redArg(v_snd_2080_);
if (v___x_2081_ == 0)
{
lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2082_ = l_Lean_MacroScopesView_review(v_view_2055_);
v___x_2083_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28(v___x_2082_, v___x_2081_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_);
if (lean_obj_tag(v___x_2083_) == 0)
{
lean_object* v_a_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2093_; 
v_a_2084_ = lean_ctor_get(v___x_2083_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_2083_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2086_ = v___x_2083_;
v_isShared_2087_ = v_isSharedCheck_2093_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_a_2084_);
lean_dec(v___x_2083_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2093_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
uint8_t v___x_2088_; 
v___x_2088_ = l_List_any___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__29(v_snd_2080_, v_a_2084_);
lean_dec(v_a_2084_);
if (v___x_2088_ == 0)
{
lean_del_object(v___x_2086_);
v___y_2066_ = v_snd_2080_;
v___y_2067_ = v_fst_2079_;
goto v___jp_2065_;
}
else
{
lean_object* v___x_2089_; lean_object* v___x_2091_; 
lean_dec(v_snd_2080_);
lean_dec(v_fst_2079_);
v___x_2089_ = lean_box(0);
if (v_isShared_2087_ == 0)
{
lean_ctor_set(v___x_2086_, 0, v___x_2089_);
v___x_2091_ = v___x_2086_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v___x_2089_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
}
else
{
lean_object* v_a_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2101_; 
lean_dec(v_snd_2080_);
lean_dec(v_fst_2079_);
v_a_2094_ = lean_ctor_get(v___x_2083_, 0);
v_isSharedCheck_2101_ = !lean_is_exclusive(v___x_2083_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2096_ = v___x_2083_;
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_a_2094_);
lean_dec(v___x_2083_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2099_; 
if (v_isShared_2097_ == 0)
{
v___x_2099_ = v___x_2096_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_a_2094_);
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
else
{
lean_dec_ref(v_view_2055_);
v___y_2066_ = v_snd_2080_;
v___y_2067_ = v_fst_2079_;
goto v___jp_2065_;
}
}
else
{
lean_object* v___x_2102_; lean_object* v___x_2103_; 
lean_dec(v_auxDecl_x3f_2073_);
lean_dec_ref(v_view_2055_);
v___x_2102_ = lean_box(0);
v___x_2103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2102_);
return v___x_2103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22___boxed(lean_object* v_view_2125_, lean_object* v_findLocalDecl_x3f_2126_, lean_object* v_n_2127_, lean_object* v_projs_2128_, lean_object* v_auxDecl_x3f_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_){
_start:
{
lean_object* v_res_2135_; 
v_res_2135_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22(v_view_2125_, v_findLocalDecl_x3f_2126_, v_n_2127_, v_projs_2128_, v_auxDecl_x3f_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__25___redArg(lean_object* v_localDecl_x3f_2136_, lean_object* v_givenName_2137_, lean_object* v_as_2138_, lean_object* v_i_2139_){
_start:
{
lean_object* v_zero_2140_; uint8_t v_isZero_2141_; 
v_zero_2140_ = lean_unsigned_to_nat(0u);
v_isZero_2141_ = lean_nat_dec_eq(v_i_2139_, v_zero_2140_);
if (v_isZero_2141_ == 1)
{
lean_object* v___x_2142_; 
lean_dec(v_i_2139_);
v___x_2142_ = lean_box(0);
return v___x_2142_;
}
else
{
lean_object* v_one_2143_; lean_object* v_n_2144_; lean_object* v___x_2145_; 
v_one_2143_ = lean_unsigned_to_nat(1u);
v_n_2144_ = lean_nat_sub(v_i_2139_, v_one_2143_);
lean_dec(v_i_2139_);
v___x_2145_ = lean_array_fget_borrowed(v_as_2138_, v_n_2144_);
if (lean_obj_tag(v___x_2145_) == 0)
{
v_i_2139_ = v_n_2144_;
goto _start;
}
else
{
lean_object* v_val_2147_; uint8_t v___x_2148_; 
v_val_2147_ = lean_ctor_get(v___x_2145_, 0);
v___x_2148_ = l_Lean_LocalDecl_isAuxDecl(v_val_2147_);
if (v___x_2148_ == 0)
{
if (lean_obj_tag(v_localDecl_x3f_2136_) == 0)
{
v_i_2139_ = v_n_2144_;
goto _start;
}
else
{
lean_dec(v_n_2144_);
lean_inc_ref(v_localDecl_x3f_2136_);
return v_localDecl_x3f_2136_;
}
}
else
{
lean_object* v___x_2150_; uint8_t v___x_2151_; 
v___x_2150_ = l_Lean_LocalDecl_userName(v_val_2147_);
v___x_2151_ = lean_name_eq(v___x_2150_, v_givenName_2137_);
lean_dec(v___x_2150_);
if (v___x_2151_ == 0)
{
v_i_2139_ = v_n_2144_;
goto _start;
}
else
{
lean_dec(v_n_2144_);
lean_inc_ref(v___x_2145_);
return v___x_2145_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__25___redArg___boxed(lean_object* v_localDecl_x3f_2153_, lean_object* v_givenName_2154_, lean_object* v_as_2155_, lean_object* v_i_2156_){
_start:
{
lean_object* v_res_2157_; 
v_res_2157_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__25___redArg(v_localDecl_x3f_2153_, v_givenName_2154_, v_as_2155_, v_i_2156_);
lean_dec_ref(v_as_2155_);
lean_dec(v_givenName_2154_);
lean_dec(v_localDecl_x3f_2153_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26_spec__30___redArg(lean_object* v_localDecl_x3f_2158_, lean_object* v_givenName_2159_, lean_object* v_as_2160_, lean_object* v_i_2161_){
_start:
{
lean_object* v_zero_2162_; uint8_t v_isZero_2163_; 
v_zero_2162_ = lean_unsigned_to_nat(0u);
v_isZero_2163_ = lean_nat_dec_eq(v_i_2161_, v_zero_2162_);
if (v_isZero_2163_ == 1)
{
lean_object* v___x_2164_; 
lean_dec(v_i_2161_);
v___x_2164_ = lean_box(0);
return v___x_2164_;
}
else
{
lean_object* v_one_2165_; lean_object* v_n_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
v_one_2165_ = lean_unsigned_to_nat(1u);
v_n_2166_ = lean_nat_sub(v_i_2161_, v_one_2165_);
lean_dec(v_i_2161_);
v___x_2167_ = lean_array_fget_borrowed(v_as_2160_, v_n_2166_);
v___x_2168_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26(v_localDecl_x3f_2158_, v_givenName_2159_, v___x_2167_);
if (lean_obj_tag(v___x_2168_) == 0)
{
v_i_2161_ = v_n_2166_;
goto _start;
}
else
{
lean_dec(v_n_2166_);
return v___x_2168_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26(lean_object* v_localDecl_x3f_2170_, lean_object* v_givenName_2171_, lean_object* v_x_2172_){
_start:
{
if (lean_obj_tag(v_x_2172_) == 0)
{
lean_object* v_cs_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v_cs_2173_ = lean_ctor_get(v_x_2172_, 0);
v___x_2174_ = lean_array_get_size(v_cs_2173_);
v___x_2175_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26_spec__30___redArg(v_localDecl_x3f_2170_, v_givenName_2171_, v_cs_2173_, v___x_2174_);
return v___x_2175_;
}
else
{
lean_object* v_vs_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v_vs_2176_ = lean_ctor_get(v_x_2172_, 0);
v___x_2177_ = lean_array_get_size(v_vs_2176_);
v___x_2178_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__25___redArg(v_localDecl_x3f_2170_, v_givenName_2171_, v_vs_2176_, v___x_2177_);
return v___x_2178_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26___boxed(lean_object* v_localDecl_x3f_2179_, lean_object* v_givenName_2180_, lean_object* v_x_2181_){
_start:
{
lean_object* v_res_2182_; 
v_res_2182_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26(v_localDecl_x3f_2179_, v_givenName_2180_, v_x_2181_);
lean_dec_ref(v_x_2181_);
lean_dec(v_givenName_2180_);
lean_dec(v_localDecl_x3f_2179_);
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26_spec__30___redArg___boxed(lean_object* v_localDecl_x3f_2183_, lean_object* v_givenName_2184_, lean_object* v_as_2185_, lean_object* v_i_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26_spec__30___redArg(v_localDecl_x3f_2183_, v_givenName_2184_, v_as_2185_, v_i_2186_);
lean_dec_ref(v_as_2185_);
lean_dec(v_givenName_2184_);
lean_dec(v_localDecl_x3f_2183_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21(lean_object* v_localDecl_x3f_2188_, lean_object* v_givenName_2189_, lean_object* v_t_2190_){
_start:
{
lean_object* v_root_2191_; lean_object* v_tail_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v_root_2191_ = lean_ctor_get(v_t_2190_, 0);
v_tail_2192_ = lean_ctor_get(v_t_2190_, 1);
v___x_2193_ = lean_array_get_size(v_tail_2192_);
v___x_2194_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__25___redArg(v_localDecl_x3f_2188_, v_givenName_2189_, v_tail_2192_, v___x_2193_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v___x_2195_; 
v___x_2195_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26(v_localDecl_x3f_2188_, v_givenName_2189_, v_root_2191_);
return v___x_2195_;
}
else
{
return v___x_2194_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21___boxed(lean_object* v_localDecl_x3f_2196_, lean_object* v_givenName_2197_, lean_object* v_t_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21(v_localDecl_x3f_2196_, v_givenName_2197_, v_t_2198_);
lean_dec_ref(v_t_2198_);
lean_dec(v_givenName_2197_);
lean_dec(v_localDecl_x3f_2196_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__19___redArg(lean_object* v_t_2200_, lean_object* v_k_2201_){
_start:
{
if (lean_obj_tag(v_t_2200_) == 0)
{
lean_object* v_k_2202_; lean_object* v_v_2203_; lean_object* v_l_2204_; lean_object* v_r_2205_; uint8_t v___x_2206_; 
v_k_2202_ = lean_ctor_get(v_t_2200_, 1);
v_v_2203_ = lean_ctor_get(v_t_2200_, 2);
v_l_2204_ = lean_ctor_get(v_t_2200_, 3);
v_r_2205_ = lean_ctor_get(v_t_2200_, 4);
v___x_2206_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2201_, v_k_2202_);
switch(v___x_2206_)
{
case 0:
{
v_t_2200_ = v_l_2204_;
goto _start;
}
case 1:
{
lean_object* v___x_2208_; 
lean_inc(v_v_2203_);
v___x_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2208_, 0, v_v_2203_);
return v___x_2208_;
}
default: 
{
v_t_2200_ = v_r_2205_;
goto _start;
}
}
}
else
{
lean_object* v___x_2210_; 
v___x_2210_ = lean_box(0);
return v___x_2210_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__19___redArg___boxed(lean_object* v_t_2211_, lean_object* v_k_2212_){
_start:
{
lean_object* v_res_2213_; 
v_res_2213_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__19___redArg(v_t_2211_, v_k_2212_);
lean_dec(v_k_2212_);
lean_dec(v_t_2211_);
return v_res_2213_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22___redArg___lam__0(lean_object* v_localDecl_2214_, lean_object* v_givenName_2215_){
_start:
{
lean_object* v___x_2216_; uint8_t v___x_2217_; 
v___x_2216_ = l_Lean_LocalDecl_userName(v_localDecl_2214_);
v___x_2217_ = lean_name_eq(v___x_2216_, v_givenName_2215_);
lean_dec(v___x_2216_);
if (v___x_2217_ == 0)
{
lean_object* v___x_2218_; 
lean_dec_ref(v_localDecl_2214_);
v___x_2218_ = lean_box(0);
return v___x_2218_;
}
else
{
lean_object* v___x_2219_; 
v___x_2219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2219_, 0, v_localDecl_2214_);
return v___x_2219_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22___redArg___lam__0___boxed(lean_object* v_localDecl_2220_, lean_object* v_givenName_2221_){
_start:
{
lean_object* v_res_2222_; 
v_res_2222_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22___redArg___lam__0(v_localDecl_2220_, v_givenName_2221_);
lean_dec(v_givenName_2221_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22___redArg(lean_object* v_givenName_2223_, lean_object* v_auxDeclToFullName_2224_, lean_object* v___x_2225_, lean_object* v_givenNameView_2226_, lean_object* v_as_2227_, lean_object* v_i_2228_){
_start:
{
lean_object* v_zero_2229_; uint8_t v_isZero_2230_; 
v_zero_2229_ = lean_unsigned_to_nat(0u);
v_isZero_2230_ = lean_nat_dec_eq(v_i_2228_, v_zero_2229_);
if (v_isZero_2230_ == 1)
{
lean_object* v___x_2231_; 
lean_dec(v_i_2228_);
lean_dec_ref(v_givenNameView_2226_);
lean_dec(v___x_2225_);
v___x_2231_ = lean_box(0);
return v___x_2231_;
}
else
{
lean_object* v_one_2232_; lean_object* v_n_2233_; lean_object* v___y_2235_; lean_object* v___x_2237_; 
v_one_2232_ = lean_unsigned_to_nat(1u);
v_n_2233_ = lean_nat_sub(v_i_2228_, v_one_2232_);
lean_dec(v_i_2228_);
v___x_2237_ = lean_array_fget_borrowed(v_as_2227_, v_n_2233_);
if (lean_obj_tag(v___x_2237_) == 0)
{
v_i_2228_ = v_n_2233_;
goto _start;
}
else
{
lean_object* v_val_2239_; uint8_t v___x_2240_; 
v_val_2239_ = lean_ctor_get(v___x_2237_, 0);
v___x_2240_ = l_Lean_LocalDecl_isAuxDecl(v_val_2239_);
if (v___x_2240_ == 0)
{
lean_object* v___x_2241_; 
lean_inc(v_val_2239_);
v___x_2241_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22___redArg___lam__0(v_val_2239_, v_givenName_2223_);
v___y_2235_ = v___x_2241_;
goto v___jp_2234_;
}
else
{
lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2242_ = l_Lean_LocalDecl_fvarId(v_val_2239_);
v___x_2243_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__19___redArg(v_auxDeclToFullName_2224_, v___x_2242_);
lean_dec(v___x_2242_);
if (lean_obj_tag(v___x_2243_) == 1)
{
lean_object* v_val_2244_; lean_object* v_fullDeclView_2245_; lean_object* v_name_2246_; lean_object* v_imported_2247_; lean_object* v_ctx_2248_; lean_object* v_scopes_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2269_; 
v_val_2244_ = lean_ctor_get(v___x_2243_, 0);
lean_inc(v_val_2244_);
lean_dec_ref_known(v___x_2243_, 1);
v_fullDeclView_2245_ = l_Lean_extractMacroScopes(v_val_2244_);
v_name_2246_ = lean_ctor_get(v_fullDeclView_2245_, 0);
v_imported_2247_ = lean_ctor_get(v_fullDeclView_2245_, 1);
v_ctx_2248_ = lean_ctor_get(v_fullDeclView_2245_, 2);
v_scopes_2249_ = lean_ctor_get(v_fullDeclView_2245_, 3);
v_isSharedCheck_2269_ = !lean_is_exclusive(v_fullDeclView_2245_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2251_ = v_fullDeclView_2245_;
v_isShared_2252_ = v_isSharedCheck_2269_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_scopes_2249_);
lean_inc(v_ctx_2248_);
lean_inc(v_imported_2247_);
lean_inc(v_name_2246_);
lean_dec(v_fullDeclView_2245_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2269_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___y_2254_; lean_object* v___x_2267_; 
lean_inc(v_name_2246_);
v___x_2267_ = l_Lean_privateToUserName_x3f(v_name_2246_);
if (lean_obj_tag(v___x_2267_) == 0)
{
v___y_2254_ = v_name_2246_;
goto v___jp_2253_;
}
else
{
lean_object* v_val_2268_; 
lean_dec(v_name_2246_);
v_val_2268_ = lean_ctor_get(v___x_2267_, 0);
lean_inc(v_val_2268_);
lean_dec_ref_known(v___x_2267_, 1);
v___y_2254_ = v_val_2268_;
goto v___jp_2253_;
}
v___jp_2253_:
{
lean_object* v_fullDeclView_2256_; 
if (v_isShared_2252_ == 0)
{
lean_ctor_set(v___x_2251_, 0, v___y_2254_);
v_fullDeclView_2256_ = v___x_2251_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v___y_2254_);
lean_ctor_set(v_reuseFailAlloc_2266_, 1, v_imported_2247_);
lean_ctor_set(v_reuseFailAlloc_2266_, 2, v_ctx_2248_);
lean_ctor_set(v_reuseFailAlloc_2266_, 3, v_scopes_2249_);
v_fullDeclView_2256_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
lean_object* v_fullDeclName_2257_; uint8_t v___x_2258_; 
lean_inc_ref(v_fullDeclView_2256_);
v_fullDeclName_2257_ = l_Lean_MacroScopesView_review(v_fullDeclView_2256_);
v___x_2258_ = l_Lean_Name_isPrefixOf(v___x_2225_, v_fullDeclName_2257_);
if (v___x_2258_ == 0)
{
lean_object* v___x_2259_; 
lean_dec_ref(v_fullDeclView_2256_);
lean_inc(v___x_2225_);
lean_inc_ref(v_givenNameView_2226_);
lean_inc(v_val_2239_);
v___x_2259_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_val_2239_, v_givenNameView_2226_, v_fullDeclName_2257_, v___x_2225_);
lean_dec(v_fullDeclName_2257_);
v___y_2235_ = v___x_2259_;
goto v___jp_2234_;
}
else
{
lean_object* v___x_2260_; lean_object* v_localDeclNameView_2261_; uint8_t v___x_2262_; 
lean_dec(v_fullDeclName_2257_);
v___x_2260_ = l_Lean_LocalDecl_userName(v_val_2239_);
v_localDeclNameView_2261_ = l_Lean_extractMacroScopes(v___x_2260_);
v___x_2262_ = l_Lean_MacroScopesView_isSuffixOf(v_localDeclNameView_2261_, v_givenNameView_2226_);
lean_dec_ref(v_localDeclNameView_2261_);
if (v___x_2262_ == 0)
{
lean_dec_ref(v_fullDeclView_2256_);
v_i_2228_ = v_n_2233_;
goto _start;
}
else
{
uint8_t v___x_2264_; 
v___x_2264_ = l_Lean_MacroScopesView_isSuffixOf(v_givenNameView_2226_, v_fullDeclView_2256_);
lean_dec_ref(v_fullDeclView_2256_);
if (v___x_2264_ == 0)
{
v_i_2228_ = v_n_2233_;
goto _start;
}
else
{
lean_dec(v_n_2233_);
lean_dec_ref(v_givenNameView_2226_);
lean_dec(v___x_2225_);
lean_inc_ref(v___x_2237_);
return v___x_2237_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2270_; 
lean_dec(v___x_2243_);
lean_inc(v_val_2239_);
v___x_2270_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22___redArg___lam__0(v_val_2239_, v_givenName_2223_);
v___y_2235_ = v___x_2270_;
goto v___jp_2234_;
}
}
}
v___jp_2234_:
{
if (lean_obj_tag(v___y_2235_) == 0)
{
v_i_2228_ = v_n_2233_;
goto _start;
}
else
{
lean_dec(v_n_2233_);
lean_dec_ref(v_givenNameView_2226_);
lean_dec(v___x_2225_);
return v___y_2235_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22___redArg___boxed(lean_object* v_givenName_2271_, lean_object* v_auxDeclToFullName_2272_, lean_object* v___x_2273_, lean_object* v_givenNameView_2274_, lean_object* v_as_2275_, lean_object* v_i_2276_){
_start:
{
lean_object* v_res_2277_; 
v_res_2277_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22___redArg(v_givenName_2271_, v_auxDeclToFullName_2272_, v___x_2273_, v_givenNameView_2274_, v_as_2275_, v_i_2276_);
lean_dec_ref(v_as_2275_);
lean_dec(v_auxDeclToFullName_2272_);
lean_dec(v_givenName_2271_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23_spec__26___redArg(lean_object* v_givenName_2278_, lean_object* v_auxDeclToFullName_2279_, lean_object* v___x_2280_, lean_object* v_givenNameView_2281_, lean_object* v_as_2282_, lean_object* v_i_2283_){
_start:
{
lean_object* v_zero_2284_; uint8_t v_isZero_2285_; 
v_zero_2284_ = lean_unsigned_to_nat(0u);
v_isZero_2285_ = lean_nat_dec_eq(v_i_2283_, v_zero_2284_);
if (v_isZero_2285_ == 1)
{
lean_object* v___x_2286_; 
lean_dec(v_i_2283_);
lean_dec_ref(v_givenNameView_2281_);
lean_dec(v___x_2280_);
v___x_2286_ = lean_box(0);
return v___x_2286_;
}
else
{
lean_object* v_one_2287_; lean_object* v_n_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
v_one_2287_ = lean_unsigned_to_nat(1u);
v_n_2288_ = lean_nat_sub(v_i_2283_, v_one_2287_);
lean_dec(v_i_2283_);
v___x_2289_ = lean_array_fget_borrowed(v_as_2282_, v_n_2288_);
lean_inc_ref(v_givenNameView_2281_);
lean_inc(v___x_2280_);
v___x_2290_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23(v_givenName_2278_, v_auxDeclToFullName_2279_, v___x_2280_, v_givenNameView_2281_, v___x_2289_);
if (lean_obj_tag(v___x_2290_) == 0)
{
v_i_2283_ = v_n_2288_;
goto _start;
}
else
{
lean_dec(v_n_2288_);
lean_dec_ref(v_givenNameView_2281_);
lean_dec(v___x_2280_);
return v___x_2290_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23(lean_object* v_givenName_2292_, lean_object* v_auxDeclToFullName_2293_, lean_object* v___x_2294_, lean_object* v_givenNameView_2295_, lean_object* v_x_2296_){
_start:
{
if (lean_obj_tag(v_x_2296_) == 0)
{
lean_object* v_cs_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; 
v_cs_2297_ = lean_ctor_get(v_x_2296_, 0);
v___x_2298_ = lean_array_get_size(v_cs_2297_);
v___x_2299_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23_spec__26___redArg(v_givenName_2292_, v_auxDeclToFullName_2293_, v___x_2294_, v_givenNameView_2295_, v_cs_2297_, v___x_2298_);
return v___x_2299_;
}
else
{
lean_object* v_vs_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
v_vs_2300_ = lean_ctor_get(v_x_2296_, 0);
v___x_2301_ = lean_array_get_size(v_vs_2300_);
v___x_2302_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22___redArg(v_givenName_2292_, v_auxDeclToFullName_2293_, v___x_2294_, v_givenNameView_2295_, v_vs_2300_, v___x_2301_);
return v___x_2302_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23___boxed(lean_object* v_givenName_2303_, lean_object* v_auxDeclToFullName_2304_, lean_object* v___x_2305_, lean_object* v_givenNameView_2306_, lean_object* v_x_2307_){
_start:
{
lean_object* v_res_2308_; 
v_res_2308_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23(v_givenName_2303_, v_auxDeclToFullName_2304_, v___x_2305_, v_givenNameView_2306_, v_x_2307_);
lean_dec_ref(v_x_2307_);
lean_dec(v_auxDeclToFullName_2304_);
lean_dec(v_givenName_2303_);
return v_res_2308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23_spec__26___redArg___boxed(lean_object* v_givenName_2309_, lean_object* v_auxDeclToFullName_2310_, lean_object* v___x_2311_, lean_object* v_givenNameView_2312_, lean_object* v_as_2313_, lean_object* v_i_2314_){
_start:
{
lean_object* v_res_2315_; 
v_res_2315_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23_spec__26___redArg(v_givenName_2309_, v_auxDeclToFullName_2310_, v___x_2311_, v_givenNameView_2312_, v_as_2313_, v_i_2314_);
lean_dec_ref(v_as_2313_);
lean_dec(v_auxDeclToFullName_2310_);
lean_dec(v_givenName_2309_);
return v_res_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20(lean_object* v_givenName_2316_, lean_object* v_auxDeclToFullName_2317_, lean_object* v___x_2318_, lean_object* v_givenNameView_2319_, lean_object* v_t_2320_){
_start:
{
lean_object* v_root_2321_; lean_object* v_tail_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
v_root_2321_ = lean_ctor_get(v_t_2320_, 0);
v_tail_2322_ = lean_ctor_get(v_t_2320_, 1);
v___x_2323_ = lean_array_get_size(v_tail_2322_);
lean_inc_ref(v_givenNameView_2319_);
lean_inc(v___x_2318_);
v___x_2324_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22___redArg(v_givenName_2316_, v_auxDeclToFullName_2317_, v___x_2318_, v_givenNameView_2319_, v_tail_2322_, v___x_2323_);
if (lean_obj_tag(v___x_2324_) == 0)
{
lean_object* v___x_2325_; 
v___x_2325_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23(v_givenName_2316_, v_auxDeclToFullName_2317_, v___x_2318_, v_givenNameView_2319_, v_root_2321_);
return v___x_2325_;
}
else
{
lean_dec_ref(v_givenNameView_2319_);
lean_dec(v___x_2318_);
return v___x_2324_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20___boxed(lean_object* v_givenName_2326_, lean_object* v_auxDeclToFullName_2327_, lean_object* v___x_2328_, lean_object* v_givenNameView_2329_, lean_object* v_t_2330_){
_start:
{
lean_object* v_res_2331_; 
v_res_2331_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20(v_givenName_2326_, v_auxDeclToFullName_2327_, v___x_2328_, v_givenNameView_2329_, v_t_2330_);
lean_dec_ref(v_t_2330_);
lean_dec(v_auxDeclToFullName_2327_);
lean_dec(v_givenName_2326_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13___lam__0(lean_object* v_auxDeclToFullName_2332_, lean_object* v_currNamespace_2333_, lean_object* v_decls_2334_, lean_object* v_givenNameView_2335_){
_start:
{
lean_object* v_givenName_2336_; lean_object* v_localDecl_x3f_2337_; 
lean_inc_ref(v_givenNameView_2335_);
v_givenName_2336_ = l_Lean_MacroScopesView_review(v_givenNameView_2335_);
v_localDecl_x3f_2337_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20(v_givenName_2336_, v_auxDeclToFullName_2332_, v_currNamespace_2333_, v_givenNameView_2335_, v_decls_2334_);
if (lean_obj_tag(v_localDecl_x3f_2337_) == 0)
{
lean_object* v___x_2338_; 
v___x_2338_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21(v_localDecl_x3f_2337_, v_givenName_2336_, v_decls_2334_);
lean_dec(v_givenName_2336_);
return v___x_2338_;
}
else
{
lean_dec(v_givenName_2336_);
return v_localDecl_x3f_2337_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13___lam__0___boxed(lean_object* v_auxDeclToFullName_2339_, lean_object* v_currNamespace_2340_, lean_object* v_decls_2341_, lean_object* v_givenNameView_2342_){
_start:
{
lean_object* v_res_2343_; 
v_res_2343_ = l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13___lam__0(v_auxDeclToFullName_2339_, v_currNamespace_2340_, v_decls_2341_, v_givenNameView_2342_);
lean_dec_ref(v_decls_2341_);
lean_dec(v_auxDeclToFullName_2339_);
return v_res_2343_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13(lean_object* v_n_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_){
_start:
{
lean_object* v_lctx_2350_; lean_object* v_toCold_2351_; lean_object* v_decls_2352_; lean_object* v_auxDeclToFullName_2353_; lean_object* v_currNamespace_2354_; lean_object* v_view_2355_; lean_object* v_name_2356_; lean_object* v_findLocalDecl_x3f_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; 
v_lctx_2350_ = lean_ctor_get(v___y_2345_, 2);
v_toCold_2351_ = lean_ctor_get(v___y_2347_, 0);
v_decls_2352_ = lean_ctor_get(v_lctx_2350_, 1);
v_auxDeclToFullName_2353_ = lean_ctor_get(v_lctx_2350_, 2);
v_currNamespace_2354_ = lean_ctor_get(v_toCold_2351_, 4);
v_view_2355_ = l_Lean_extractMacroScopes(v_n_2344_);
v_name_2356_ = lean_ctor_get(v_view_2355_, 0);
lean_inc(v_name_2356_);
lean_inc_ref(v_decls_2352_);
lean_inc(v_currNamespace_2354_);
lean_inc(v_auxDeclToFullName_2353_);
v_findLocalDecl_x3f_2357_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13___lam__0___boxed), 4, 3);
lean_closure_set(v_findLocalDecl_x3f_2357_, 0, v_auxDeclToFullName_2353_);
lean_closure_set(v_findLocalDecl_x3f_2357_, 1, v_currNamespace_2354_);
lean_closure_set(v_findLocalDecl_x3f_2357_, 2, v_decls_2352_);
v___x_2358_ = lean_box(0);
v___x_2359_ = lean_box(0);
v___x_2360_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22(v_view_2355_, v_findLocalDecl_x3f_2357_, v_name_2356_, v___x_2358_, v___x_2359_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_);
return v___x_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13___boxed(lean_object* v_n_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
lean_object* v_res_2367_; 
v_res_2367_ = l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13(v_n_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
return v_res_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6___lam__0(uint8_t v___x_2368_, lean_object* v_n_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_){
_start:
{
lean_object* v___x_2375_; 
v___x_2375_ = l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13(v_n_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_);
if (lean_obj_tag(v___x_2375_) == 0)
{
lean_object* v_a_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2389_; 
v_a_2376_ = lean_ctor_get(v___x_2375_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2375_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2378_ = v___x_2375_;
v_isShared_2379_ = v_isSharedCheck_2389_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_a_2376_);
lean_dec(v___x_2375_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2389_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
if (lean_obj_tag(v_a_2376_) == 0)
{
uint8_t v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2383_; 
v___x_2380_ = 1;
v___x_2381_ = lean_box(v___x_2380_);
if (v_isShared_2379_ == 0)
{
lean_ctor_set(v___x_2378_, 0, v___x_2381_);
v___x_2383_ = v___x_2378_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v___x_2381_);
v___x_2383_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
return v___x_2383_;
}
}
else
{
lean_object* v___x_2385_; lean_object* v___x_2387_; 
lean_dec_ref_known(v_a_2376_, 1);
v___x_2385_ = lean_box(v___x_2368_);
if (v_isShared_2379_ == 0)
{
lean_ctor_set(v___x_2378_, 0, v___x_2385_);
v___x_2387_ = v___x_2378_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v___x_2385_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
}
else
{
lean_object* v_a_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2397_; 
v_a_2390_ = lean_ctor_get(v___x_2375_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2375_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2392_ = v___x_2375_;
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_a_2390_);
lean_dec(v___x_2375_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2395_; 
if (v_isShared_2393_ == 0)
{
v___x_2395_ = v___x_2392_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v_a_2390_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6___lam__0___boxed(lean_object* v___x_2398_, lean_object* v_n_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_){
_start:
{
uint8_t v___x_47729__boxed_2405_; lean_object* v_res_2406_; 
v___x_47729__boxed_2405_ = lean_unbox(v___x_2398_);
v_res_2406_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6___lam__0(v___x_47729__boxed_2405_, v_n_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6(lean_object* v_n_u2080_2410_, uint8_t v_fullNames_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_){
_start:
{
uint8_t v___x_2417_; lean_object* v___f_2418_; lean_object* v___x_2419_; 
v___x_2417_ = 0;
v___f_2418_ = ((lean_object*)(l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6___closed__0));
v___x_2419_ = l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14(v_n_u2080_2410_, v_fullNames_2411_, v___x_2417_, v___f_2418_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
return v___x_2419_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6___boxed(lean_object* v_n_u2080_2420_, lean_object* v_fullNames_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_){
_start:
{
uint8_t v_fullNames_boxed_2427_; lean_object* v_res_2428_; 
v_fullNames_boxed_2427_ = lean_unbox(v_fullNames_2421_);
v_res_2428_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6(v_n_u2080_2420_, v_fullNames_boxed_2427_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2422_);
return v_res_2428_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__1_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2430_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__0_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2431_ = l_Lean_stringToMessageData(v___x_2430_);
return v___x_2431_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__4_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2435_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__3_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2436_ = l_Lean_MessageData_ofFormat(v___x_2435_);
return v___x_2436_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2438_; lean_object* v___x_2439_; 
v___x_2438_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__5_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2439_ = l_Lean_stringToMessageData(v___x_2438_);
return v___x_2439_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2441_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2442_ = l_Lean_stringToMessageData(v___x_2441_);
return v___x_2442_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__10_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2444_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2445_ = l_Lean_stringToMessageData(v___x_2444_);
return v___x_2445_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__13_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2449_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__12_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2450_ = l_Lean_MessageData_ofFormat(v___x_2449_);
return v___x_2450_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__14_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2451_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__13_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__13_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__13_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2452_ = l_Lean_MessageData_hint_x27(v___x_2451_);
return v___x_2452_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2454_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__15_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2455_ = l_Lean_stringToMessageData(v___x_2454_);
return v___x_2455_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__19_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2459_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__18_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2460_ = l_Lean_MessageData_ofFormat(v___x_2459_);
return v___x_2460_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__24_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2467_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__23_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2468_ = l_Lean_MessageData_ofFormat(v___x_2467_);
return v___x_2468_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__25_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; 
v___x_2469_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__24_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__24_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__24_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2469_);
return v___x_2470_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; 
v___x_2471_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_2472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2471_);
return v___x_2472_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__27_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2473_ = lean_box(1);
v___x_2474_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_2475_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2476_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2475_);
lean_ctor_set(v___x_2476_, 1, v___x_2474_);
lean_ctor_set(v___x_2476_, 2, v___x_2473_);
return v___x_2476_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
v___x_2479_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2480_ = lean_unsigned_to_nat(0u);
v___x_2481_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2481_, 0, v___x_2480_);
lean_ctor_set(v___x_2481_, 1, v___x_2480_);
lean_ctor_set(v___x_2481_, 2, v___x_2480_);
lean_ctor_set(v___x_2481_, 3, v___x_2480_);
lean_ctor_set(v___x_2481_, 4, v___x_2479_);
lean_ctor_set(v___x_2481_, 5, v___x_2479_);
lean_ctor_set(v___x_2481_, 6, v___x_2479_);
lean_ctor_set(v___x_2481_, 7, v___x_2479_);
lean_ctor_set(v___x_2481_, 8, v___x_2479_);
lean_ctor_set(v___x_2481_, 9, v___x_2479_);
lean_ctor_set(v___x_2481_, 10, v___x_2479_);
return v___x_2481_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2482_; 
v___x_2482_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__4_spec__10___redArg();
return v___x_2482_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; 
v___x_2483_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2484_, 0, v___x_2483_);
lean_ctor_set(v___x_2484_, 1, v___x_2483_);
return v___x_2484_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; 
v___x_2485_ = lean_unsigned_to_nat(0u);
v___x_2486_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2487_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2487_, 0, v___x_2486_);
lean_ctor_set(v___x_2487_, 1, v___x_2486_);
lean_ctor_set(v___x_2487_, 2, v___x_2485_);
return v___x_2487_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2488_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2489_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2490_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2491_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2492_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2492_, 0, v___x_2491_);
lean_ctor_set(v___x_2492_, 1, v___x_2490_);
lean_ctor_set(v___x_2492_, 2, v___x_2489_);
lean_ctor_set(v___x_2492_, 3, v___x_2490_);
lean_ctor_set(v___x_2492_, 4, v___x_2490_);
lean_ctor_set(v___x_2492_, 5, v___x_2490_);
lean_ctor_set(v___x_2492_, 6, v___x_2490_);
lean_ctor_set(v___x_2492_, 7, v___x_2488_);
return v___x_2492_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2493_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2494_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2493_);
lean_ctor_set(v___x_2494_, 1, v___x_2493_);
lean_ctor_set(v___x_2494_, 2, v___x_2493_);
lean_ctor_set(v___x_2494_, 3, v___x_2493_);
lean_ctor_set(v___x_2494_, 4, v___x_2493_);
return v___x_2494_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__37_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; 
v___x_2498_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__36_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2499_ = l_Lean_MessageData_ofFormat(v___x_2498_);
return v___x_2499_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__39_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2501_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__38_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2502_ = l_Lean_stringToMessageData(v___x_2501_);
return v___x_2502_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2504_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__40_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2505_ = l_Lean_stringToMessageData(v___x_2504_);
return v___x_2505_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2507_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2508_ = l_Lean_stringToMessageData(v___x_2507_);
return v___x_2508_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; 
v___x_2510_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2511_ = l_Lean_stringToMessageData(v___x_2510_);
return v___x_2511_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__47_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2513_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2514_ = l_Lean_stringToMessageData(v___x_2513_);
return v___x_2514_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__49_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; 
v___x_2516_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__48_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2517_ = l_Lean_stringToMessageData(v___x_2516_);
return v___x_2517_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__51_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2519_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__50_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2520_ = l_Lean_stringToMessageData(v___x_2519_);
return v___x_2520_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__53_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2522_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__52_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2523_ = l_Lean_stringToMessageData(v___x_2522_);
return v___x_2523_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__55_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2525_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__54_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2526_ = l_Lean_stringToMessageData(v___x_2525_);
return v___x_2526_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__57_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2528_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__56_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2529_ = l_Lean_stringToMessageData(v___x_2528_);
return v___x_2529_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__59_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2531_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__58_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2532_ = l_Lean_stringToMessageData(v___x_2531_);
return v___x_2532_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__61_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2534_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__60_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2535_ = l_Lean_stringToMessageData(v___x_2534_);
return v___x_2535_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__63_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; 
v___x_2537_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__62_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2538_ = l_Lean_stringToMessageData(v___x_2537_);
return v___x_2538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(lean_object* v___x_2539_, lean_object* v___x_2540_, lean_object* v___f_2541_, uint8_t v___x_2542_, lean_object* v___x_2543_, lean_object* v___x_2544_, lean_object* v_a_2545_, lean_object* v_declName_2546_, lean_object* v_stx_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_){
_start:
{
lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v___y_2560_; lean_object* v___y_2561_; lean_object* v___y_2562_; lean_object* v___y_2585_; lean_object* v___y_2586_; lean_object* v___y_2587_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v___y_2590_; lean_object* v___y_2602_; lean_object* v___y_2603_; lean_object* v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2619_; lean_object* v___y_2620_; lean_object* v___y_2621_; lean_object* v___y_2622_; lean_object* v___y_2623_; lean_object* v___y_2624_; lean_object* v___y_2636_; lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v___y_2639_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v_hint_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2667_; lean_object* v___y_2668_; lean_object* v___y_2669_; lean_object* v___y_2670_; lean_object* v___y_2671_; lean_object* v___y_2672_; lean_object* v___y_2673_; lean_object* v___y_2674_; lean_object* v___x_2676_; uint8_t v___x_2677_; 
v___x_2676_ = l_Lean_Name_mkStr2(v___x_2539_, v___x_2540_);
lean_inc(v_stx_2547_);
v___x_2677_ = l_Lean_Syntax_isOfKind(v_stx_2547_, v___x_2676_);
lean_dec(v___x_2676_);
if (v___x_2677_ == 0)
{
lean_object* v___x_2678_; lean_object* v___x_2679_; 
lean_dec(v_stx_2547_);
lean_dec(v_declName_2546_);
lean_dec_ref(v___x_2544_);
lean_dec(v___x_2543_);
lean_dec_ref(v___f_2541_);
v___x_2678_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2679_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0___redArg(v___x_2678_, v___y_2548_, v___y_2549_);
return v___x_2679_;
}
else
{
lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___y_2685_; lean_object* v___y_2686_; lean_object* v___y_2687_; lean_object* v___y_2688_; lean_object* v___y_2689_; lean_object* v___y_2690_; lean_object* v_val_2691_; lean_object* v___y_2716_; lean_object* v___y_2717_; lean_object* v___y_2718_; lean_object* v___y_2719_; lean_object* v___y_2720_; lean_object* v___y_2721_; lean_object* v___y_2722_; lean_object* v___y_2723_; lean_object* v___y_2728_; lean_object* v___y_2729_; lean_object* v___y_2730_; uint8_t v___y_2731_; lean_object* v___y_2732_; lean_object* v___y_2733_; lean_object* v___y_2734_; lean_object* v___y_2735_; lean_object* v___y_2736_; lean_object* v___y_2737_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v___y_2787_; uint8_t v___y_2788_; lean_object* v___y_2789_; lean_object* v___y_2790_; lean_object* v___y_2791_; lean_object* v_msg_2792_; lean_object* v___y_2793_; lean_object* v___y_2794_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; lean_object* v___y_2809_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2946_; lean_object* v___y_2947_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v_a_2952_; lean_object* v___y_2970_; lean_object* v___y_2971_; lean_object* v___y_2972_; lean_object* v_since_x3f_2973_; lean_object* v___y_2974_; lean_object* v___y_2975_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v_typeChanged_x3f_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_3008_; lean_object* v_text_x3f_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v_id_x3f_3022_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___x_3034_; uint8_t v___x_3035_; 
v___x_2680_ = lean_unsigned_to_nat(0u);
v___x_2681_ = lean_unsigned_to_nat(1u);
v___x_3034_ = l_Lean_Syntax_getArg(v_stx_2547_, v___x_2681_);
v___x_3035_ = l_Lean_Syntax_isNone(v___x_3034_);
if (v___x_3035_ == 0)
{
uint8_t v___x_3036_; 
lean_inc(v___x_3034_);
v___x_3036_ = l_Lean_Syntax_matchesNull(v___x_3034_, v___x_2681_);
if (v___x_3036_ == 0)
{
lean_object* v___x_3037_; lean_object* v___x_3038_; 
lean_dec(v___x_3034_);
lean_dec(v_stx_2547_);
lean_dec(v_declName_2546_);
lean_dec_ref(v___x_2544_);
lean_dec(v___x_2543_);
lean_dec_ref(v___f_2541_);
v___x_3037_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_3038_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0___redArg(v___x_3037_, v___y_2548_, v___y_2549_);
return v___x_3038_;
}
else
{
lean_object* v___x_3039_; lean_object* v___x_3040_; 
v___x_3039_ = l_Lean_Syntax_getArg(v___x_3034_, v___x_2680_);
lean_dec(v___x_3034_);
v___x_3040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3039_);
v_id_x3f_3022_ = v___x_3040_;
v___y_3023_ = v___y_2548_;
v___y_3024_ = v___y_2549_;
goto v___jp_3021_;
}
}
else
{
lean_object* v___x_3041_; 
lean_dec(v___x_3034_);
v___x_3041_ = lean_box(0);
v_id_x3f_3022_ = v___x_3041_;
v___y_3023_ = v___y_2548_;
v___y_3024_ = v___y_2549_;
goto v___jp_3021_;
}
v___jp_2682_:
{
lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; uint8_t v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v___x_2692_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__19_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__19_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__19_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2693_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__21_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2694_ = lean_box(0);
v___x_2695_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__25_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__25_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__25_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2696_, 0, v___f_2541_);
v___x_2697_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2697_, 0, v___x_2693_);
lean_ctor_set(v___x_2697_, 1, v___x_2694_);
lean_ctor_set(v___x_2697_, 2, v___x_2694_);
lean_ctor_set(v___x_2697_, 3, v___x_2694_);
lean_ctor_set(v___x_2697_, 4, v___x_2695_);
lean_ctor_set(v___x_2697_, 5, v___x_2696_);
lean_inc(v_val_2691_);
v___x_2698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2698_, 0, v_val_2691_);
lean_ctor_set(v___x_2698_, 1, v_val_2691_);
v___x_2699_ = l_Lean_Syntax_ofRange(v___x_2698_, v___x_2677_);
v___x_2700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2699_);
v___x_2701_ = 4;
v___x_2702_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2702_, 0, v___x_2697_);
lean_ctor_set(v___x_2702_, 1, v___x_2700_);
lean_ctor_set(v___x_2702_, 2, v___x_2694_);
lean_ctor_set_uint8(v___x_2702_, sizeof(void*)*3, v___x_2701_);
v___x_2703_ = lean_mk_empty_array_with_capacity(v___x_2681_);
v___x_2704_ = lean_array_push(v___x_2703_, v___x_2702_);
v___x_2705_ = l_Lean_MessageData_hint(v___x_2692_, v___x_2704_, v___x_2694_, v___x_2694_, v___x_2542_, v___y_2685_, v___y_2683_);
lean_dec_ref(v___x_2704_);
if (lean_obj_tag(v___x_2705_) == 0)
{
lean_object* v_a_2706_; 
v_a_2706_ = lean_ctor_get(v___x_2705_, 0);
lean_inc(v_a_2706_);
lean_dec_ref_known(v___x_2705_, 1);
v___y_2636_ = v___y_2684_;
v___y_2637_ = v___y_2686_;
v___y_2638_ = v___y_2688_;
v___y_2639_ = v___y_2687_;
v___y_2640_ = v___y_2689_;
v___y_2641_ = v___y_2690_;
v_hint_2642_ = v_a_2706_;
v___y_2643_ = v___y_2685_;
v___y_2644_ = v___y_2683_;
goto v___jp_2635_;
}
else
{
lean_object* v_a_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2714_; 
lean_dec(v___y_2690_);
lean_dec_ref(v___y_2689_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
lean_dec(v___y_2686_);
lean_dec(v___y_2684_);
lean_dec(v_stx_2547_);
v_a_2707_ = lean_ctor_get(v___x_2705_, 0);
v_isSharedCheck_2714_ = !lean_is_exclusive(v___x_2705_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2709_ = v___x_2705_;
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_a_2707_);
lean_dec(v___x_2705_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v___x_2712_; 
if (v_isShared_2710_ == 0)
{
v___x_2712_ = v___x_2709_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v_a_2707_);
v___x_2712_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
return v___x_2712_;
}
}
}
}
v___jp_2715_:
{
if (lean_obj_tag(v___y_2718_) == 0)
{
lean_dec_ref(v___f_2541_);
v___y_2667_ = v___y_2716_;
v___y_2668_ = v___y_2718_;
v___y_2669_ = v___y_2717_;
v___y_2670_ = v___y_2719_;
v___y_2671_ = v___y_2721_;
v___y_2672_ = v___y_2720_;
v___y_2673_ = v___y_2722_;
v___y_2674_ = v___y_2723_;
goto v___jp_2666_;
}
else
{
lean_object* v_val_2724_; lean_object* v___x_2725_; 
v_val_2724_ = lean_ctor_get(v___y_2718_, 0);
v___x_2725_ = l_Lean_Syntax_getTailPos_x3f(v_val_2724_, v___x_2677_);
if (lean_obj_tag(v___x_2725_) == 1)
{
lean_object* v_val_2726_; 
v_val_2726_ = lean_ctor_get(v___x_2725_, 0);
lean_inc(v_val_2726_);
lean_dec_ref_known(v___x_2725_, 1);
v___y_2683_ = v___y_2716_;
v___y_2684_ = v___y_2718_;
v___y_2685_ = v___y_2717_;
v___y_2686_ = v___y_2719_;
v___y_2687_ = v___y_2721_;
v___y_2688_ = v___y_2720_;
v___y_2689_ = v___y_2722_;
v___y_2690_ = v___y_2723_;
v_val_2691_ = v_val_2726_;
goto v___jp_2682_;
}
else
{
lean_dec(v___x_2725_);
lean_dec_ref(v___f_2541_);
v___y_2667_ = v___y_2716_;
v___y_2668_ = v___y_2718_;
v___y_2669_ = v___y_2717_;
v___y_2670_ = v___y_2719_;
v___y_2671_ = v___y_2721_;
v___y_2672_ = v___y_2720_;
v___y_2673_ = v___y_2722_;
v___y_2674_ = v___y_2723_;
goto v___jp_2666_;
}
}
}
v___jp_2727_:
{
lean_object* v___x_2738_; 
lean_inc_ref(v___y_2732_);
v___x_2738_ = l_Lean_Environment_findConstVal_x3f(v___y_2732_, v_declName_2546_, v___x_2542_);
if (lean_obj_tag(v___x_2738_) == 1)
{
lean_object* v_val_2739_; lean_object* v___x_2740_; 
v_val_2739_ = lean_ctor_get(v___x_2738_, 0);
lean_inc(v_val_2739_);
lean_dec_ref_known(v___x_2738_, 1);
v___x_2740_ = l_Lean_Environment_findConstVal_x3f(v___y_2732_, v___y_2729_, v___x_2542_);
if (lean_obj_tag(v___x_2740_) == 1)
{
lean_object* v_val_2741_; uint8_t v___x_2742_; uint8_t v___x_2743_; uint8_t v___x_2744_; lean_object* v___x_2745_; uint64_t v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; 
v_val_2741_ = lean_ctor_get(v___x_2740_, 0);
lean_inc(v_val_2741_);
lean_dec_ref_known(v___x_2740_, 1);
v___x_2742_ = 1;
v___x_2743_ = 0;
v___x_2744_ = 2;
v___x_2745_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_2745_, 0, v___x_2542_);
lean_ctor_set_uint8(v___x_2745_, 1, v___x_2542_);
lean_ctor_set_uint8(v___x_2745_, 2, v___x_2542_);
lean_ctor_set_uint8(v___x_2745_, 3, v___x_2542_);
lean_ctor_set_uint8(v___x_2745_, 4, v___x_2542_);
lean_ctor_set_uint8(v___x_2745_, 5, v___y_2731_);
lean_ctor_set_uint8(v___x_2745_, 6, v___y_2731_);
lean_ctor_set_uint8(v___x_2745_, 7, v___x_2542_);
lean_ctor_set_uint8(v___x_2745_, 8, v___y_2731_);
lean_ctor_set_uint8(v___x_2745_, 9, v___x_2742_);
lean_ctor_set_uint8(v___x_2745_, 10, v___x_2743_);
lean_ctor_set_uint8(v___x_2745_, 11, v___y_2731_);
lean_ctor_set_uint8(v___x_2745_, 12, v___y_2731_);
lean_ctor_set_uint8(v___x_2745_, 13, v___y_2731_);
lean_ctor_set_uint8(v___x_2745_, 14, v___x_2744_);
lean_ctor_set_uint8(v___x_2745_, 15, v___y_2731_);
lean_ctor_set_uint8(v___x_2745_, 16, v___y_2731_);
lean_ctor_set_uint8(v___x_2745_, 17, v___y_2731_);
lean_ctor_set_uint8(v___x_2745_, 18, v___y_2731_);
lean_ctor_set_uint8(v___x_2745_, 19, v___x_2542_);
v___x_2746_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2745_);
v___x_2747_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2747_, 0, v___x_2745_);
lean_ctor_set_uint64(v___x_2747_, sizeof(void*)*1, v___x_2746_);
v___x_2748_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_2749_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__27_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__27_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__27_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2750_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__28_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2751_ = lean_box(0);
lean_inc(v___x_2543_);
v___x_2752_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2752_, 0, v___x_2747_);
lean_ctor_set(v___x_2752_, 1, v___x_2543_);
lean_ctor_set(v___x_2752_, 2, v___x_2749_);
lean_ctor_set(v___x_2752_, 3, v___x_2750_);
lean_ctor_set(v___x_2752_, 4, v___x_2751_);
lean_ctor_set(v___x_2752_, 5, v___x_2680_);
lean_ctor_set(v___x_2752_, 6, v___x_2751_);
lean_ctor_set_uint8(v___x_2752_, sizeof(void*)*7, v___x_2542_);
lean_ctor_set_uint8(v___x_2752_, sizeof(void*)*7 + 1, v___x_2542_);
lean_ctor_set_uint8(v___x_2752_, sizeof(void*)*7 + 2, v___x_2542_);
lean_ctor_set_uint8(v___x_2752_, sizeof(void*)*7 + 3, v___x_2677_);
v___x_2753_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2754_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2755_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2756_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2756_, 0, v___x_2753_);
lean_ctor_set(v___x_2756_, 1, v___x_2754_);
lean_ctor_set(v___x_2756_, 2, v___x_2543_);
lean_ctor_set(v___x_2756_, 3, v___x_2748_);
lean_ctor_set(v___x_2756_, 4, v___x_2755_);
v___x_2757_ = lean_st_mk_ref(v___x_2756_);
v___x_2758_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq(v_val_2739_, v_val_2741_, v___x_2752_, v___x_2757_, v___y_2736_, v___y_2737_);
lean_dec_ref_known(v___x_2752_, 7);
if (lean_obj_tag(v___x_2758_) == 0)
{
lean_object* v_a_2759_; lean_object* v___x_2760_; uint8_t v___x_2761_; 
v_a_2759_ = lean_ctor_get(v___x_2758_, 0);
lean_inc(v_a_2759_);
lean_dec_ref_known(v___x_2758_, 1);
v___x_2760_ = lean_st_ref_get(v___x_2757_);
lean_dec(v___x_2757_);
lean_dec(v___x_2760_);
v___x_2761_ = lean_unbox(v_a_2759_);
lean_dec(v_a_2759_);
if (v___x_2761_ == 0)
{
if (lean_obj_tag(v___y_2734_) == 0)
{
if (lean_obj_tag(v___y_2730_) == 0)
{
v___y_2716_ = v___y_2737_;
v___y_2717_ = v___y_2736_;
v___y_2718_ = v___y_2728_;
v___y_2719_ = v___y_2730_;
v___y_2720_ = v___y_2733_;
v___y_2721_ = v_val_2739_;
v___y_2722_ = v_val_2741_;
v___y_2723_ = v___y_2735_;
goto v___jp_2715_;
}
else
{
lean_object* v_val_2762_; lean_object* v___x_2763_; 
v_val_2762_ = lean_ctor_get(v___y_2730_, 0);
v___x_2763_ = l_Lean_Syntax_getTailPos_x3f(v_val_2762_, v___x_2677_);
if (lean_obj_tag(v___x_2763_) == 0)
{
v___y_2716_ = v___y_2737_;
v___y_2717_ = v___y_2736_;
v___y_2718_ = v___y_2728_;
v___y_2719_ = v___y_2730_;
v___y_2720_ = v___y_2733_;
v___y_2721_ = v_val_2739_;
v___y_2722_ = v_val_2741_;
v___y_2723_ = v___y_2735_;
goto v___jp_2715_;
}
else
{
lean_object* v_val_2764_; 
v_val_2764_ = lean_ctor_get(v___x_2763_, 0);
lean_inc(v_val_2764_);
lean_dec_ref_known(v___x_2763_, 1);
v___y_2683_ = v___y_2737_;
v___y_2684_ = v___y_2728_;
v___y_2685_ = v___y_2736_;
v___y_2686_ = v___y_2730_;
v___y_2687_ = v_val_2739_;
v___y_2688_ = v___y_2733_;
v___y_2689_ = v_val_2741_;
v___y_2690_ = v___y_2735_;
v_val_2691_ = v_val_2764_;
goto v___jp_2682_;
}
}
}
else
{
lean_dec_ref_known(v___y_2734_, 1);
lean_dec(v_val_2741_);
lean_dec(v_val_2739_);
lean_dec_ref(v___f_2541_);
v___y_2619_ = v___y_2728_;
v___y_2620_ = v___y_2730_;
v___y_2621_ = v___y_2733_;
v___y_2622_ = v___y_2735_;
v___y_2623_ = v___y_2736_;
v___y_2624_ = v___y_2737_;
goto v___jp_2618_;
}
}
else
{
lean_dec(v_val_2741_);
lean_dec(v_val_2739_);
lean_dec_ref(v___f_2541_);
if (lean_obj_tag(v___y_2734_) == 0)
{
v___y_2619_ = v___y_2728_;
v___y_2620_ = v___y_2730_;
v___y_2621_ = v___y_2733_;
v___y_2622_ = v___y_2735_;
v___y_2623_ = v___y_2736_;
v___y_2624_ = v___y_2737_;
goto v___jp_2618_;
}
else
{
lean_object* v___x_2765_; lean_object* v___x_2766_; 
lean_dec_ref_known(v___y_2734_, 1);
v___x_2765_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__37_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__37_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__37_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2766_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1(v___x_2765_, v___y_2736_, v___y_2737_);
if (lean_obj_tag(v___x_2766_) == 0)
{
lean_dec_ref_known(v___x_2766_, 1);
v___y_2619_ = v___y_2728_;
v___y_2620_ = v___y_2730_;
v___y_2621_ = v___y_2733_;
v___y_2622_ = v___y_2735_;
v___y_2623_ = v___y_2736_;
v___y_2624_ = v___y_2737_;
goto v___jp_2618_;
}
else
{
lean_object* v_a_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2774_; 
lean_dec(v___y_2735_);
lean_dec(v___y_2733_);
lean_dec(v___y_2730_);
lean_dec(v___y_2728_);
lean_dec(v_stx_2547_);
v_a_2767_ = lean_ctor_get(v___x_2766_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2766_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2769_ = v___x_2766_;
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_a_2767_);
lean_dec(v___x_2766_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2772_; 
if (v_isShared_2770_ == 0)
{
v___x_2772_ = v___x_2769_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_a_2767_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
return v___x_2772_;
}
}
}
}
}
}
else
{
lean_object* v_a_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2782_; 
lean_dec(v___x_2757_);
lean_dec(v_val_2741_);
lean_dec(v_val_2739_);
lean_dec(v___y_2735_);
lean_dec(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec(v___y_2730_);
lean_dec(v___y_2728_);
lean_dec(v_stx_2547_);
lean_dec_ref(v___f_2541_);
v_a_2775_ = lean_ctor_get(v___x_2758_, 0);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2758_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2777_ = v___x_2758_;
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_a_2775_);
lean_dec(v___x_2758_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2780_; 
if (v_isShared_2778_ == 0)
{
v___x_2780_ = v___x_2777_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_a_2775_);
v___x_2780_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
return v___x_2780_;
}
}
}
}
else
{
lean_dec(v___x_2740_);
lean_dec(v_val_2739_);
lean_dec(v___y_2734_);
lean_dec(v___x_2543_);
lean_dec_ref(v___f_2541_);
v___y_2619_ = v___y_2728_;
v___y_2620_ = v___y_2730_;
v___y_2621_ = v___y_2733_;
v___y_2622_ = v___y_2735_;
v___y_2623_ = v___y_2736_;
v___y_2624_ = v___y_2737_;
goto v___jp_2618_;
}
}
else
{
lean_dec(v___x_2738_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2729_);
lean_dec(v___x_2543_);
lean_dec_ref(v___f_2541_);
v___y_2619_ = v___y_2728_;
v___y_2620_ = v___y_2730_;
v___y_2621_ = v___y_2733_;
v___y_2622_ = v___y_2735_;
v___y_2623_ = v___y_2736_;
v___y_2624_ = v___y_2737_;
goto v___jp_2618_;
}
}
v___jp_2783_:
{
lean_object* v___x_2795_; 
v___x_2795_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1(v_msg_2792_, v___y_2793_, v___y_2794_);
if (lean_obj_tag(v___x_2795_) == 0)
{
lean_dec_ref_known(v___x_2795_, 1);
v___y_2728_ = v___y_2784_;
v___y_2729_ = v___y_2785_;
v___y_2730_ = v___y_2786_;
v___y_2731_ = v___y_2788_;
v___y_2732_ = v___y_2787_;
v___y_2733_ = v___y_2789_;
v___y_2734_ = v___y_2790_;
v___y_2735_ = v___y_2791_;
v___y_2736_ = v___y_2793_;
v___y_2737_ = v___y_2794_;
goto v___jp_2727_;
}
else
{
lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2803_; 
lean_dec(v___y_2791_);
lean_dec(v___y_2790_);
lean_dec(v___y_2789_);
lean_dec_ref(v___y_2787_);
lean_dec(v___y_2786_);
lean_dec(v___y_2785_);
lean_dec(v___y_2784_);
lean_dec(v_stx_2547_);
lean_dec(v_declName_2546_);
lean_dec(v___x_2543_);
lean_dec_ref(v___f_2541_);
v_a_2796_ = lean_ctor_get(v___x_2795_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2795_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2798_ = v___x_2795_;
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v___x_2795_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2801_; 
if (v_isShared_2799_ == 0)
{
v___x_2801_ = v___x_2798_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_a_2796_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
}
v___jp_2804_:
{
if (lean_obj_tag(v___y_2809_) == 1)
{
lean_object* v_val_2812_; lean_object* v___x_2813_; 
v_val_2812_ = lean_ctor_get(v___y_2809_, 0);
lean_inc(v_val_2812_);
v___x_2813_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2(v_val_2812_, v___x_2542_, v___y_2810_, v___y_2811_);
if (lean_obj_tag(v___x_2813_) == 0)
{
lean_object* v___x_2814_; lean_object* v_a_2815_; lean_object* v___x_2816_; uint8_t v___x_2817_; 
lean_dec_ref_known(v___x_2813_, 1);
v___x_2814_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__3(v___y_2810_, v___y_2811_);
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_a_2815_);
lean_dec_ref(v___x_2814_);
v___x_2816_ = l_Lean_Linter_linter_deprecated;
v___x_2817_ = l_Lean_Linter_getLinterValue(v___x_2816_, v_a_2815_);
lean_dec(v_a_2815_);
if (v___x_2817_ == 0)
{
lean_dec(v___y_2808_);
lean_dec(v_declName_2546_);
lean_dec_ref(v___x_2544_);
lean_dec(v___x_2543_);
lean_dec_ref(v___f_2541_);
v___y_2619_ = v___y_2805_;
v___y_2620_ = v___y_2806_;
v___y_2621_ = v___y_2807_;
v___y_2622_ = v___y_2809_;
v___y_2623_ = v___y_2810_;
v___y_2624_ = v___y_2811_;
goto v___jp_2618_;
}
else
{
lean_object* v___x_2818_; lean_object* v_env_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; uint8_t v___x_2822_; 
lean_inc(v_val_2812_);
v___x_2818_ = lean_st_ref_get(v___y_2811_);
v_env_2819_ = lean_ctor_get(v___x_2818_, 0);
lean_inc_ref(v_env_2819_);
lean_dec(v___x_2818_);
v___x_2820_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2810_);
v___x_2821_ = l_Lean_Linter_linter_deprecated_deprecatedTarget;
v___x_2822_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__5(v___x_2820_, v___x_2821_);
lean_dec_ref(v___x_2820_);
if (v___x_2822_ == 0)
{
lean_dec_ref(v___x_2544_);
v___y_2728_ = v___y_2805_;
v___y_2729_ = v_val_2812_;
v___y_2730_ = v___y_2806_;
v___y_2731_ = v___x_2817_;
v___y_2732_ = v_env_2819_;
v___y_2733_ = v___y_2807_;
v___y_2734_ = v___y_2808_;
v___y_2735_ = v___y_2809_;
v___y_2736_ = v___y_2810_;
v___y_2737_ = v___y_2811_;
goto v___jp_2727_;
}
else
{
lean_object* v___x_2823_; 
lean_inc(v_val_2812_);
lean_inc_ref(v_env_2819_);
v___x_2823_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v___x_2544_, v_a_2545_, v___x_2542_, v_env_2819_, v_val_2812_);
if (lean_obj_tag(v___x_2823_) == 1)
{
lean_object* v_val_2824_; lean_object* v_name_2825_; lean_object* v_newName_x3f_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; 
v_val_2824_ = lean_ctor_get(v___x_2823_, 0);
lean_inc(v_val_2824_);
lean_dec_ref_known(v___x_2823_, 1);
v_name_2825_ = lean_ctor_get(v___x_2821_, 0);
v_newName_x3f_2826_ = lean_ctor_get(v_val_2824_, 0);
lean_inc(v_newName_x3f_2826_);
lean_dec(v_val_2824_);
v___x_2827_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__39_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__39_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__39_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
lean_inc(v_name_2825_);
v___x_2828_ = l_Lean_MessageData_ofName(v_name_2825_);
v___x_2829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2827_);
lean_ctor_set(v___x_2829_, 1, v___x_2828_);
v___x_2830_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2831_, 0, v___x_2829_);
lean_ctor_set(v___x_2831_, 1, v___x_2830_);
v___x_2832_ = l_Lean_MessageData_note(v___x_2831_);
if (lean_obj_tag(v_newName_x3f_2826_) == 0)
{
lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; 
v___x_2833_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
lean_inc(v_val_2812_);
v___x_2834_ = l_Lean_MessageData_ofConstName(v_val_2812_, v___x_2677_);
v___x_2835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2835_, 0, v___x_2833_);
lean_ctor_set(v___x_2835_, 1, v___x_2834_);
v___x_2836_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2837_, 0, v___x_2835_);
lean_ctor_set(v___x_2837_, 1, v___x_2836_);
lean_inc(v_declName_2546_);
v___x_2838_ = l_Lean_MessageData_ofConstName(v_declName_2546_, v___x_2677_);
v___x_2839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2839_, 0, v___x_2837_);
lean_ctor_set(v___x_2839_, 1, v___x_2838_);
v___x_2840_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__47_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__47_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__47_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2839_);
lean_ctor_set(v___x_2841_, 1, v___x_2840_);
v___x_2842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2842_, 0, v___x_2841_);
lean_ctor_set(v___x_2842_, 1, v___x_2832_);
v___x_2843_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1(v___x_2842_, v___y_2810_, v___y_2811_);
if (lean_obj_tag(v___x_2843_) == 0)
{
lean_dec_ref_known(v___x_2843_, 1);
v___y_2728_ = v___y_2805_;
v___y_2729_ = v_val_2812_;
v___y_2730_ = v___y_2806_;
v___y_2731_ = v___x_2817_;
v___y_2732_ = v_env_2819_;
v___y_2733_ = v___y_2807_;
v___y_2734_ = v___y_2808_;
v___y_2735_ = v___y_2809_;
v___y_2736_ = v___y_2810_;
v___y_2737_ = v___y_2811_;
goto v___jp_2727_;
}
else
{
lean_object* v_a_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2851_; 
lean_dec_ref(v_env_2819_);
lean_dec(v_val_2812_);
lean_dec_ref_known(v___y_2809_, 1);
lean_dec(v___y_2808_);
lean_dec(v___y_2807_);
lean_dec(v___y_2806_);
lean_dec(v___y_2805_);
lean_dec(v_stx_2547_);
lean_dec(v_declName_2546_);
lean_dec(v___x_2543_);
lean_dec_ref(v___f_2541_);
v_a_2844_ = lean_ctor_get(v___x_2843_, 0);
v_isSharedCheck_2851_ = !lean_is_exclusive(v___x_2843_);
if (v_isSharedCheck_2851_ == 0)
{
v___x_2846_ = v___x_2843_;
v_isShared_2847_ = v_isSharedCheck_2851_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_a_2844_);
lean_dec(v___x_2843_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2851_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
lean_object* v___x_2849_; 
if (v_isShared_2847_ == 0)
{
v___x_2849_ = v___x_2846_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v_a_2844_);
v___x_2849_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
return v___x_2849_;
}
}
}
}
else
{
lean_object* v_val_2852_; uint8_t v___x_2853_; 
v_val_2852_ = lean_ctor_get(v_newName_x3f_2826_, 0);
lean_inc(v_val_2852_);
lean_dec_ref_known(v_newName_x3f_2826_, 1);
v___x_2853_ = lean_name_eq(v_val_2852_, v_val_2812_);
if (v___x_2853_ == 0)
{
lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; 
v___x_2854_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
lean_inc(v_val_2812_);
v___x_2855_ = l_Lean_MessageData_ofConstName(v_val_2812_, v___x_2677_);
v___x_2856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2854_);
lean_ctor_set(v___x_2856_, 1, v___x_2855_);
v___x_2857_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__49_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__49_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__49_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2858_, 0, v___x_2856_);
lean_ctor_set(v___x_2858_, 1, v___x_2857_);
lean_inc(v_val_2852_);
v___x_2859_ = l_Lean_MessageData_ofConstName(v_val_2852_, v___x_2677_);
lean_inc_ref_n(v___x_2859_, 2);
v___x_2860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2860_, 0, v___x_2858_);
lean_ctor_set(v___x_2860_, 1, v___x_2859_);
v___x_2861_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__51_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__51_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__51_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2862_, 0, v___x_2860_);
lean_ctor_set(v___x_2862_, 1, v___x_2861_);
lean_inc(v_declName_2546_);
v___x_2863_ = l_Lean_MessageData_ofConstName(v_declName_2546_, v___x_2677_);
v___x_2864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2864_, 0, v___x_2862_);
lean_ctor_set(v___x_2864_, 1, v___x_2863_);
v___x_2865_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__53_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__53_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__53_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2864_);
lean_ctor_set(v___x_2866_, 1, v___x_2865_);
v___x_2867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2867_, 0, v___x_2866_);
lean_ctor_set(v___x_2867_, 1, v___x_2859_);
v___x_2868_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__55_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__55_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__55_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2869_, 0, v___x_2867_);
lean_ctor_set(v___x_2869_, 1, v___x_2868_);
v___x_2870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2870_, 0, v___x_2869_);
lean_ctor_set(v___x_2870_, 1, v___x_2832_);
if (lean_obj_tag(v___y_2805_) == 1)
{
lean_object* v_val_2871_; lean_object* v___x_2872_; 
v_val_2871_ = lean_ctor_get(v___y_2805_, 0);
v___x_2872_ = l_Lean_Syntax_getRange_x3f(v_val_2871_, v___x_2677_);
if (lean_obj_tag(v___x_2872_) == 0)
{
lean_dec_ref(v___x_2859_);
lean_dec(v_val_2852_);
v___y_2784_ = v___y_2805_;
v___y_2785_ = v_val_2812_;
v___y_2786_ = v___y_2806_;
v___y_2787_ = v_env_2819_;
v___y_2788_ = v___x_2817_;
v___y_2789_ = v___y_2807_;
v___y_2790_ = v___y_2808_;
v___y_2791_ = v___y_2809_;
v_msg_2792_ = v___x_2870_;
v___y_2793_ = v___y_2810_;
v___y_2794_ = v___y_2811_;
goto v___jp_2783_;
}
else
{
lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2935_; 
v_isSharedCheck_2935_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_2935_ == 0)
{
lean_object* v_unused_2936_; 
v_unused_2936_ = lean_ctor_get(v___x_2872_, 0);
lean_dec(v_unused_2936_);
v___x_2874_ = v___x_2872_;
v_isShared_2875_ = v_isSharedCheck_2935_;
goto v_resetjp_2873_;
}
else
{
lean_dec(v___x_2872_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2935_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
uint8_t v___x_2876_; uint8_t v___x_2877_; uint8_t v___x_2878_; lean_object* v___x_2879_; uint64_t v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; 
v___x_2876_ = 1;
v___x_2877_ = 0;
v___x_2878_ = 2;
v___x_2879_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_2879_, 0, v___x_2853_);
lean_ctor_set_uint8(v___x_2879_, 1, v___x_2853_);
lean_ctor_set_uint8(v___x_2879_, 2, v___x_2853_);
lean_ctor_set_uint8(v___x_2879_, 3, v___x_2853_);
lean_ctor_set_uint8(v___x_2879_, 4, v___x_2853_);
lean_ctor_set_uint8(v___x_2879_, 5, v___x_2822_);
lean_ctor_set_uint8(v___x_2879_, 6, v___x_2822_);
lean_ctor_set_uint8(v___x_2879_, 7, v___x_2853_);
lean_ctor_set_uint8(v___x_2879_, 8, v___x_2822_);
lean_ctor_set_uint8(v___x_2879_, 9, v___x_2876_);
lean_ctor_set_uint8(v___x_2879_, 10, v___x_2877_);
lean_ctor_set_uint8(v___x_2879_, 11, v___x_2822_);
lean_ctor_set_uint8(v___x_2879_, 12, v___x_2822_);
lean_ctor_set_uint8(v___x_2879_, 13, v___x_2822_);
lean_ctor_set_uint8(v___x_2879_, 14, v___x_2878_);
lean_ctor_set_uint8(v___x_2879_, 15, v___x_2822_);
lean_ctor_set_uint8(v___x_2879_, 16, v___x_2822_);
lean_ctor_set_uint8(v___x_2879_, 17, v___x_2822_);
lean_ctor_set_uint8(v___x_2879_, 18, v___x_2822_);
lean_ctor_set_uint8(v___x_2879_, 19, v___x_2853_);
v___x_2880_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2879_);
v___x_2881_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2881_, 0, v___x_2879_);
lean_ctor_set_uint64(v___x_2881_, sizeof(void*)*1, v___x_2880_);
v___x_2882_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_2883_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__27_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__27_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__27_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2884_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__28_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_2885_ = lean_box(0);
lean_inc_n(v___x_2543_, 2);
v___x_2886_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2886_, 0, v___x_2881_);
lean_ctor_set(v___x_2886_, 1, v___x_2543_);
lean_ctor_set(v___x_2886_, 2, v___x_2883_);
lean_ctor_set(v___x_2886_, 3, v___x_2884_);
lean_ctor_set(v___x_2886_, 4, v___x_2885_);
lean_ctor_set(v___x_2886_, 5, v___x_2680_);
lean_ctor_set(v___x_2886_, 6, v___x_2885_);
lean_ctor_set_uint8(v___x_2886_, sizeof(void*)*7, v___x_2542_);
lean_ctor_set_uint8(v___x_2886_, sizeof(void*)*7 + 1, v___x_2542_);
lean_ctor_set_uint8(v___x_2886_, sizeof(void*)*7 + 2, v___x_2542_);
lean_ctor_set_uint8(v___x_2886_, sizeof(void*)*7 + 3, v___x_2677_);
v___x_2887_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2888_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2889_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2890_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2887_);
lean_ctor_set(v___x_2890_, 1, v___x_2888_);
lean_ctor_set(v___x_2890_, 2, v___x_2543_);
lean_ctor_set(v___x_2890_, 3, v___x_2882_);
lean_ctor_set(v___x_2890_, 4, v___x_2889_);
v___x_2891_ = lean_st_mk_ref(v___x_2890_);
v___x_2892_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6(v_val_2852_, v___x_2542_, v___x_2886_, v___x_2891_, v___y_2810_, v___y_2811_);
lean_dec_ref_known(v___x_2886_, 7);
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_object* v_a_2893_; lean_object* v___x_2894_; 
v_a_2893_ = lean_ctor_get(v___x_2892_, 0);
lean_inc(v_a_2893_);
lean_dec_ref_known(v___x_2892_, 1);
v___x_2894_ = lean_st_ref_get(v___x_2891_);
lean_dec(v___x_2891_);
lean_dec(v___x_2894_);
if (lean_obj_tag(v_a_2893_) == 1)
{
lean_object* v_val_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2926_; 
v_val_2895_ = lean_ctor_get(v_a_2893_, 0);
v_isSharedCheck_2926_ = !lean_is_exclusive(v_a_2893_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2897_ = v_a_2893_;
v_isShared_2898_ = v_isSharedCheck_2926_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_val_2895_);
lean_dec(v_a_2893_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2926_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2905_; 
v___x_2899_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__57_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__57_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__57_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2900_, 0, v___x_2899_);
lean_ctor_set(v___x_2900_, 1, v___x_2859_);
v___x_2901_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__59_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__59_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__59_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2900_);
lean_ctor_set(v___x_2902_, 1, v___x_2901_);
v___x_2903_ = l_Lean_Name_toString(v_val_2895_, v___x_2677_);
if (v_isShared_2875_ == 0)
{
lean_ctor_set(v___x_2874_, 0, v___x_2903_);
v___x_2905_ = v___x_2874_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v___x_2903_);
v___x_2905_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
lean_object* v___x_2906_; uint8_t v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2912_; 
v___x_2906_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2906_, 0, v___x_2905_);
lean_ctor_set(v___x_2906_, 1, v___x_2885_);
lean_ctor_set(v___x_2906_, 2, v___x_2885_);
lean_ctor_set(v___x_2906_, 3, v___x_2885_);
lean_ctor_set(v___x_2906_, 4, v___x_2885_);
lean_ctor_set(v___x_2906_, 5, v___x_2885_);
v___x_2907_ = 0;
v___x_2908_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2908_, 0, v___x_2906_);
lean_ctor_set(v___x_2908_, 1, v___x_2885_);
lean_ctor_set(v___x_2908_, 2, v___x_2885_);
lean_ctor_set_uint8(v___x_2908_, sizeof(void*)*3, v___x_2907_);
v___x_2909_ = lean_mk_empty_array_with_capacity(v___x_2681_);
v___x_2910_ = lean_array_push(v___x_2909_, v___x_2908_);
lean_inc(v_val_2871_);
if (v_isShared_2898_ == 0)
{
lean_ctor_set(v___x_2897_, 0, v_val_2871_);
v___x_2912_ = v___x_2897_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v_val_2871_);
v___x_2912_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
lean_object* v___x_2913_; 
v___x_2913_ = l_Lean_MessageData_hint(v___x_2902_, v___x_2910_, v___x_2912_, v___x_2885_, v___x_2542_, v___y_2810_, v___y_2811_);
lean_dec_ref(v___x_2910_);
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_object* v_a_2914_; lean_object* v___x_2915_; 
v_a_2914_ = lean_ctor_get(v___x_2913_, 0);
lean_inc(v_a_2914_);
lean_dec_ref_known(v___x_2913_, 1);
v___x_2915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2915_, 0, v___x_2870_);
lean_ctor_set(v___x_2915_, 1, v_a_2914_);
v___y_2784_ = v___y_2805_;
v___y_2785_ = v_val_2812_;
v___y_2786_ = v___y_2806_;
v___y_2787_ = v_env_2819_;
v___y_2788_ = v___x_2817_;
v___y_2789_ = v___y_2807_;
v___y_2790_ = v___y_2808_;
v___y_2791_ = v___y_2809_;
v_msg_2792_ = v___x_2915_;
v___y_2793_ = v___y_2810_;
v___y_2794_ = v___y_2811_;
goto v___jp_2783_;
}
else
{
lean_object* v_a_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2923_; 
lean_dec_ref_known(v___y_2805_, 1);
lean_dec_ref_known(v___x_2870_, 2);
lean_dec_ref(v_env_2819_);
lean_dec(v_val_2812_);
lean_dec_ref_known(v___y_2809_, 1);
lean_dec(v___y_2808_);
lean_dec(v___y_2807_);
lean_dec(v___y_2806_);
lean_dec(v_stx_2547_);
lean_dec(v_declName_2546_);
lean_dec(v___x_2543_);
lean_dec_ref(v___f_2541_);
v_a_2916_ = lean_ctor_get(v___x_2913_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v___x_2913_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2918_ = v___x_2913_;
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_a_2916_);
lean_dec(v___x_2913_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2921_; 
if (v_isShared_2919_ == 0)
{
v___x_2921_ = v___x_2918_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v_a_2916_);
v___x_2921_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
return v___x_2921_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2893_);
lean_del_object(v___x_2874_);
lean_dec_ref(v___x_2859_);
v___y_2784_ = v___y_2805_;
v___y_2785_ = v_val_2812_;
v___y_2786_ = v___y_2806_;
v___y_2787_ = v_env_2819_;
v___y_2788_ = v___x_2817_;
v___y_2789_ = v___y_2807_;
v___y_2790_ = v___y_2808_;
v___y_2791_ = v___y_2809_;
v_msg_2792_ = v___x_2870_;
v___y_2793_ = v___y_2810_;
v___y_2794_ = v___y_2811_;
goto v___jp_2783_;
}
}
else
{
lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2934_; 
lean_dec(v___x_2891_);
lean_del_object(v___x_2874_);
lean_dec_ref_known(v___y_2805_, 1);
lean_dec_ref_known(v___x_2870_, 2);
lean_dec_ref(v___x_2859_);
lean_dec_ref(v_env_2819_);
lean_dec_ref_known(v___y_2809_, 1);
lean_dec(v_val_2812_);
lean_dec(v___y_2808_);
lean_dec(v___y_2807_);
lean_dec(v___y_2806_);
lean_dec(v_stx_2547_);
lean_dec(v_declName_2546_);
lean_dec(v___x_2543_);
lean_dec_ref(v___f_2541_);
v_a_2927_ = lean_ctor_get(v___x_2892_, 0);
v_isSharedCheck_2934_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2929_ = v___x_2892_;
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_a_2927_);
lean_dec(v___x_2892_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2932_; 
if (v_isShared_2930_ == 0)
{
v___x_2932_ = v___x_2929_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_a_2927_);
v___x_2932_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
return v___x_2932_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_2859_);
lean_dec(v_val_2852_);
v___y_2784_ = v___y_2805_;
v___y_2785_ = v_val_2812_;
v___y_2786_ = v___y_2806_;
v___y_2787_ = v_env_2819_;
v___y_2788_ = v___x_2817_;
v___y_2789_ = v___y_2807_;
v___y_2790_ = v___y_2808_;
v___y_2791_ = v___y_2809_;
v_msg_2792_ = v___x_2870_;
v___y_2793_ = v___y_2810_;
v___y_2794_ = v___y_2811_;
goto v___jp_2783_;
}
}
else
{
lean_dec(v_val_2852_);
lean_dec_ref(v___x_2832_);
v___y_2728_ = v___y_2805_;
v___y_2729_ = v_val_2812_;
v___y_2730_ = v___y_2806_;
v___y_2731_ = v___x_2817_;
v___y_2732_ = v_env_2819_;
v___y_2733_ = v___y_2807_;
v___y_2734_ = v___y_2808_;
v___y_2735_ = v___y_2809_;
v___y_2736_ = v___y_2810_;
v___y_2737_ = v___y_2811_;
goto v___jp_2727_;
}
}
}
else
{
lean_dec(v___x_2823_);
v___y_2728_ = v___y_2805_;
v___y_2729_ = v_val_2812_;
v___y_2730_ = v___y_2806_;
v___y_2731_ = v___x_2817_;
v___y_2732_ = v_env_2819_;
v___y_2733_ = v___y_2807_;
v___y_2734_ = v___y_2808_;
v___y_2735_ = v___y_2809_;
v___y_2736_ = v___y_2810_;
v___y_2737_ = v___y_2811_;
goto v___jp_2727_;
}
}
}
}
else
{
lean_object* v_a_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2944_; 
lean_dec_ref_known(v___y_2809_, 1);
lean_dec(v___y_2808_);
lean_dec(v___y_2807_);
lean_dec(v___y_2806_);
lean_dec(v___y_2805_);
lean_dec(v_stx_2547_);
lean_dec(v_declName_2546_);
lean_dec_ref(v___x_2544_);
lean_dec(v___x_2543_);
lean_dec_ref(v___f_2541_);
v_a_2937_ = lean_ctor_get(v___x_2813_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2813_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2939_ = v___x_2813_;
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_a_2937_);
lean_dec(v___x_2813_);
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
else
{
lean_dec(v___y_2808_);
lean_dec(v_declName_2546_);
lean_dec_ref(v___x_2544_);
lean_dec(v___x_2543_);
lean_dec_ref(v___f_2541_);
v___y_2619_ = v___y_2805_;
v___y_2620_ = v___y_2806_;
v___y_2621_ = v___y_2807_;
v___y_2622_ = v___y_2809_;
v___y_2623_ = v___y_2810_;
v___y_2624_ = v___y_2811_;
goto v___jp_2618_;
}
}
v___jp_2945_:
{
lean_object* v___x_2953_; uint8_t v___x_2954_; 
lean_inc(v_declName_2546_);
v___x_2953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2953_, 0, v_declName_2546_);
v___x_2954_ = l_instBEqOption_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__7(v_a_2952_, v___x_2953_);
lean_dec_ref_known(v___x_2953_, 1);
if (v___x_2954_ == 0)
{
v___y_2805_ = v___y_2946_;
v___y_2806_ = v___y_2947_;
v___y_2807_ = v___y_2948_;
v___y_2808_ = v___y_2950_;
v___y_2809_ = v_a_2952_;
v___y_2810_ = v___y_2951_;
v___y_2811_ = v___y_2949_;
goto v___jp_2804_;
}
else
{
lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v_a_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2968_; 
lean_dec(v_a_2952_);
lean_dec(v___y_2950_);
lean_dec(v___y_2948_);
lean_dec(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec(v_stx_2547_);
lean_dec_ref(v___x_2544_);
lean_dec(v___x_2543_);
lean_dec_ref(v___f_2541_);
v___x_2955_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__61_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__61_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__61_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2956_ = l_Lean_MessageData_ofConstName(v_declName_2546_, v___x_2677_);
v___x_2957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2957_, 0, v___x_2955_);
lean_ctor_set(v___x_2957_, 1, v___x_2956_);
v___x_2958_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__63_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__63_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__63_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2957_);
lean_ctor_set(v___x_2959_, 1, v___x_2958_);
v___x_2960_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0___redArg(v___x_2959_, v___y_2951_, v___y_2949_);
v_a_2961_ = lean_ctor_get(v___x_2960_, 0);
v_isSharedCheck_2968_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2963_ = v___x_2960_;
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_a_2961_);
lean_dec(v___x_2960_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2966_; 
if (v_isShared_2964_ == 0)
{
v___x_2966_ = v___x_2963_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_a_2961_);
v___x_2966_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
return v___x_2966_;
}
}
}
}
v___jp_2969_:
{
if (lean_obj_tag(v___y_2970_) == 0)
{
lean_object* v___x_2976_; 
v___x_2976_ = lean_box(0);
v___y_2946_ = v___y_2970_;
v___y_2947_ = v___y_2971_;
v___y_2948_ = v_since_x3f_2973_;
v___y_2949_ = v___y_2975_;
v___y_2950_ = v___y_2972_;
v___y_2951_ = v___y_2974_;
v_a_2952_ = v___x_2976_;
goto v___jp_2945_;
}
else
{
lean_object* v_val_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; 
v_val_2977_ = lean_ctor_get(v___y_2970_, 0);
v___x_2978_ = lean_box(0);
lean_inc(v_val_2977_);
v___x_2979_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_val_2977_, v___x_2978_, v___y_2974_, v___y_2975_);
if (lean_obj_tag(v___x_2979_) == 0)
{
lean_object* v_a_2980_; lean_object* v___x_2981_; 
v_a_2980_ = lean_ctor_get(v___x_2979_, 0);
lean_inc(v_a_2980_);
lean_dec_ref_known(v___x_2979_, 1);
v___x_2981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2981_, 0, v_a_2980_);
v___y_2946_ = v___y_2970_;
v___y_2947_ = v___y_2971_;
v___y_2948_ = v_since_x3f_2973_;
v___y_2949_ = v___y_2975_;
v___y_2950_ = v___y_2972_;
v___y_2951_ = v___y_2974_;
v_a_2952_ = v___x_2981_;
goto v___jp_2945_;
}
else
{
lean_object* v_a_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_2989_; 
lean_dec_ref_known(v___y_2970_, 1);
lean_dec(v_since_x3f_2973_);
lean_dec(v___y_2972_);
lean_dec(v___y_2971_);
lean_dec(v_stx_2547_);
lean_dec(v_declName_2546_);
lean_dec_ref(v___x_2544_);
lean_dec(v___x_2543_);
lean_dec_ref(v___f_2541_);
v_a_2982_ = lean_ctor_get(v___x_2979_, 0);
v_isSharedCheck_2989_ = !lean_is_exclusive(v___x_2979_);
if (v_isSharedCheck_2989_ == 0)
{
v___x_2984_ = v___x_2979_;
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_a_2982_);
lean_dec(v___x_2979_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v___x_2987_; 
if (v_isShared_2985_ == 0)
{
v___x_2987_ = v___x_2984_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v_a_2982_);
v___x_2987_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
return v___x_2987_;
}
}
}
}
}
v___jp_2990_:
{
lean_object* v___x_2997_; lean_object* v___x_2998_; uint8_t v___x_2999_; 
v___x_2997_ = lean_unsigned_to_nat(4u);
v___x_2998_ = l_Lean_Syntax_getArg(v_stx_2547_, v___x_2997_);
v___x_2999_ = l_Lean_Syntax_isNone(v___x_2998_);
if (v___x_2999_ == 0)
{
lean_object* v___x_3000_; uint8_t v___x_3001_; 
v___x_3000_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_2998_);
v___x_3001_ = l_Lean_Syntax_matchesNull(v___x_2998_, v___x_3000_);
if (v___x_3001_ == 0)
{
lean_object* v___x_3002_; lean_object* v___x_3003_; 
lean_dec(v___x_2998_);
lean_dec(v_typeChanged_x3f_2994_);
lean_dec(v___y_2992_);
lean_dec(v___y_2991_);
lean_dec(v_stx_2547_);
lean_dec(v_declName_2546_);
lean_dec_ref(v___x_2544_);
lean_dec(v___x_2543_);
lean_dec_ref(v___f_2541_);
v___x_3002_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_3003_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0___redArg(v___x_3002_, v___y_2995_, v___y_2996_);
return v___x_3003_;
}
else
{
lean_object* v___x_3004_; lean_object* v___x_3005_; 
v___x_3004_ = l_Lean_Syntax_getArg(v___x_2998_, v___y_2993_);
lean_dec(v___x_2998_);
v___x_3005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3005_, 0, v___x_3004_);
v___y_2970_ = v___y_2991_;
v___y_2971_ = v___y_2992_;
v___y_2972_ = v_typeChanged_x3f_2994_;
v_since_x3f_2973_ = v___x_3005_;
v___y_2974_ = v___y_2995_;
v___y_2975_ = v___y_2996_;
goto v___jp_2969_;
}
}
else
{
lean_object* v___x_3006_; 
lean_dec(v___x_2998_);
v___x_3006_ = lean_box(0);
v___y_2970_ = v___y_2991_;
v___y_2971_ = v___y_2992_;
v___y_2972_ = v_typeChanged_x3f_2994_;
v_since_x3f_2973_ = v___x_3006_;
v___y_2974_ = v___y_2995_;
v___y_2975_ = v___y_2996_;
goto v___jp_2969_;
}
}
v___jp_3007_:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; uint8_t v___x_3014_; 
v___x_3012_ = lean_unsigned_to_nat(3u);
v___x_3013_ = l_Lean_Syntax_getArg(v_stx_2547_, v___x_3012_);
v___x_3014_ = l_Lean_Syntax_isNone(v___x_3013_);
if (v___x_3014_ == 0)
{
uint8_t v___x_3015_; 
lean_inc(v___x_3013_);
v___x_3015_ = l_Lean_Syntax_matchesNull(v___x_3013_, v___x_2681_);
if (v___x_3015_ == 0)
{
lean_object* v___x_3016_; lean_object* v___x_3017_; 
lean_dec(v___x_3013_);
lean_dec(v_text_x3f_3009_);
lean_dec(v___y_3008_);
lean_dec(v_stx_2547_);
lean_dec(v_declName_2546_);
lean_dec_ref(v___x_2544_);
lean_dec(v___x_2543_);
lean_dec_ref(v___f_2541_);
v___x_3016_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_3017_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0___redArg(v___x_3016_, v___y_3010_, v___y_3011_);
return v___x_3017_;
}
else
{
lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3018_ = l_Lean_Syntax_getArg(v___x_3013_, v___x_2680_);
lean_dec(v___x_3013_);
v___x_3019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3019_, 0, v___x_3018_);
v___y_2991_ = v___y_3008_;
v___y_2992_ = v_text_x3f_3009_;
v___y_2993_ = v___x_3012_;
v_typeChanged_x3f_2994_ = v___x_3019_;
v___y_2995_ = v___y_3010_;
v___y_2996_ = v___y_3011_;
goto v___jp_2990_;
}
}
else
{
lean_object* v___x_3020_; 
lean_dec(v___x_3013_);
v___x_3020_ = lean_box(0);
v___y_2991_ = v___y_3008_;
v___y_2992_ = v_text_x3f_3009_;
v___y_2993_ = v___x_3012_;
v_typeChanged_x3f_2994_ = v___x_3020_;
v___y_2995_ = v___y_3010_;
v___y_2996_ = v___y_3011_;
goto v___jp_2990_;
}
}
v___jp_3021_:
{
lean_object* v___x_3025_; lean_object* v___x_3026_; uint8_t v___x_3027_; 
v___x_3025_ = lean_unsigned_to_nat(2u);
v___x_3026_ = l_Lean_Syntax_getArg(v_stx_2547_, v___x_3025_);
v___x_3027_ = l_Lean_Syntax_isNone(v___x_3026_);
if (v___x_3027_ == 0)
{
uint8_t v___x_3028_; 
lean_inc(v___x_3026_);
v___x_3028_ = l_Lean_Syntax_matchesNull(v___x_3026_, v___x_2681_);
if (v___x_3028_ == 0)
{
lean_object* v___x_3029_; lean_object* v___x_3030_; 
lean_dec(v___x_3026_);
lean_dec(v_id_x3f_3022_);
lean_dec(v_stx_2547_);
lean_dec(v_declName_2546_);
lean_dec_ref(v___x_2544_);
lean_dec(v___x_2543_);
lean_dec_ref(v___f_2541_);
v___x_3029_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_3030_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0___redArg(v___x_3029_, v___y_3023_, v___y_3024_);
return v___x_3030_;
}
else
{
lean_object* v___x_3031_; lean_object* v___x_3032_; 
v___x_3031_ = l_Lean_Syntax_getArg(v___x_3026_, v___x_2680_);
lean_dec(v___x_3026_);
v___x_3032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3032_, 0, v___x_3031_);
v___y_3008_ = v_id_x3f_3022_;
v_text_x3f_3009_ = v___x_3032_;
v___y_3010_ = v___y_3023_;
v___y_3011_ = v___y_3024_;
goto v___jp_3007_;
}
}
else
{
lean_object* v___x_3033_; 
lean_dec(v___x_3026_);
v___x_3033_ = lean_box(0);
v___y_3008_ = v_id_x3f_3022_;
v_text_x3f_3009_ = v___x_3033_;
v___y_3010_ = v___y_3023_;
v___y_3011_ = v___y_3024_;
goto v___jp_3007_;
}
}
}
v___jp_2551_:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2555_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2555_, 0, v___y_2554_);
lean_ctor_set(v___x_2555_, 1, v___y_2553_);
lean_ctor_set(v___x_2555_, 2, v___y_2552_);
v___x_2556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2556_, 0, v___x_2555_);
return v___x_2556_;
}
v___jp_2557_:
{
if (lean_obj_tag(v___y_2558_) == 0)
{
lean_object* v___x_2563_; 
v___x_2563_ = l_Lean_Linter_mkSinceHint(v_stx_2547_, v___y_2561_, v___y_2562_);
if (lean_obj_tag(v___x_2563_) == 0)
{
lean_object* v_a_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; 
v_a_2564_ = lean_ctor_get(v___x_2563_, 0);
lean_inc(v_a_2564_);
lean_dec_ref_known(v___x_2563_, 1);
v___x_2565_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__1_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__1_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__1_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2566_, 0, v___x_2565_);
lean_ctor_set(v___x_2566_, 1, v_a_2564_);
v___x_2567_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1(v___x_2566_, v___y_2561_, v___y_2562_);
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_dec_ref_known(v___x_2567_, 1);
v___y_2552_ = v___y_2558_;
v___y_2553_ = v___y_2559_;
v___y_2554_ = v___y_2560_;
goto v___jp_2551_;
}
else
{
lean_object* v_a_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2575_; 
lean_dec(v___y_2560_);
lean_dec(v___y_2559_);
v_a_2568_ = lean_ctor_get(v___x_2567_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2570_ = v___x_2567_;
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_a_2568_);
lean_dec(v___x_2567_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2573_; 
if (v_isShared_2571_ == 0)
{
v___x_2573_ = v___x_2570_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_a_2568_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
}
}
else
{
lean_object* v_a_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2583_; 
lean_dec(v___y_2560_);
lean_dec(v___y_2559_);
v_a_2576_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2583_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2578_ = v___x_2563_;
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_a_2576_);
lean_dec(v___x_2563_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v___x_2581_; 
if (v_isShared_2579_ == 0)
{
v___x_2581_ = v___x_2578_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_a_2576_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
}
else
{
lean_dec(v_stx_2547_);
v___y_2552_ = v___y_2558_;
v___y_2553_ = v___y_2559_;
v___y_2554_ = v___y_2560_;
goto v___jp_2551_;
}
}
v___jp_2584_:
{
if (lean_obj_tag(v___y_2585_) == 0)
{
if (lean_obj_tag(v___y_2588_) == 0)
{
lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2591_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__4_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__4_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__4_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2592_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1(v___x_2591_, v___y_2587_, v___y_2586_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_dec_ref_known(v___x_2592_, 1);
v___y_2558_ = v___y_2590_;
v___y_2559_ = v___y_2588_;
v___y_2560_ = v___y_2589_;
v___y_2561_ = v___y_2587_;
v___y_2562_ = v___y_2586_;
goto v___jp_2557_;
}
else
{
lean_object* v_a_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2600_; 
lean_dec(v___y_2590_);
lean_dec(v___y_2589_);
lean_dec(v_stx_2547_);
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
else
{
v___y_2558_ = v___y_2590_;
v___y_2559_ = v___y_2588_;
v___y_2560_ = v___y_2589_;
v___y_2561_ = v___y_2587_;
v___y_2562_ = v___y_2586_;
goto v___jp_2557_;
}
}
else
{
lean_dec_ref_known(v___y_2585_, 1);
v___y_2558_ = v___y_2590_;
v___y_2559_ = v___y_2588_;
v___y_2560_ = v___y_2589_;
v___y_2561_ = v___y_2587_;
v___y_2562_ = v___y_2586_;
goto v___jp_2557_;
}
}
v___jp_2601_:
{
if (lean_obj_tag(v___y_2603_) == 0)
{
lean_object* v___x_2608_; 
v___x_2608_ = lean_box(0);
v___y_2585_ = v___y_2602_;
v___y_2586_ = v___y_2604_;
v___y_2587_ = v___y_2605_;
v___y_2588_ = v___y_2607_;
v___y_2589_ = v___y_2606_;
v___y_2590_ = v___x_2608_;
goto v___jp_2584_;
}
else
{
lean_object* v_val_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2617_; 
v_val_2609_ = lean_ctor_get(v___y_2603_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___y_2603_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2611_ = v___y_2603_;
v_isShared_2612_ = v_isSharedCheck_2617_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_val_2609_);
lean_dec(v___y_2603_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2617_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2613_; lean_object* v___x_2615_; 
v___x_2613_ = l_Lean_TSyntax_getString(v_val_2609_);
lean_dec(v_val_2609_);
if (v_isShared_2612_ == 0)
{
lean_ctor_set(v___x_2611_, 0, v___x_2613_);
v___x_2615_ = v___x_2611_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v___x_2613_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
v___y_2585_ = v___y_2602_;
v___y_2586_ = v___y_2604_;
v___y_2587_ = v___y_2605_;
v___y_2588_ = v___y_2607_;
v___y_2589_ = v___y_2606_;
v___y_2590_ = v___x_2615_;
goto v___jp_2584_;
}
}
}
}
v___jp_2618_:
{
if (lean_obj_tag(v___y_2620_) == 0)
{
lean_object* v___x_2625_; 
v___x_2625_ = lean_box(0);
v___y_2602_ = v___y_2619_;
v___y_2603_ = v___y_2621_;
v___y_2604_ = v___y_2624_;
v___y_2605_ = v___y_2623_;
v___y_2606_ = v___y_2622_;
v___y_2607_ = v___x_2625_;
goto v___jp_2601_;
}
else
{
lean_object* v_val_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2634_; 
v_val_2626_ = lean_ctor_get(v___y_2620_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___y_2620_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2628_ = v___y_2620_;
v_isShared_2629_ = v_isSharedCheck_2634_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_val_2626_);
lean_dec(v___y_2620_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2634_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v___x_2630_; lean_object* v___x_2632_; 
v___x_2630_ = l_Lean_TSyntax_getString(v_val_2626_);
lean_dec(v_val_2626_);
if (v_isShared_2629_ == 0)
{
lean_ctor_set(v___x_2628_, 0, v___x_2630_);
v___x_2632_ = v___x_2628_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v___x_2630_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
v___y_2602_ = v___y_2619_;
v___y_2603_ = v___y_2621_;
v___y_2604_ = v___y_2624_;
v___y_2605_ = v___y_2623_;
v___y_2606_ = v___y_2622_;
v___y_2607_ = v___x_2632_;
goto v___jp_2601_;
}
}
}
}
v___jp_2635_:
{
lean_object* v_type_2645_; lean_object* v_type_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; 
v_type_2645_ = lean_ctor_get(v___y_2640_, 2);
lean_inc_ref(v_type_2645_);
lean_dec_ref(v___y_2640_);
v_type_2646_ = lean_ctor_get(v___y_2639_, 2);
lean_inc_ref(v_type_2646_);
lean_dec_ref(v___y_2639_);
v___x_2647_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2648_ = l_Lean_indentExpr(v_type_2645_);
v___x_2649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2649_, 0, v___x_2647_);
lean_ctor_set(v___x_2649_, 1, v___x_2648_);
v___x_2650_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2651_, 0, v___x_2649_);
lean_ctor_set(v___x_2651_, 1, v___x_2650_);
v___x_2652_ = l_Lean_indentExpr(v_type_2646_);
v___x_2653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2653_, 0, v___x_2651_);
lean_ctor_set(v___x_2653_, 1, v___x_2652_);
v___x_2654_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__10_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__10_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__10_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_2655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2655_, 0, v___x_2653_);
lean_ctor_set(v___x_2655_, 1, v___x_2654_);
v___x_2656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2656_, 0, v___x_2655_);
lean_ctor_set(v___x_2656_, 1, v_hint_2642_);
v___x_2657_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__1(v___x_2656_, v___y_2643_, v___y_2644_);
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_dec_ref_known(v___x_2657_, 1);
v___y_2619_ = v___y_2636_;
v___y_2620_ = v___y_2637_;
v___y_2621_ = v___y_2638_;
v___y_2622_ = v___y_2641_;
v___y_2623_ = v___y_2643_;
v___y_2624_ = v___y_2644_;
goto v___jp_2618_;
}
else
{
lean_object* v_a_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2665_; 
lean_dec(v___y_2641_);
lean_dec(v___y_2638_);
lean_dec(v___y_2637_);
lean_dec(v___y_2636_);
lean_dec(v_stx_2547_);
v_a_2658_ = lean_ctor_get(v___x_2657_, 0);
v_isSharedCheck_2665_ = !lean_is_exclusive(v___x_2657_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2660_ = v___x_2657_;
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_a_2658_);
lean_dec(v___x_2657_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2663_; 
if (v_isShared_2661_ == 0)
{
v___x_2663_ = v___x_2660_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v_a_2658_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
return v___x_2663_;
}
}
}
}
v___jp_2666_:
{
lean_object* v___x_2675_; 
v___x_2675_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__14_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__14_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__14_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___y_2636_ = v___y_2668_;
v___y_2637_ = v___y_2670_;
v___y_2638_ = v___y_2672_;
v___y_2639_ = v___y_2671_;
v___y_2640_ = v___y_2673_;
v___y_2641_ = v___y_2674_;
v_hint_2642_ = v___x_2675_;
v___y_2643_ = v___y_2669_;
v___y_2644_ = v___y_2667_;
goto v___jp_2635_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2____boxed(lean_object* v___x_3042_, lean_object* v___x_3043_, lean_object* v___f_3044_, lean_object* v___x_3045_, lean_object* v___x_3046_, lean_object* v___x_3047_, lean_object* v_a_3048_, lean_object* v_declName_3049_, lean_object* v_stx_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_){
_start:
{
uint8_t v___x_48164__boxed_3054_; lean_object* v_res_3055_; 
v___x_48164__boxed_3054_ = lean_unbox(v___x_3045_);
v_res_3055_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(v___x_3042_, v___x_3043_, v___f_3044_, v___x_48164__boxed_3054_, v___x_3046_, v___x_3047_, v_a_3048_, v_declName_3049_, v_stx_3050_, v___y_3051_, v___y_3052_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3051_);
lean_dec_ref(v_a_3048_);
return v_res_3055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3075_; lean_object* v___f_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; uint8_t v___x_3081_; lean_object* v___f_3082_; lean_object* v___x_3083_; 
v___f_3075_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___f_3076_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_3077_ = lean_box(1);
v___x_3078_ = ((lean_object*)(l_Lean_Linter_instInhabitedDeprecationEntry_default));
v___x_3079_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_));
v___x_3080_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_3081_ = 0;
v___f_3082_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_3083_ = l_Lean_registerParametricAttributeExt___redArg(v___x_3080_, v___x_3081_, v___f_3082_, v___x_3081_);
if (lean_obj_tag(v___x_3083_) == 0)
{
lean_object* v_a_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___f_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; 
v_a_3084_ = lean_ctor_get(v___x_3083_, 0);
lean_inc_n(v_a_3084_, 2);
lean_dec_ref_known(v___x_3083_, 1);
v___x_3085_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_));
v___x_3086_ = lean_box(v___x_3081_);
v___f_3087_ = lean_alloc_closure((void*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2____boxed), 12, 7);
lean_closure_set(v___f_3087_, 0, v___x_3079_);
lean_closure_set(v___f_3087_, 1, v___x_3085_);
lean_closure_set(v___f_3087_, 2, v___f_3075_);
lean_closure_set(v___f_3087_, 3, v___x_3086_);
lean_closure_set(v___f_3087_, 4, v___x_3077_);
lean_closure_set(v___f_3087_, 5, v___x_3078_);
lean_closure_set(v___f_3087_, 6, v_a_3084_);
v___x_3088_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_3089_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3089_, 0, v___x_3088_);
lean_ctor_set(v___x_3089_, 1, v___f_3087_);
lean_ctor_set(v___x_3089_, 2, v___f_3076_);
lean_ctor_set(v___x_3089_, 3, v___f_3082_);
lean_ctor_set_uint8(v___x_3089_, sizeof(void*)*4, v___x_3081_);
v___x_3090_ = l_Lean_registerParametricAttributeForExt___redArg(v___x_3089_, v_a_3084_);
return v___x_3090_;
}
else
{
lean_object* v_a_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3098_; 
v_a_3091_ = lean_ctor_get(v___x_3083_, 0);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3093_ = v___x_3083_;
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_a_3091_);
lean_dec(v___x_3083_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3096_; 
if (v_isShared_3094_ == 0)
{
v___x_3096_ = v___x_3093_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_a_3091_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2____boxed(lean_object* v_a_3099_){
_start:
{
lean_object* v_res_3100_; 
v_res_3100_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_();
return v_res_3100_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_3101_, lean_object* v_msg_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_){
_start:
{
lean_object* v___x_3106_; 
v___x_3106_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0___redArg(v_msg_3102_, v___y_3103_, v___y_3104_);
return v___x_3106_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_3107_, lean_object* v_msg_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_){
_start:
{
lean_object* v_res_3112_; 
v_res_3112_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0(v_00_u03b1_3107_, v_msg_3108_, v___y_3109_, v___y_3110_);
lean_dec(v___y_3110_);
lean_dec_ref(v___y_3109_);
return v_res_3112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__3_spec__8(lean_object* v_o_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_){
_start:
{
lean_object* v___x_3117_; 
v___x_3117_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__3_spec__8___redArg(v_o_3113_, v___y_3115_);
return v___x_3117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__3_spec__8___boxed(lean_object* v_o_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_){
_start:
{
lean_object* v_res_3122_; 
v_res_3122_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__3_spec__8(v_o_3118_, v___y_3119_, v___y_3120_);
lean_dec(v___y_3120_);
lean_dec_ref(v___y_3119_);
return v_res_3122_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__4_spec__10(lean_object* v_00_u03b2_3123_){
_start:
{
lean_object* v___x_3124_; 
v___x_3124_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
return v___x_3124_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__4___redArg(){
_start:
{
lean_object* v___x_3126_; 
v___x_3126_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
return v___x_3126_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__4___redArg___boxed(lean_object* v___dummy_3127_){
_start:
{
lean_object* v_res_3128_; 
v_res_3128_ = l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__4___redArg();
return v_res_3128_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__4(lean_object* v_00_u03b2_3129_){
_start:
{
lean_object* v___x_3130_; 
v___x_3130_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
return v___x_3130_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__6(lean_object* v_00_u03b2_3131_, lean_object* v_m_3132_, lean_object* v_a_3133_){
_start:
{
lean_object* v___x_3134_; 
v___x_3134_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__6___redArg(v_m_3132_, v_a_3133_);
return v___x_3134_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__6___boxed(lean_object* v_00_u03b2_3135_, lean_object* v_m_3136_, lean_object* v_a_3137_){
_start:
{
lean_object* v_res_3138_; 
v_res_3138_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__6(v_00_u03b2_3135_, v_m_3136_, v_a_3137_);
lean_dec(v_a_3137_);
lean_dec_ref(v_m_3136_);
return v_res_3138_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8(lean_object* v_00_u03b2_3139_, lean_object* v_x_3140_, lean_object* v_x_3141_){
_start:
{
uint8_t v___x_3142_; 
v___x_3142_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg(v_x_3140_, v_x_3141_);
return v___x_3142_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_3143_, lean_object* v_x_3144_, lean_object* v_x_3145_){
_start:
{
uint8_t v_res_3146_; lean_object* v_r_3147_; 
v_res_3146_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8(v_00_u03b2_3143_, v_x_3144_, v_x_3145_);
lean_dec_ref(v_x_3145_);
lean_dec_ref(v_x_3144_);
v_r_3147_ = lean_box(v_res_3146_);
return v_r_3147_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__6_spec__12(lean_object* v_00_u03b2_3148_, lean_object* v_a_3149_, lean_object* v_x_3150_){
_start:
{
lean_object* v___x_3151_; 
v___x_3151_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg(v_a_3149_, v_x_3150_);
return v___x_3151_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__6_spec__12___boxed(lean_object* v_00_u03b2_3152_, lean_object* v_a_3153_, lean_object* v_x_3154_){
_start:
{
lean_object* v_res_3155_; 
v_res_3155_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__6_spec__12(v_00_u03b2_3152_, v_a_3153_, v_x_3154_);
lean_dec(v_x_3154_);
lean_dec(v_a_3153_);
return v_res_3155_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__19(lean_object* v_00_u03b4_3156_, lean_object* v_t_3157_, lean_object* v_k_3158_){
_start:
{
lean_object* v___x_3159_; 
v___x_3159_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__19___redArg(v_t_3157_, v_k_3158_);
return v___x_3159_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__19___boxed(lean_object* v_00_u03b4_3160_, lean_object* v_t_3161_, lean_object* v_k_3162_){
_start:
{
lean_object* v_res_3163_; 
v_res_3163_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__19(v_00_u03b4_3160_, v_t_3161_, v_k_3162_);
lean_dec(v_k_3162_);
lean_dec(v_t_3161_);
return v_res_3163_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14(lean_object* v_00_u03b2_3164_, lean_object* v_x_3165_, size_t v_x_3166_, lean_object* v_x_3167_){
_start:
{
uint8_t v___x_3168_; 
v___x_3168_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14___redArg(v_x_3165_, v_x_3166_, v_x_3167_);
return v___x_3168_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14___boxed(lean_object* v_00_u03b2_3169_, lean_object* v_x_3170_, lean_object* v_x_3171_, lean_object* v_x_3172_){
_start:
{
size_t v_x_49432__boxed_3173_; uint8_t v_res_3174_; lean_object* v_r_3175_; 
v_x_49432__boxed_3173_ = lean_unbox_usize(v_x_3171_);
lean_dec(v_x_3171_);
v_res_3174_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14(v_00_u03b2_3169_, v_x_3170_, v_x_49432__boxed_3173_, v_x_3172_);
lean_dec_ref(v_x_3172_);
lean_dec_ref(v_x_3170_);
v_r_3175_ = lean_box(v_res_3174_);
return v_r_3175_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22(lean_object* v_givenName_3176_, lean_object* v_auxDeclToFullName_3177_, lean_object* v___x_3178_, lean_object* v_givenNameView_3179_, lean_object* v_as_3180_, lean_object* v_i_3181_, lean_object* v_a_3182_){
_start:
{
lean_object* v___x_3183_; 
v___x_3183_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22___redArg(v_givenName_3176_, v_auxDeclToFullName_3177_, v___x_3178_, v_givenNameView_3179_, v_as_3180_, v_i_3181_);
return v___x_3183_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22___boxed(lean_object* v_givenName_3184_, lean_object* v_auxDeclToFullName_3185_, lean_object* v___x_3186_, lean_object* v_givenNameView_3187_, lean_object* v_as_3188_, lean_object* v_i_3189_, lean_object* v_a_3190_){
_start:
{
lean_object* v_res_3191_; 
v_res_3191_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22(v_givenName_3184_, v_auxDeclToFullName_3185_, v___x_3186_, v_givenNameView_3187_, v_as_3188_, v_i_3189_, v_a_3190_);
lean_dec_ref(v_as_3188_);
lean_dec(v_auxDeclToFullName_3185_);
lean_dec(v_givenName_3184_);
return v_res_3191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__25(lean_object* v_localDecl_x3f_3192_, lean_object* v_givenName_3193_, lean_object* v_as_3194_, lean_object* v_i_3195_, lean_object* v_a_3196_){
_start:
{
lean_object* v___x_3197_; 
v___x_3197_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__25___redArg(v_localDecl_x3f_3192_, v_givenName_3193_, v_as_3194_, v_i_3195_);
return v___x_3197_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__25___boxed(lean_object* v_localDecl_x3f_3198_, lean_object* v_givenName_3199_, lean_object* v_as_3200_, lean_object* v_i_3201_, lean_object* v_a_3202_){
_start:
{
lean_object* v_res_3203_; 
v_res_3203_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__25(v_localDecl_x3f_3198_, v_givenName_3199_, v_as_3200_, v_i_3201_, v_a_3202_);
lean_dec_ref(v_as_3200_);
lean_dec(v_givenName_3199_);
lean_dec(v_localDecl_x3f_3198_);
return v_res_3203_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24_spec__32(lean_object* v_n_u2080_3204_, lean_object* v_filter_3205_, lean_object* v_view_x3f_3206_, lean_object* v_as_3207_, lean_object* v_as_x27_3208_, lean_object* v_b_3209_, lean_object* v_a_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_){
_start:
{
lean_object* v___x_3216_; 
v___x_3216_ = l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24_spec__32___redArg(v_n_u2080_3204_, v_filter_3205_, v_view_x3f_3206_, v_as_x27_3208_, v_b_3209_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_);
return v___x_3216_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24_spec__32___boxed(lean_object* v_n_u2080_3217_, lean_object* v_filter_3218_, lean_object* v_view_x3f_3219_, lean_object* v_as_3220_, lean_object* v_as_x27_3221_, lean_object* v_b_3222_, lean_object* v_a_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_){
_start:
{
lean_object* v_res_3229_; 
v_res_3229_ = l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__24_spec__32(v_n_u2080_3217_, v_filter_3218_, v_view_x3f_3219_, v_as_3220_, v_as_x27_3221_, v_b_3222_, v_a_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_);
lean_dec(v___y_3227_);
lean_dec_ref(v___y_3226_);
lean_dec(v___y_3225_);
lean_dec_ref(v___y_3224_);
lean_dec(v_as_x27_3221_);
lean_dec(v_as_3220_);
lean_dec(v_n_u2080_3217_);
return v_res_3229_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14_spec__19(lean_object* v_00_u03b2_3230_, lean_object* v_keys_3231_, lean_object* v_vals_3232_, lean_object* v_heq_3233_, lean_object* v_i_3234_, lean_object* v_k_3235_){
_start:
{
uint8_t v___x_3236_; 
v___x_3236_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14_spec__19___redArg(v_keys_3231_, v_i_3234_, v_k_3235_);
return v___x_3236_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14_spec__19___boxed(lean_object* v_00_u03b2_3237_, lean_object* v_keys_3238_, lean_object* v_vals_3239_, lean_object* v_heq_3240_, lean_object* v_i_3241_, lean_object* v_k_3242_){
_start:
{
uint8_t v_res_3243_; lean_object* v_r_3244_; 
v_res_3243_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14_spec__19(v_00_u03b2_3237_, v_keys_3238_, v_vals_3239_, v_heq_3240_, v_i_3241_, v_k_3242_);
lean_dec_ref(v_k_3242_);
lean_dec_ref(v_vals_3239_);
lean_dec_ref(v_keys_3238_);
v_r_3244_ = lean_box(v_res_3243_);
return v_r_3244_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23_spec__26(lean_object* v_givenName_3245_, lean_object* v_auxDeclToFullName_3246_, lean_object* v___x_3247_, lean_object* v_givenNameView_3248_, lean_object* v_as_3249_, lean_object* v_i_3250_, lean_object* v_a_3251_){
_start:
{
lean_object* v___x_3252_; 
v___x_3252_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23_spec__26___redArg(v_givenName_3245_, v_auxDeclToFullName_3246_, v___x_3247_, v_givenNameView_3248_, v_as_3249_, v_i_3250_);
return v___x_3252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23_spec__26___boxed(lean_object* v_givenName_3253_, lean_object* v_auxDeclToFullName_3254_, lean_object* v___x_3255_, lean_object* v_givenNameView_3256_, lean_object* v_as_3257_, lean_object* v_i_3258_, lean_object* v_a_3259_){
_start:
{
lean_object* v_res_3260_; 
v_res_3260_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23_spec__26(v_givenName_3253_, v_auxDeclToFullName_3254_, v___x_3255_, v_givenNameView_3256_, v_as_3257_, v_i_3258_, v_a_3259_);
lean_dec_ref(v_as_3257_);
lean_dec(v_auxDeclToFullName_3254_);
lean_dec(v_givenName_3253_);
return v_res_3260_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26_spec__30(lean_object* v_localDecl_x3f_3261_, lean_object* v_givenName_3262_, lean_object* v_as_3263_, lean_object* v_i_3264_, lean_object* v_a_3265_){
_start:
{
lean_object* v___x_3266_; 
v___x_3266_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26_spec__30___redArg(v_localDecl_x3f_3261_, v_givenName_3262_, v_as_3263_, v_i_3264_);
return v___x_3266_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26_spec__30___boxed(lean_object* v_localDecl_x3f_3267_, lean_object* v_givenName_3268_, lean_object* v_as_3269_, lean_object* v_i_3270_, lean_object* v_a_3271_){
_start:
{
lean_object* v_res_3272_; 
v_res_3272_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26_spec__30(v_localDecl_x3f_3267_, v_givenName_3268_, v_as_3269_, v_i_3270_, v_a_3271_);
lean_dec_ref(v_as_3269_);
lean_dec(v_givenName_3268_);
lean_dec(v_localDecl_x3f_3267_);
return v_res_3272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__39(lean_object* v_opt_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_){
_start:
{
lean_object* v___x_3279_; 
v___x_3279_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__39___redArg(v_opt_3273_, v___y_3276_);
return v___x_3279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__39___boxed(lean_object* v_opt_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_){
_start:
{
lean_object* v_res_3286_; 
v_res_3286_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__39(v_opt_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_);
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3283_);
lean_dec(v___y_3282_);
lean_dec_ref(v___y_3281_);
lean_dec_ref(v_opt_3280_);
return v_res_3286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__45(lean_object* v_opt_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_){
_start:
{
lean_object* v___x_3293_; 
v___x_3293_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__45___redArg(v_opt_3287_, v___y_3290_);
return v___x_3293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__45___boxed(lean_object* v_opt_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_){
_start:
{
lean_object* v_res_3300_; 
v_res_3300_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__45(v_opt_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3297_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3295_);
lean_dec_ref(v_opt_3294_);
return v_res_3300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___redArg___lam__0(lean_object* v_declName_3301_, lean_object* v_entry_3302_, lean_object* v_inst_3303_, lean_object* v_inst_3304_, lean_object* v_inst_3305_, lean_object* v_env_3306_){
_start:
{
lean_object* v___x_3307_; lean_object* v___x_3308_; 
v___x_3307_ = l_Lean_Linter_deprecatedAttr;
v___x_3308_ = l_Lean_ParametricAttribute_setParam___redArg(v___x_3307_, v_env_3306_, v_declName_3301_, v_entry_3302_);
if (lean_obj_tag(v___x_3308_) == 0)
{
lean_object* v_a_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3318_; 
lean_dec_ref(v_inst_3305_);
v_a_3309_ = lean_ctor_get(v___x_3308_, 0);
v_isSharedCheck_3318_ = !lean_is_exclusive(v___x_3308_);
if (v_isSharedCheck_3318_ == 0)
{
v___x_3311_ = v___x_3308_;
v_isShared_3312_ = v_isSharedCheck_3318_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_a_3309_);
lean_dec(v___x_3308_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3318_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v___x_3314_; 
if (v_isShared_3312_ == 0)
{
lean_ctor_set_tag(v___x_3311_, 3);
v___x_3314_ = v___x_3311_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v_a_3309_);
v___x_3314_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
lean_object* v___x_3315_; lean_object* v___x_3316_; 
v___x_3315_ = l_Lean_MessageData_ofFormat(v___x_3314_);
v___x_3316_ = l_Lean_throwError___redArg(v_inst_3303_, v_inst_3304_, v___x_3315_);
return v___x_3316_;
}
}
}
else
{
lean_object* v_a_3319_; lean_object* v___x_3320_; 
lean_dec_ref(v_inst_3304_);
lean_dec_ref(v_inst_3303_);
v_a_3319_ = lean_ctor_get(v___x_3308_, 0);
lean_inc(v_a_3319_);
lean_dec_ref_known(v___x_3308_, 1);
v___x_3320_ = l_Lean_setEnv___redArg(v_inst_3305_, v_a_3319_);
return v___x_3320_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___redArg(lean_object* v_inst_3321_, lean_object* v_inst_3322_, lean_object* v_inst_3323_, lean_object* v_declName_3324_, lean_object* v_entry_3325_){
_start:
{
lean_object* v_toBind_3326_; lean_object* v_getEnv_3327_; lean_object* v___f_3328_; lean_object* v___x_3329_; 
v_toBind_3326_ = lean_ctor_get(v_inst_3321_, 1);
lean_inc(v_toBind_3326_);
v_getEnv_3327_ = lean_ctor_get(v_inst_3322_, 0);
lean_inc(v_getEnv_3327_);
v___f_3328_ = lean_alloc_closure((void*)(l_Lean_Linter_setDeprecated___redArg___lam__0), 6, 5);
lean_closure_set(v___f_3328_, 0, v_declName_3324_);
lean_closure_set(v___f_3328_, 1, v_entry_3325_);
lean_closure_set(v___f_3328_, 2, v_inst_3321_);
lean_closure_set(v___f_3328_, 3, v_inst_3323_);
lean_closure_set(v___f_3328_, 4, v_inst_3322_);
v___x_3329_ = lean_apply_4(v_toBind_3326_, lean_box(0), lean_box(0), v_getEnv_3327_, v___f_3328_);
return v___x_3329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated(lean_object* v_m_3330_, lean_object* v_inst_3331_, lean_object* v_inst_3332_, lean_object* v_inst_3333_, lean_object* v_declName_3334_, lean_object* v_entry_3335_){
_start:
{
lean_object* v___x_3336_; 
v___x_3336_ = l_Lean_Linter_setDeprecated___redArg(v_inst_3331_, v_inst_3332_, v_inst_3333_, v_declName_3334_, v_entry_3335_);
return v___x_3336_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_isDeprecated(lean_object* v_env_3337_, lean_object* v_declName_3338_){
_start:
{
lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; 
v___x_3339_ = ((lean_object*)(l_Lean_Linter_instInhabitedDeprecationEntry_default));
v___x_3340_ = l_Lean_Linter_deprecatedAttr;
v___x_3341_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_3339_, v___x_3340_, v_env_3337_, v_declName_3338_);
if (lean_obj_tag(v___x_3341_) == 0)
{
uint8_t v___x_3342_; 
v___x_3342_ = 0;
return v___x_3342_;
}
else
{
uint8_t v___x_3343_; 
lean_dec_ref_known(v___x_3341_, 1);
v___x_3343_ = 1;
return v___x_3343_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_isDeprecated___boxed(lean_object* v_env_3344_, lean_object* v_declName_3345_){
_start:
{
uint8_t v_res_3346_; lean_object* v_r_3347_; 
v_res_3346_ = l_Lean_Linter_isDeprecated(v_env_3344_, v_declName_3345_);
v_r_3347_ = lean_box(v_res_3346_);
return v_r_3347_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_isDeprecationWarning___lam__0(lean_object* v_x_3348_){
_start:
{
lean_object* v___x_3349_; uint8_t v___x_3350_; 
v___x_3349_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_3350_ = lean_name_eq(v_x_3348_, v___x_3349_);
return v___x_3350_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_isDeprecationWarning___lam__0___boxed(lean_object* v_x_3351_){
_start:
{
uint8_t v_res_3352_; lean_object* v_r_3353_; 
v_res_3352_ = l_Lean_MessageData_isDeprecationWarning___lam__0(v_x_3351_);
lean_dec(v_x_3351_);
v_r_3353_ = lean_box(v_res_3352_);
return v_r_3353_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_isDeprecationWarning(lean_object* v_msg_3355_){
_start:
{
lean_object* v___f_3356_; uint8_t v___x_3357_; 
v___f_3356_ = ((lean_object*)(l_Lean_MessageData_isDeprecationWarning___closed__0));
v___x_3357_ = l_Lean_MessageData_hasTag(v___f_3356_, v_msg_3355_);
return v___x_3357_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_isDeprecationWarning___boxed(lean_object* v_msg_3358_){
_start:
{
uint8_t v_res_3359_; lean_object* v_r_3360_; 
v_res_3359_ = l_Lean_MessageData_isDeprecationWarning(v_msg_3358_);
v_r_3360_ = lean_box(v_res_3359_);
return v_r_3360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getDeprecatedNewName(lean_object* v_env_3361_, lean_object* v_declName_3362_){
_start:
{
lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; 
v___x_3363_ = ((lean_object*)(l_Lean_Linter_instInhabitedDeprecationEntry_default));
v___x_3364_ = l_Lean_Linter_deprecatedAttr;
v___x_3365_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_3363_, v___x_3364_, v_env_3361_, v_declName_3362_);
if (lean_obj_tag(v___x_3365_) == 0)
{
lean_object* v___x_3366_; 
v___x_3366_ = lean_box(0);
return v___x_3366_;
}
else
{
lean_object* v_val_3367_; lean_object* v_newName_x3f_3368_; 
v_val_3367_ = lean_ctor_get(v___x_3365_, 0);
lean_inc(v_val_3367_);
lean_dec_ref_known(v___x_3365_, 1);
v_newName_x3f_3368_ = lean_ctor_get(v_val_3367_, 0);
lean_inc(v_newName_x3f_3368_);
lean_dec(v_val_3367_);
return v_newName_x3f_3368_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_DeprecationHint_ctorIdx___impl(lean_object* v_x_3369_){
_start:
{
lean_object* v___x_3370_; 
v___x_3370_ = lean_obj_tag_nat(v_x_3369_);
return v___x_3370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_DeprecationHint_ctorIdx___impl___boxed(lean_object* v_x_3371_){
_start:
{
lean_object* v_res_3372_; 
v_res_3372_ = l_Lean_Linter_DeprecationHint_ctorIdx___impl(v_x_3371_);
lean_dec(v_x_3371_);
return v_res_3372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_DeprecationHint_ctorElim___redArg(lean_object* v_t_3373_, lean_object* v_k_3374_){
_start:
{
if (lean_obj_tag(v_t_3373_) == 2)
{
lean_object* v_mk_3375_; lean_object* v___x_3376_; 
v_mk_3375_ = lean_ctor_get(v_t_3373_, 0);
lean_inc_ref(v_mk_3375_);
lean_dec_ref_known(v_t_3373_, 1);
v___x_3376_ = lean_apply_1(v_k_3374_, v_mk_3375_);
return v___x_3376_;
}
else
{
lean_dec(v_t_3373_);
return v_k_3374_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_DeprecationHint_ctorElim(lean_object* v_motive_3377_, lean_object* v_ctorIdx_3378_, lean_object* v_t_3379_, lean_object* v_h_3380_, lean_object* v_k_3381_){
_start:
{
lean_object* v___x_3382_; 
v___x_3382_ = l_Lean_Linter_DeprecationHint_ctorElim___redArg(v_t_3379_, v_k_3381_);
return v___x_3382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_DeprecationHint_ctorElim___boxed(lean_object* v_motive_3383_, lean_object* v_ctorIdx_3384_, lean_object* v_t_3385_, lean_object* v_h_3386_, lean_object* v_k_3387_){
_start:
{
lean_object* v_res_3388_; 
v_res_3388_ = l_Lean_Linter_DeprecationHint_ctorElim(v_motive_3383_, v_ctorIdx_3384_, v_t_3385_, v_h_3386_, v_k_3387_);
lean_dec(v_ctorIdx_3384_);
return v_res_3388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_DeprecationHint_none_elim___redArg(lean_object* v_t_3389_, lean_object* v_none_3390_){
_start:
{
lean_object* v___x_3391_; 
v___x_3391_ = l_Lean_Linter_DeprecationHint_ctorElim___redArg(v_t_3389_, v_none_3390_);
return v___x_3391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_DeprecationHint_none_elim(lean_object* v_motive_3392_, lean_object* v_t_3393_, lean_object* v_h_3394_, lean_object* v_none_3395_){
_start:
{
lean_object* v___x_3396_; 
v___x_3396_ = l_Lean_Linter_DeprecationHint_ctorElim___redArg(v_t_3393_, v_none_3395_);
return v___x_3396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_DeprecationHint_ident_elim___redArg(lean_object* v_t_3397_, lean_object* v_ident_3398_){
_start:
{
lean_object* v___x_3399_; 
v___x_3399_ = l_Lean_Linter_DeprecationHint_ctorElim___redArg(v_t_3397_, v_ident_3398_);
return v___x_3399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_DeprecationHint_ident_elim(lean_object* v_motive_3400_, lean_object* v_t_3401_, lean_object* v_h_3402_, lean_object* v_ident_3403_){
_start:
{
lean_object* v___x_3404_; 
v___x_3404_ = l_Lean_Linter_DeprecationHint_ctorElim___redArg(v_t_3401_, v_ident_3403_);
return v___x_3404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_DeprecationHint_custom_elim___redArg(lean_object* v_t_3405_, lean_object* v_custom_3406_){
_start:
{
lean_object* v___x_3407_; 
v___x_3407_ = l_Lean_Linter_DeprecationHint_ctorElim___redArg(v_t_3405_, v_custom_3406_);
return v___x_3407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_DeprecationHint_custom_elim(lean_object* v_motive_3408_, lean_object* v_t_3409_, lean_object* v_h_3410_, lean_object* v_custom_3411_){
_start:
{
lean_object* v___x_3412_; 
v___x_3412_ = l_Lean_Linter_DeprecationHint_ctorElim___redArg(v_t_3409_, v_custom_3411_);
return v___x_3412_;
}
}
static lean_object* _init_l_Lean_Linter_mkReplacementHint___redArg___closed__1(void){
_start:
{
lean_object* v___x_3414_; lean_object* v___x_3415_; 
v___x_3414_ = ((lean_object*)(l_Lean_Linter_mkReplacementHint___redArg___closed__0));
v___x_3415_ = l_Lean_stringToMessageData(v___x_3414_);
return v___x_3415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_mkReplacementHint___redArg(lean_object* v_ref_3416_, lean_object* v_replacement_3417_, lean_object* v_a_3418_, lean_object* v_a_3419_){
_start:
{
uint8_t v___x_3421_; lean_object* v___x_3422_; 
v___x_3421_ = 1;
v___x_3422_ = l_Lean_Syntax_getRange_x3f(v_ref_3416_, v___x_3421_);
if (lean_obj_tag(v___x_3422_) == 0)
{
lean_object* v___x_3423_; lean_object* v___x_3424_; 
lean_dec_ref(v_replacement_3417_);
lean_dec(v_ref_3416_);
v___x_3423_ = l_Lean_MessageData_nil;
v___x_3424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3424_, 0, v___x_3423_);
return v___x_3424_;
}
else
{
lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3442_; 
v_isSharedCheck_3442_ = !lean_is_exclusive(v___x_3422_);
if (v_isSharedCheck_3442_ == 0)
{
lean_object* v_unused_3443_; 
v_unused_3443_ = lean_ctor_get(v___x_3422_, 0);
lean_dec(v_unused_3443_);
v___x_3426_ = v___x_3422_;
v_isShared_3427_ = v_isSharedCheck_3442_;
goto v_resetjp_3425_;
}
else
{
lean_dec(v___x_3422_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3442_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; uint8_t v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3438_; 
v___x_3428_ = lean_obj_once(&l_Lean_Linter_mkReplacementHint___redArg___closed__1, &l_Lean_Linter_mkReplacementHint___redArg___closed__1_once, _init_l_Lean_Linter_mkReplacementHint___redArg___closed__1);
v___x_3429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3429_, 0, v_replacement_3417_);
v___x_3430_ = lean_box(0);
v___x_3431_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3431_, 0, v___x_3429_);
lean_ctor_set(v___x_3431_, 1, v___x_3430_);
lean_ctor_set(v___x_3431_, 2, v___x_3430_);
lean_ctor_set(v___x_3431_, 3, v___x_3430_);
lean_ctor_set(v___x_3431_, 4, v___x_3430_);
lean_ctor_set(v___x_3431_, 5, v___x_3430_);
v___x_3432_ = 0;
v___x_3433_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3433_, 0, v___x_3431_);
lean_ctor_set(v___x_3433_, 1, v___x_3430_);
lean_ctor_set(v___x_3433_, 2, v___x_3430_);
lean_ctor_set_uint8(v___x_3433_, sizeof(void*)*3, v___x_3432_);
v___x_3434_ = lean_unsigned_to_nat(1u);
v___x_3435_ = lean_mk_empty_array_with_capacity(v___x_3434_);
v___x_3436_ = lean_array_push(v___x_3435_, v___x_3433_);
if (v_isShared_3427_ == 0)
{
lean_ctor_set(v___x_3426_, 0, v_ref_3416_);
v___x_3438_ = v___x_3426_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v_ref_3416_);
v___x_3438_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
uint8_t v___x_3439_; lean_object* v___x_3440_; 
v___x_3439_ = 0;
v___x_3440_ = l_Lean_MessageData_hint(v___x_3428_, v___x_3436_, v___x_3438_, v___x_3430_, v___x_3439_, v_a_3418_, v_a_3419_);
lean_dec_ref(v___x_3436_);
return v___x_3440_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_mkReplacementHint___redArg___boxed(lean_object* v_ref_3444_, lean_object* v_replacement_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_){
_start:
{
lean_object* v_res_3449_; 
v_res_3449_ = l_Lean_Linter_mkReplacementHint___redArg(v_ref_3444_, v_replacement_3445_, v_a_3446_, v_a_3447_);
lean_dec(v_a_3447_);
lean_dec_ref(v_a_3446_);
return v_res_3449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_mkReplacementHint(lean_object* v_ref_3450_, lean_object* v_replacement_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_){
_start:
{
lean_object* v___x_3457_; 
v___x_3457_ = l_Lean_Linter_mkReplacementHint___redArg(v_ref_3450_, v_replacement_3451_, v_a_3454_, v_a_3455_);
return v___x_3457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_mkReplacementHint___boxed(lean_object* v_ref_3458_, lean_object* v_replacement_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_){
_start:
{
lean_object* v_res_3465_; 
v_res_3465_ = l_Lean_Linter_mkReplacementHint(v_ref_3458_, v_replacement_3459_, v_a_3460_, v_a_3461_, v_a_3462_, v_a_3463_);
lean_dec(v_a_3463_);
lean_dec_ref(v_a_3462_);
lean_dec(v_a_3461_);
lean_dec_ref(v_a_3460_);
return v_res_3465_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00List_beq___at___00Lean_Linter_mkIdentHint_spec__0_spec__0(lean_object* v_x_3466_, lean_object* v_x_3467_){
_start:
{
if (lean_obj_tag(v_x_3466_) == 0)
{
if (lean_obj_tag(v_x_3467_) == 0)
{
uint8_t v___x_3468_; 
v___x_3468_ = 1;
return v___x_3468_;
}
else
{
uint8_t v___x_3469_; 
v___x_3469_ = 0;
return v___x_3469_;
}
}
else
{
if (lean_obj_tag(v_x_3467_) == 0)
{
uint8_t v___x_3470_; 
v___x_3470_ = 0;
return v___x_3470_;
}
else
{
lean_object* v_head_3471_; lean_object* v_tail_3472_; lean_object* v_head_3473_; lean_object* v_tail_3474_; uint8_t v___x_3475_; 
v_head_3471_ = lean_ctor_get(v_x_3466_, 0);
v_tail_3472_ = lean_ctor_get(v_x_3466_, 1);
v_head_3473_ = lean_ctor_get(v_x_3467_, 0);
v_tail_3474_ = lean_ctor_get(v_x_3467_, 1);
v___x_3475_ = lean_string_dec_eq(v_head_3471_, v_head_3473_);
if (v___x_3475_ == 0)
{
return v___x_3475_;
}
else
{
v_x_3466_ = v_tail_3472_;
v_x_3467_ = v_tail_3474_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00List_beq___at___00Lean_Linter_mkIdentHint_spec__0_spec__0___boxed(lean_object* v_x_3477_, lean_object* v_x_3478_){
_start:
{
uint8_t v_res_3479_; lean_object* v_r_3480_; 
v_res_3479_ = l_List_beq___at___00List_beq___at___00Lean_Linter_mkIdentHint_spec__0_spec__0(v_x_3477_, v_x_3478_);
lean_dec(v_x_3478_);
lean_dec(v_x_3477_);
v_r_3480_ = lean_box(v_res_3479_);
return v_r_3480_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Linter_mkIdentHint_spec__0(lean_object* v_x_3481_, lean_object* v_x_3482_){
_start:
{
if (lean_obj_tag(v_x_3481_) == 0)
{
if (lean_obj_tag(v_x_3482_) == 0)
{
uint8_t v___x_3483_; 
v___x_3483_ = 1;
return v___x_3483_;
}
else
{
uint8_t v___x_3484_; 
v___x_3484_ = 0;
return v___x_3484_;
}
}
else
{
if (lean_obj_tag(v_x_3482_) == 0)
{
uint8_t v___x_3485_; 
v___x_3485_ = 0;
return v___x_3485_;
}
else
{
lean_object* v_head_3486_; lean_object* v_head_3487_; lean_object* v_tail_3488_; lean_object* v_tail_3489_; lean_object* v_fst_3490_; lean_object* v_snd_3491_; lean_object* v_fst_3492_; lean_object* v_snd_3493_; uint8_t v___x_3494_; 
v_head_3486_ = lean_ctor_get(v_x_3481_, 0);
v_head_3487_ = lean_ctor_get(v_x_3482_, 0);
v_tail_3488_ = lean_ctor_get(v_x_3481_, 1);
v_tail_3489_ = lean_ctor_get(v_x_3482_, 1);
v_fst_3490_ = lean_ctor_get(v_head_3486_, 0);
v_snd_3491_ = lean_ctor_get(v_head_3486_, 1);
v_fst_3492_ = lean_ctor_get(v_head_3487_, 0);
v_snd_3493_ = lean_ctor_get(v_head_3487_, 1);
v___x_3494_ = lean_name_eq(v_fst_3490_, v_fst_3492_);
if (v___x_3494_ == 0)
{
return v___x_3494_;
}
else
{
uint8_t v___x_3495_; 
v___x_3495_ = l_List_beq___at___00List_beq___at___00Lean_Linter_mkIdentHint_spec__0_spec__0(v_snd_3491_, v_snd_3493_);
if (v___x_3495_ == 0)
{
return v___x_3495_;
}
else
{
v_x_3481_ = v_tail_3488_;
v_x_3482_ = v_tail_3489_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Linter_mkIdentHint_spec__0___boxed(lean_object* v_x_3497_, lean_object* v_x_3498_){
_start:
{
uint8_t v_res_3499_; lean_object* v_r_3500_; 
v_res_3499_ = l_List_beq___at___00Lean_Linter_mkIdentHint_spec__0(v_x_3497_, v_x_3498_);
lean_dec(v_x_3498_);
lean_dec(v_x_3497_);
v_r_3500_ = lean_box(v_res_3499_);
return v_r_3500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_mkIdentHint(lean_object* v_declName_3501_, lean_object* v_newName_3502_, lean_object* v_a_3503_, lean_object* v_a_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_){
_start:
{
lean_object* v_ref_3508_; 
v_ref_3508_ = lean_ctor_get(v_a_3505_, 2);
if (lean_obj_tag(v_ref_3508_) == 3)
{
lean_object* v_val_3509_; uint8_t v___x_3510_; 
v_val_3509_ = lean_ctor_get(v_ref_3508_, 2);
v___x_3510_ = l_Lean_Name_hasMacroScopes(v_val_3509_);
if (v___x_3510_ == 0)
{
uint8_t v___x_3511_; lean_object* v___x_3512_; 
v___x_3511_ = 1;
lean_inc(v_val_3509_);
v___x_3512_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28(v_val_3509_, v___x_3511_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_);
if (lean_obj_tag(v___x_3512_) == 0)
{
lean_object* v_a_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3546_; 
v_a_3513_ = lean_ctor_get(v___x_3512_, 0);
v_isSharedCheck_3546_ = !lean_is_exclusive(v___x_3512_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3515_ = v___x_3512_;
v_isShared_3516_ = v_isSharedCheck_3546_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_a_3513_);
lean_dec(v___x_3512_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3546_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; uint8_t v___x_3520_; 
v___x_3517_ = lean_box(0);
v___x_3518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3518_, 0, v_declName_3501_);
lean_ctor_set(v___x_3518_, 1, v___x_3517_);
v___x_3519_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3519_, 0, v___x_3518_);
lean_ctor_set(v___x_3519_, 1, v___x_3517_);
v___x_3520_ = l_List_beq___at___00Lean_Linter_mkIdentHint_spec__0(v_a_3513_, v___x_3519_);
lean_dec_ref_known(v___x_3519_, 2);
lean_dec(v_a_3513_);
if (v___x_3520_ == 0)
{
lean_object* v___x_3521_; lean_object* v___x_3523_; 
lean_dec(v_newName_3502_);
v___x_3521_ = l_Lean_MessageData_nil;
if (v_isShared_3516_ == 0)
{
lean_ctor_set(v___x_3515_, 0, v___x_3521_);
v___x_3523_ = v___x_3515_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v___x_3521_);
v___x_3523_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
return v___x_3523_;
}
}
else
{
lean_object* v___x_3525_; 
lean_del_object(v___x_3515_);
v___x_3525_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6(v_newName_3502_, v___x_3510_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_);
if (lean_obj_tag(v___x_3525_) == 0)
{
lean_object* v_a_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3537_; 
v_a_3526_ = lean_ctor_get(v___x_3525_, 0);
v_isSharedCheck_3537_ = !lean_is_exclusive(v___x_3525_);
if (v_isSharedCheck_3537_ == 0)
{
v___x_3528_ = v___x_3525_;
v_isShared_3529_ = v_isSharedCheck_3537_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_a_3526_);
lean_dec(v___x_3525_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3537_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
if (lean_obj_tag(v_a_3526_) == 1)
{
lean_object* v_val_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; 
lean_del_object(v___x_3528_);
v_val_3530_ = lean_ctor_get(v_a_3526_, 0);
lean_inc(v_val_3530_);
lean_dec_ref_known(v_a_3526_, 1);
v___x_3531_ = l_Lean_Name_toString(v_val_3530_, v___x_3511_);
lean_inc_ref(v_ref_3508_);
v___x_3532_ = l_Lean_Linter_mkReplacementHint___redArg(v_ref_3508_, v___x_3531_, v_a_3505_, v_a_3506_);
return v___x_3532_;
}
else
{
lean_object* v___x_3533_; lean_object* v___x_3535_; 
lean_dec(v_a_3526_);
v___x_3533_ = l_Lean_MessageData_nil;
if (v_isShared_3529_ == 0)
{
lean_ctor_set(v___x_3528_, 0, v___x_3533_);
v___x_3535_ = v___x_3528_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v___x_3533_);
v___x_3535_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3534_;
}
v_reusejp_3534_:
{
return v___x_3535_;
}
}
}
}
else
{
lean_object* v_a_3538_; lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3545_; 
v_a_3538_ = lean_ctor_get(v___x_3525_, 0);
v_isSharedCheck_3545_ = !lean_is_exclusive(v___x_3525_);
if (v_isSharedCheck_3545_ == 0)
{
v___x_3540_ = v___x_3525_;
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
else
{
lean_inc(v_a_3538_);
lean_dec(v___x_3525_);
v___x_3540_ = lean_box(0);
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
v_resetjp_3539_:
{
lean_object* v___x_3543_; 
if (v_isShared_3541_ == 0)
{
v___x_3543_ = v___x_3540_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v_a_3538_);
v___x_3543_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
return v___x_3543_;
}
}
}
}
}
}
else
{
lean_object* v_a_3547_; lean_object* v___x_3549_; uint8_t v_isShared_3550_; uint8_t v_isSharedCheck_3554_; 
lean_dec(v_newName_3502_);
lean_dec(v_declName_3501_);
v_a_3547_ = lean_ctor_get(v___x_3512_, 0);
v_isSharedCheck_3554_ = !lean_is_exclusive(v___x_3512_);
if (v_isSharedCheck_3554_ == 0)
{
v___x_3549_ = v___x_3512_;
v_isShared_3550_ = v_isSharedCheck_3554_;
goto v_resetjp_3548_;
}
else
{
lean_inc(v_a_3547_);
lean_dec(v___x_3512_);
v___x_3549_ = lean_box(0);
v_isShared_3550_ = v_isSharedCheck_3554_;
goto v_resetjp_3548_;
}
v_resetjp_3548_:
{
lean_object* v___x_3552_; 
if (v_isShared_3550_ == 0)
{
v___x_3552_ = v___x_3549_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v_a_3547_);
v___x_3552_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
return v___x_3552_;
}
}
}
}
else
{
lean_object* v___x_3555_; lean_object* v___x_3556_; 
lean_dec(v_newName_3502_);
lean_dec(v_declName_3501_);
v___x_3555_ = l_Lean_MessageData_nil;
v___x_3556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3556_, 0, v___x_3555_);
return v___x_3556_;
}
}
else
{
lean_object* v___x_3557_; lean_object* v___x_3558_; 
lean_dec(v_newName_3502_);
lean_dec(v_declName_3501_);
v___x_3557_ = l_Lean_MessageData_nil;
v___x_3558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3558_, 0, v___x_3557_);
return v___x_3558_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_mkIdentHint___boxed(lean_object* v_declName_3559_, lean_object* v_newName_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_){
_start:
{
lean_object* v_res_3566_; 
v_res_3566_ = l_Lean_Linter_mkIdentHint(v_declName_3559_, v_newName_3560_, v_a_3561_, v_a_3562_, v_a_3563_, v_a_3564_);
lean_dec(v_a_3564_);
lean_dec_ref(v_a_3563_);
lean_dec(v_a_3562_);
lean_dec_ref(v_a_3561_);
return v_res_3566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(lean_object* v_o_3567_, lean_object* v___y_3568_){
_start:
{
lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v_env_3572_; lean_object* v___x_3573_; lean_object* v_toEnvExtension_3574_; lean_object* v_asyncMode_3575_; lean_object* v___x_3576_; uint8_t v___x_3577_; lean_object* v___x_3578_; lean_object* v_merged_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3587_; 
v___x_3570_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_3571_ = lean_st_ref_get(v___y_3568_);
v_env_3572_ = lean_ctor_get(v___x_3571_, 0);
lean_inc_ref(v_env_3572_);
lean_dec(v___x_3571_);
v___x_3573_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_3574_ = lean_ctor_get(v___x_3573_, 0);
v_asyncMode_3575_ = lean_ctor_get(v_toEnvExtension_3574_, 2);
v___x_3576_ = lean_box(0);
v___x_3577_ = 0;
v___x_3578_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3570_, v___x_3573_, v_env_3572_, v_asyncMode_3575_, v___x_3576_, v___x_3577_);
v_merged_3579_ = lean_ctor_get(v___x_3578_, 0);
v_isSharedCheck_3587_ = !lean_is_exclusive(v___x_3578_);
if (v_isSharedCheck_3587_ == 0)
{
lean_object* v_unused_3588_; 
v_unused_3588_ = lean_ctor_get(v___x_3578_, 1);
lean_dec(v_unused_3588_);
v___x_3581_ = v___x_3578_;
v_isShared_3582_ = v_isSharedCheck_3587_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_merged_3579_);
lean_dec(v___x_3578_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3587_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v___x_3584_; 
if (v_isShared_3582_ == 0)
{
lean_ctor_set(v___x_3581_, 1, v_merged_3579_);
lean_ctor_set(v___x_3581_, 0, v_o_3567_);
v___x_3584_ = v___x_3581_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v_o_3567_);
lean_ctor_set(v_reuseFailAlloc_3586_, 1, v_merged_3579_);
v___x_3584_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
lean_object* v___x_3585_; 
v___x_3585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3585_, 0, v___x_3584_);
return v___x_3585_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg___boxed(lean_object* v_o_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_){
_start:
{
lean_object* v_res_3592_; 
v_res_3592_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(v_o_3589_, v___y_3590_);
lean_dec(v___y_3590_);
return v_res_3592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0(lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_){
_start:
{
lean_object* v___x_3598_; lean_object* v___x_3599_; 
v___x_3598_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3595_);
v___x_3599_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(v___x_3598_, v___y_3596_);
return v___x_3599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0___boxed(lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_){
_start:
{
lean_object* v_res_3605_; 
v_res_3605_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0(v___y_3600_, v___y_3601_, v___y_3602_, v___y_3603_);
lean_dec(v___y_3603_);
lean_dec_ref(v___y_3602_);
lean_dec(v___y_3601_);
lean_dec_ref(v___y_3600_);
return v_res_3605_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__1(void){
_start:
{
lean_object* v___x_3607_; lean_object* v___x_3608_; 
v___x_3607_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__0));
v___x_3608_ = l_Lean_stringToMessageData(v___x_3607_);
return v___x_3608_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__3(void){
_start:
{
lean_object* v___x_3610_; lean_object* v___x_3611_; 
v___x_3610_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__2));
v___x_3611_ = l_Lean_stringToMessageData(v___x_3610_);
return v___x_3611_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__5(void){
_start:
{
lean_object* v___x_3613_; lean_object* v___x_3614_; 
v___x_3613_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__4));
v___x_3614_ = l_Lean_stringToMessageData(v___x_3613_);
return v___x_3614_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__7(void){
_start:
{
lean_object* v___x_3616_; lean_object* v___x_3617_; 
v___x_3616_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__6));
v___x_3617_ = l_Lean_stringToMessageData(v___x_3616_);
return v___x_3617_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__9(void){
_start:
{
lean_object* v___x_3619_; lean_object* v___x_3620_; 
v___x_3619_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__8));
v___x_3620_ = l_Lean_stringToMessageData(v___x_3619_);
return v___x_3620_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__11(void){
_start:
{
lean_object* v___x_3622_; lean_object* v___x_3623_; 
v___x_3622_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__10));
v___x_3623_ = l_Lean_stringToMessageData(v___x_3622_);
return v___x_3623_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__13(void){
_start:
{
lean_object* v___x_3625_; lean_object* v___x_3626_; 
v___x_3625_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__12));
v___x_3626_ = l_Lean_stringToMessageData(v___x_3625_);
return v___x_3626_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__15(void){
_start:
{
lean_object* v___x_3628_; lean_object* v___x_3629_; 
v___x_3628_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__14));
v___x_3629_ = l_Lean_stringToMessageData(v___x_3628_);
return v___x_3629_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__17(void){
_start:
{
lean_object* v___x_3631_; lean_object* v___x_3632_; 
v___x_3631_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__16));
v___x_3632_ = l_Lean_stringToMessageData(v___x_3631_);
return v___x_3632_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__19(void){
_start:
{
lean_object* v___x_3634_; lean_object* v___x_3635_; 
v___x_3634_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__18));
v___x_3635_ = l_Lean_stringToMessageData(v___x_3634_);
return v___x_3635_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__21(void){
_start:
{
lean_object* v___x_3638_; lean_object* v___x_3639_; 
v___x_3638_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__20));
v___x_3639_ = l_Lean_MessageData_ofFormat(v___x_3638_);
return v___x_3639_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__23(void){
_start:
{
lean_object* v___x_3641_; lean_object* v___x_3642_; 
v___x_3641_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__22));
v___x_3642_ = l_Lean_stringToMessageData(v___x_3641_);
return v___x_3642_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__25(void){
_start:
{
lean_object* v___x_3644_; lean_object* v___x_3645_; 
v___x_3644_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__24));
v___x_3645_ = l_Lean_stringToMessageData(v___x_3644_);
return v___x_3645_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__27(void){
_start:
{
lean_object* v___x_3647_; lean_object* v___x_3648_; 
v___x_3647_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__26));
v___x_3648_ = l_Lean_stringToMessageData(v___x_3647_);
return v___x_3648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkDeprecated(lean_object* v_declName_3649_, lean_object* v_hint_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_){
_start:
{
lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v_a_3658_; lean_object* v___x_3660_; uint8_t v_isShared_3661_; uint8_t v_isSharedCheck_3832_; 
v___x_3656_ = ((lean_object*)(l_Lean_Linter_instInhabitedDeprecationEntry_default));
v___x_3657_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0(v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_);
v_a_3658_ = lean_ctor_get(v___x_3657_, 0);
v_isSharedCheck_3832_ = !lean_is_exclusive(v___x_3657_);
if (v_isSharedCheck_3832_ == 0)
{
v___x_3660_ = v___x_3657_;
v_isShared_3661_ = v_isSharedCheck_3832_;
goto v_resetjp_3659_;
}
else
{
lean_inc(v_a_3658_);
lean_dec(v___x_3657_);
v___x_3660_ = lean_box(0);
v_isShared_3661_ = v_isSharedCheck_3832_;
goto v_resetjp_3659_;
}
v_resetjp_3659_:
{
lean_object* v___x_3662_; uint8_t v___x_3663_; lean_object* v_extraMsg_3665_; lean_object* v___y_3666_; lean_object* v___y_3667_; lean_object* v___y_3668_; lean_object* v___y_3669_; 
v___x_3662_ = l_Lean_Linter_linter_deprecated;
v___x_3663_ = l_Lean_Linter_getLinterValue(v___x_3662_, v_a_3658_);
lean_dec(v_a_3658_);
if (v___x_3663_ == 0)
{
lean_object* v___x_3679_; lean_object* v___x_3681_; 
lean_dec(v_hint_3650_);
lean_dec(v_declName_3649_);
v___x_3679_ = lean_box(0);
if (v_isShared_3661_ == 0)
{
lean_ctor_set(v___x_3660_, 0, v___x_3679_);
v___x_3681_ = v___x_3660_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v___x_3679_);
v___x_3681_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
return v___x_3681_;
}
}
else
{
lean_object* v___x_3683_; lean_object* v_env_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; 
v___x_3683_ = lean_st_ref_get(v_a_3654_);
v_env_3684_ = lean_ctor_get(v___x_3683_, 0);
lean_inc_ref(v_env_3684_);
lean_dec(v___x_3683_);
v___x_3685_ = l_Lean_Linter_deprecatedAttr;
lean_inc(v_declName_3649_);
v___x_3686_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_3656_, v___x_3685_, v_env_3684_, v_declName_3649_);
if (lean_obj_tag(v___x_3686_) == 1)
{
lean_object* v_val_3687_; lean_object* v_text_x3f_3688_; 
lean_del_object(v___x_3660_);
v_val_3687_ = lean_ctor_get(v___x_3686_, 0);
lean_inc(v_val_3687_);
lean_dec_ref_known(v___x_3686_, 1);
v_text_x3f_3688_ = lean_ctor_get(v_val_3687_, 1);
if (lean_obj_tag(v_text_x3f_3688_) == 0)
{
lean_object* v_newName_x3f_3689_; 
v_newName_x3f_3689_ = lean_ctor_get(v_val_3687_, 0);
lean_inc(v_newName_x3f_3689_);
lean_dec(v_val_3687_);
if (lean_obj_tag(v_newName_x3f_3689_) == 0)
{
lean_object* v___x_3690_; 
lean_dec(v_hint_3650_);
v___x_3690_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__2_spec__4___closed__9);
v_extraMsg_3665_ = v___x_3690_;
v___y_3666_ = v_a_3651_;
v___y_3667_ = v_a_3652_;
v___y_3668_ = v_a_3653_;
v___y_3669_ = v_a_3654_;
goto v___jp_3664_;
}
else
{
lean_object* v_val_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v_env_3698_; lean_object* v___x_3699_; uint8_t v___x_3700_; lean_object* v___x_3701_; 
v_val_3691_ = lean_ctor_get(v_newName_x3f_3689_, 0);
lean_inc_n(v_val_3691_, 2);
lean_dec_ref_known(v_newName_x3f_3689_, 1);
v___x_3692_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__3, &l_Lean_Linter_checkDeprecated___closed__3_once, _init_l_Lean_Linter_checkDeprecated___closed__3);
v___x_3693_ = l_Lean_MessageData_ofConstName(v_val_3691_, v___x_3663_);
lean_inc_ref(v___x_3693_);
v___x_3694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3694_, 0, v___x_3692_);
lean_ctor_set(v___x_3694_, 1, v___x_3693_);
v___x_3695_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__55_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__55_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__55_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_3696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3696_, 0, v___x_3694_);
lean_ctor_set(v___x_3696_, 1, v___x_3695_);
v___x_3697_ = lean_st_ref_get(v_a_3654_);
v_env_3698_ = lean_ctor_get(v___x_3697_, 0);
lean_inc_ref_n(v_env_3698_, 2);
lean_dec(v___x_3697_);
v___x_3699_ = l_Lean_Name_getPrefix(v_declName_3649_);
v___x_3700_ = 0;
lean_inc(v_declName_3649_);
v___x_3701_ = l_Lean_Environment_findConstVal_x3f(v_env_3698_, v_declName_3649_, v___x_3700_);
if (lean_obj_tag(v___x_3701_) == 1)
{
lean_object* v_val_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; 
v_val_3702_ = lean_ctor_get(v___x_3701_, 0);
lean_inc(v_val_3702_);
lean_dec_ref_known(v___x_3701_, 1);
v___x_3703_ = l_Lean_Name_getPrefix(v_val_3691_);
lean_inc(v_val_3691_);
lean_inc_ref(v_env_3698_);
v___x_3704_ = l_Lean_Environment_findConstVal_x3f(v_env_3698_, v_val_3691_, v___x_3700_);
if (lean_obj_tag(v___x_3704_) == 1)
{
lean_object* v_val_3705_; lean_object* v___x_3706_; 
v_val_3705_ = lean_ctor_get(v___x_3704_, 0);
lean_inc(v_val_3705_);
lean_dec_ref_known(v___x_3704_, 1);
v___x_3706_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq(v_val_3702_, v_val_3705_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_);
if (lean_obj_tag(v___x_3706_) == 0)
{
lean_object* v_a_3707_; lean_object* v_msg_3709_; lean_object* v___y_3710_; lean_object* v___y_3711_; lean_object* v___y_3712_; lean_object* v___y_3713_; lean_object* v___y_3739_; lean_object* v___y_3740_; lean_object* v___y_3741_; lean_object* v___y_3742_; lean_object* v___y_3743_; lean_object* v___y_3744_; lean_object* v___y_3759_; lean_object* v___y_3760_; lean_object* v___y_3761_; lean_object* v___y_3762_; lean_object* v___y_3763_; lean_object* v___y_3764_; lean_object* v_msg_3772_; lean_object* v___y_3773_; lean_object* v___y_3774_; lean_object* v___y_3775_; lean_object* v___y_3776_; uint8_t v___x_3804_; 
v_a_3707_ = lean_ctor_get(v___x_3706_, 0);
lean_inc(v_a_3707_);
lean_dec_ref_known(v___x_3706_, 1);
v___x_3804_ = lean_unbox(v_a_3707_);
if (v___x_3804_ == 0)
{
lean_object* v_type_3805_; lean_object* v_type_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; 
v_type_3805_ = lean_ctor_get(v_val_3705_, 2);
lean_inc_ref(v_type_3805_);
lean_dec(v_val_3705_);
v_type_3806_ = lean_ctor_get(v_val_3702_, 2);
lean_inc_ref(v_type_3806_);
lean_dec(v_val_3702_);
v___x_3807_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_3808_ = l_Lean_indentExpr(v_type_3805_);
v___x_3809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3809_, 0, v___x_3807_);
lean_ctor_set(v___x_3809_, 1, v___x_3808_);
v___x_3810_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_3811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3811_, 0, v___x_3809_);
lean_ctor_set(v___x_3811_, 1, v___x_3810_);
v___x_3812_ = l_Lean_indentExpr(v_type_3806_);
v___x_3813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3813_, 0, v___x_3811_);
lean_ctor_set(v___x_3813_, 1, v___x_3812_);
v___x_3814_ = l_Lean_MessageData_note(v___x_3813_);
v___x_3815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3815_, 0, v___x_3696_);
lean_ctor_set(v___x_3815_, 1, v___x_3814_);
v_msg_3772_ = v___x_3815_;
v___y_3773_ = v_a_3651_;
v___y_3774_ = v_a_3652_;
v___y_3775_ = v_a_3653_;
v___y_3776_ = v_a_3654_;
goto v___jp_3771_;
}
else
{
lean_dec(v_val_3705_);
lean_dec(v_val_3702_);
v_msg_3772_ = v___x_3696_;
v___y_3773_ = v_a_3651_;
v___y_3774_ = v_a_3652_;
v___y_3775_ = v_a_3653_;
v___y_3776_ = v_a_3654_;
goto v___jp_3771_;
}
v___jp_3708_:
{
uint8_t v___x_3714_; 
v___x_3714_ = lean_unbox(v_a_3707_);
lean_dec(v_a_3707_);
if (v___x_3714_ == 0)
{
lean_dec(v_val_3691_);
lean_dec(v_hint_3650_);
v_extraMsg_3665_ = v_msg_3709_;
v___y_3666_ = v___y_3710_;
v___y_3667_ = v___y_3711_;
v___y_3668_ = v___y_3712_;
v___y_3669_ = v___y_3713_;
goto v___jp_3664_;
}
else
{
switch(lean_obj_tag(v_hint_3650_))
{
case 0:
{
lean_dec(v_val_3691_);
v_extraMsg_3665_ = v_msg_3709_;
v___y_3666_ = v___y_3710_;
v___y_3667_ = v___y_3711_;
v___y_3668_ = v___y_3712_;
v___y_3669_ = v___y_3713_;
goto v___jp_3664_;
}
case 1:
{
lean_object* v___x_3715_; 
lean_inc(v_declName_3649_);
v___x_3715_ = l_Lean_Linter_mkIdentHint(v_declName_3649_, v_val_3691_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_);
if (lean_obj_tag(v___x_3715_) == 0)
{
lean_object* v_a_3716_; lean_object* v___x_3717_; 
v_a_3716_ = lean_ctor_get(v___x_3715_, 0);
lean_inc(v_a_3716_);
lean_dec_ref_known(v___x_3715_, 1);
v___x_3717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3717_, 0, v_msg_3709_);
lean_ctor_set(v___x_3717_, 1, v_a_3716_);
v_extraMsg_3665_ = v___x_3717_;
v___y_3666_ = v___y_3710_;
v___y_3667_ = v___y_3711_;
v___y_3668_ = v___y_3712_;
v___y_3669_ = v___y_3713_;
goto v___jp_3664_;
}
else
{
lean_object* v_a_3718_; lean_object* v___x_3720_; uint8_t v_isShared_3721_; uint8_t v_isSharedCheck_3725_; 
lean_dec_ref(v_msg_3709_);
lean_dec(v_declName_3649_);
v_a_3718_ = lean_ctor_get(v___x_3715_, 0);
v_isSharedCheck_3725_ = !lean_is_exclusive(v___x_3715_);
if (v_isSharedCheck_3725_ == 0)
{
v___x_3720_ = v___x_3715_;
v_isShared_3721_ = v_isSharedCheck_3725_;
goto v_resetjp_3719_;
}
else
{
lean_inc(v_a_3718_);
lean_dec(v___x_3715_);
v___x_3720_ = lean_box(0);
v_isShared_3721_ = v_isSharedCheck_3725_;
goto v_resetjp_3719_;
}
v_resetjp_3719_:
{
lean_object* v___x_3723_; 
if (v_isShared_3721_ == 0)
{
v___x_3723_ = v___x_3720_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v_a_3718_);
v___x_3723_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
return v___x_3723_;
}
}
}
}
default: 
{
lean_object* v_mk_3726_; lean_object* v___x_3727_; 
v_mk_3726_ = lean_ctor_get(v_hint_3650_, 0);
lean_inc_ref(v_mk_3726_);
lean_dec_ref_known(v_hint_3650_, 1);
lean_inc(v___y_3713_);
lean_inc_ref(v___y_3712_);
lean_inc(v___y_3711_);
lean_inc_ref(v___y_3710_);
v___x_3727_ = lean_apply_6(v_mk_3726_, v_val_3691_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_, lean_box(0));
if (lean_obj_tag(v___x_3727_) == 0)
{
lean_object* v_a_3728_; lean_object* v___x_3729_; 
v_a_3728_ = lean_ctor_get(v___x_3727_, 0);
lean_inc(v_a_3728_);
lean_dec_ref_known(v___x_3727_, 1);
v___x_3729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3729_, 0, v_msg_3709_);
lean_ctor_set(v___x_3729_, 1, v_a_3728_);
v_extraMsg_3665_ = v___x_3729_;
v___y_3666_ = v___y_3710_;
v___y_3667_ = v___y_3711_;
v___y_3668_ = v___y_3712_;
v___y_3669_ = v___y_3713_;
goto v___jp_3664_;
}
else
{
lean_object* v_a_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3737_; 
lean_dec_ref(v_msg_3709_);
lean_dec(v_declName_3649_);
v_a_3730_ = lean_ctor_get(v___x_3727_, 0);
v_isSharedCheck_3737_ = !lean_is_exclusive(v___x_3727_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3732_ = v___x_3727_;
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_a_3730_);
lean_dec(v___x_3727_);
v___x_3732_ = lean_box(0);
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
v_resetjp_3731_:
{
lean_object* v___x_3735_; 
if (v_isShared_3733_ == 0)
{
v___x_3735_ = v___x_3732_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_a_3730_);
v___x_3735_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
return v___x_3735_;
}
}
}
}
}
}
}
v___jp_3738_:
{
lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; 
v___x_3745_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_3746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3746_, 0, v___x_3745_);
lean_ctor_set(v___x_3746_, 1, v___x_3693_);
v___x_3747_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__5, &l_Lean_Linter_checkDeprecated___closed__5_once, _init_l_Lean_Linter_checkDeprecated___closed__5);
v___x_3748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3748_, 0, v___x_3746_);
lean_ctor_set(v___x_3748_, 1, v___x_3747_);
v___x_3749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3749_, 0, v___x_3748_);
lean_ctor_set(v___x_3749_, 1, v___y_3744_);
v___x_3750_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__7, &l_Lean_Linter_checkDeprecated___closed__7_once, _init_l_Lean_Linter_checkDeprecated___closed__7);
v___x_3751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3751_, 0, v___x_3749_);
lean_ctor_set(v___x_3751_, 1, v___x_3750_);
v___x_3752_ = l_Lean_MessageData_ofName(v___x_3703_);
v___x_3753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3753_, 0, v___x_3751_);
lean_ctor_set(v___x_3753_, 1, v___x_3752_);
v___x_3754_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__9, &l_Lean_Linter_checkDeprecated___closed__9_once, _init_l_Lean_Linter_checkDeprecated___closed__9);
v___x_3755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3755_, 0, v___x_3753_);
lean_ctor_set(v___x_3755_, 1, v___x_3754_);
v___x_3756_ = l_Lean_MessageData_note(v___x_3755_);
v___x_3757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3757_, 0, v___y_3743_);
lean_ctor_set(v___x_3757_, 1, v___x_3756_);
v_msg_3709_ = v___x_3757_;
v___y_3710_ = v___y_3742_;
v___y_3711_ = v___y_3740_;
v___y_3712_ = v___y_3739_;
v___y_3713_ = v___y_3741_;
goto v___jp_3708_;
}
v___jp_3758_:
{
lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; 
v___x_3765_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__11, &l_Lean_Linter_checkDeprecated___closed__11_once, _init_l_Lean_Linter_checkDeprecated___closed__11);
v___x_3766_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3766_, 0, v___x_3765_);
lean_ctor_set(v___x_3766_, 1, v___y_3764_);
v___x_3767_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__13, &l_Lean_Linter_checkDeprecated___closed__13_once, _init_l_Lean_Linter_checkDeprecated___closed__13);
v___x_3768_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3768_, 0, v___x_3766_);
lean_ctor_set(v___x_3768_, 1, v___x_3767_);
v___x_3769_ = l_Lean_MessageData_note(v___x_3768_);
v___x_3770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3770_, 0, v___y_3763_);
lean_ctor_set(v___x_3770_, 1, v___x_3769_);
v_msg_3709_ = v___x_3770_;
v___y_3710_ = v___y_3762_;
v___y_3711_ = v___y_3760_;
v___y_3712_ = v___y_3759_;
v___y_3713_ = v___y_3761_;
goto v___jp_3708_;
}
v___jp_3771_:
{
uint8_t v___x_3777_; 
v___x_3777_ = l_Lean_Name_isAnonymous(v___x_3699_);
if (v___x_3777_ == 0)
{
uint8_t v___x_3778_; 
v___x_3778_ = lean_name_eq(v___x_3699_, v___x_3703_);
lean_dec(v___x_3699_);
if (v___x_3778_ == 0)
{
lean_dec(v___x_3703_);
lean_dec_ref(v_env_3698_);
lean_dec_ref(v___x_3693_);
if (lean_obj_tag(v_declName_3649_) == 1)
{
lean_object* v_str_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; 
v_str_3779_ = lean_ctor_get(v_declName_3649_, 1);
v___x_3780_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__15, &l_Lean_Linter_checkDeprecated___closed__15_once, _init_l_Lean_Linter_checkDeprecated___closed__15);
lean_inc_ref(v_str_3779_);
v___x_3781_ = l_Lean_stringToMessageData(v_str_3779_);
v___x_3782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3782_, 0, v___x_3780_);
lean_ctor_set(v___x_3782_, 1, v___x_3781_);
v___x_3783_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__17, &l_Lean_Linter_checkDeprecated___closed__17_once, _init_l_Lean_Linter_checkDeprecated___closed__17);
v___x_3784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3784_, 0, v___x_3782_);
lean_ctor_set(v___x_3784_, 1, v___x_3783_);
lean_inc(v_val_3691_);
v___x_3785_ = l_Lean_MessageData_ofConstName(v_val_3691_, v___x_3777_);
v___x_3786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3786_, 0, v___x_3784_);
lean_ctor_set(v___x_3786_, 1, v___x_3785_);
v___x_3787_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__19, &l_Lean_Linter_checkDeprecated___closed__19_once, _init_l_Lean_Linter_checkDeprecated___closed__19);
v___x_3788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3788_, 0, v___x_3786_);
lean_ctor_set(v___x_3788_, 1, v___x_3787_);
v___y_3759_ = v___y_3775_;
v___y_3760_ = v___y_3774_;
v___y_3761_ = v___y_3776_;
v___y_3762_ = v___y_3773_;
v___y_3763_ = v_msg_3772_;
v___y_3764_ = v___x_3788_;
goto v___jp_3758_;
}
else
{
lean_object* v___x_3789_; 
v___x_3789_ = l_Lean_MessageData_nil;
v___y_3759_ = v___y_3775_;
v___y_3760_ = v___y_3774_;
v___y_3761_ = v___y_3776_;
v___y_3762_ = v___y_3773_;
v___y_3763_ = v_msg_3772_;
v___y_3764_ = v___x_3789_;
goto v___jp_3758_;
}
}
else
{
uint8_t v___x_3790_; 
lean_inc(v_declName_3649_);
lean_inc_ref(v_env_3698_);
v___x_3790_ = l_Lean_isProtected(v_env_3698_, v_declName_3649_);
if (v___x_3790_ == 0)
{
uint8_t v___x_3791_; 
lean_inc(v_val_3691_);
v___x_3791_ = l_Lean_isProtected(v_env_3698_, v_val_3691_);
if (v___x_3791_ == 0)
{
lean_dec(v___x_3703_);
lean_dec_ref(v___x_3693_);
v_msg_3709_ = v_msg_3772_;
v___y_3710_ = v___y_3773_;
v___y_3711_ = v___y_3774_;
v___y_3712_ = v___y_3775_;
v___y_3713_ = v___y_3776_;
goto v___jp_3708_;
}
else
{
lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; uint8_t v___x_3795_; 
lean_inc(v___x_3703_);
v___x_3792_ = l_Lean_Name_componentsRev(v___x_3703_);
v___x_3793_ = lean_unsigned_to_nat(1u);
v___x_3794_ = l_List_lengthTR___redArg(v___x_3792_);
v___x_3795_ = lean_nat_dec_lt(v___x_3793_, v___x_3794_);
lean_dec(v___x_3794_);
if (v___x_3795_ == 0)
{
lean_object* v___x_3796_; 
lean_dec(v___x_3792_);
v___x_3796_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__21, &l_Lean_Linter_checkDeprecated___closed__21_once, _init_l_Lean_Linter_checkDeprecated___closed__21);
v___y_3739_ = v___y_3775_;
v___y_3740_ = v___y_3774_;
v___y_3741_ = v___y_3776_;
v___y_3742_ = v___y_3773_;
v___y_3743_ = v_msg_3772_;
v___y_3744_ = v___x_3796_;
goto v___jp_3738_;
}
else
{
lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; 
v___x_3797_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__23, &l_Lean_Linter_checkDeprecated___closed__23_once, _init_l_Lean_Linter_checkDeprecated___closed__23);
v___x_3798_ = lean_unsigned_to_nat(0u);
v___x_3799_ = l_List_get___redArg(v___x_3792_, v___x_3798_);
lean_dec(v___x_3792_);
v___x_3800_ = l_Lean_MessageData_ofName(v___x_3799_);
v___x_3801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3801_, 0, v___x_3797_);
lean_ctor_set(v___x_3801_, 1, v___x_3800_);
v___x_3802_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__25, &l_Lean_Linter_checkDeprecated___closed__25_once, _init_l_Lean_Linter_checkDeprecated___closed__25);
v___x_3803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3803_, 0, v___x_3801_);
lean_ctor_set(v___x_3803_, 1, v___x_3802_);
v___y_3739_ = v___y_3775_;
v___y_3740_ = v___y_3774_;
v___y_3741_ = v___y_3776_;
v___y_3742_ = v___y_3773_;
v___y_3743_ = v_msg_3772_;
v___y_3744_ = v___x_3803_;
goto v___jp_3738_;
}
}
}
else
{
lean_dec(v___x_3703_);
lean_dec_ref(v_env_3698_);
lean_dec_ref(v___x_3693_);
v_msg_3709_ = v_msg_3772_;
v___y_3710_ = v___y_3773_;
v___y_3711_ = v___y_3774_;
v___y_3712_ = v___y_3775_;
v___y_3713_ = v___y_3776_;
goto v___jp_3708_;
}
}
}
else
{
lean_dec(v___x_3703_);
lean_dec(v___x_3699_);
lean_dec_ref(v_env_3698_);
lean_dec_ref(v___x_3693_);
v_msg_3709_ = v_msg_3772_;
v___y_3710_ = v___y_3773_;
v___y_3711_ = v___y_3774_;
v___y_3712_ = v___y_3775_;
v___y_3713_ = v___y_3776_;
goto v___jp_3708_;
}
}
}
else
{
lean_object* v_a_3816_; lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3823_; 
lean_dec(v_val_3705_);
lean_dec(v___x_3703_);
lean_dec(v_val_3702_);
lean_dec(v___x_3699_);
lean_dec_ref(v_env_3698_);
lean_dec_ref_known(v___x_3696_, 2);
lean_dec_ref(v___x_3693_);
lean_dec(v_val_3691_);
lean_dec(v_hint_3650_);
lean_dec(v_declName_3649_);
v_a_3816_ = lean_ctor_get(v___x_3706_, 0);
v_isSharedCheck_3823_ = !lean_is_exclusive(v___x_3706_);
if (v_isSharedCheck_3823_ == 0)
{
v___x_3818_ = v___x_3706_;
v_isShared_3819_ = v_isSharedCheck_3823_;
goto v_resetjp_3817_;
}
else
{
lean_inc(v_a_3816_);
lean_dec(v___x_3706_);
v___x_3818_ = lean_box(0);
v_isShared_3819_ = v_isSharedCheck_3823_;
goto v_resetjp_3817_;
}
v_resetjp_3817_:
{
lean_object* v___x_3821_; 
if (v_isShared_3819_ == 0)
{
v___x_3821_ = v___x_3818_;
goto v_reusejp_3820_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v_a_3816_);
v___x_3821_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3820_;
}
v_reusejp_3820_:
{
return v___x_3821_;
}
}
}
}
else
{
lean_dec(v___x_3704_);
lean_dec(v___x_3703_);
lean_dec(v_val_3702_);
lean_dec(v___x_3699_);
lean_dec_ref(v_env_3698_);
lean_dec_ref(v___x_3693_);
lean_dec(v_val_3691_);
lean_dec(v_hint_3650_);
v_extraMsg_3665_ = v___x_3696_;
v___y_3666_ = v_a_3651_;
v___y_3667_ = v_a_3652_;
v___y_3668_ = v_a_3653_;
v___y_3669_ = v_a_3654_;
goto v___jp_3664_;
}
}
else
{
lean_dec(v___x_3701_);
lean_dec(v___x_3699_);
lean_dec_ref(v_env_3698_);
lean_dec_ref(v___x_3693_);
lean_dec(v_val_3691_);
lean_dec(v_hint_3650_);
v_extraMsg_3665_ = v___x_3696_;
v___y_3666_ = v_a_3651_;
v___y_3667_ = v_a_3652_;
v___y_3668_ = v_a_3653_;
v___y_3669_ = v_a_3654_;
goto v___jp_3664_;
}
}
}
else
{
lean_object* v_val_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; 
lean_inc_ref(v_text_x3f_3688_);
lean_dec(v_val_3687_);
lean_dec(v_hint_3650_);
v_val_3824_ = lean_ctor_get(v_text_x3f_3688_, 0);
lean_inc(v_val_3824_);
lean_dec_ref_known(v_text_x3f_3688_, 1);
v___x_3825_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__27, &l_Lean_Linter_checkDeprecated___closed__27_once, _init_l_Lean_Linter_checkDeprecated___closed__27);
v___x_3826_ = l_Lean_stringToMessageData(v_val_3824_);
v___x_3827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3827_, 0, v___x_3825_);
lean_ctor_set(v___x_3827_, 1, v___x_3826_);
v_extraMsg_3665_ = v___x_3827_;
v___y_3666_ = v_a_3651_;
v___y_3667_ = v_a_3652_;
v___y_3668_ = v_a_3653_;
v___y_3669_ = v_a_3654_;
goto v___jp_3664_;
}
}
else
{
lean_object* v___x_3828_; lean_object* v___x_3830_; 
lean_dec(v___x_3686_);
lean_dec(v_hint_3650_);
lean_dec(v_declName_3649_);
v___x_3828_ = lean_box(0);
if (v_isShared_3661_ == 0)
{
lean_ctor_set(v___x_3660_, 0, v___x_3828_);
v___x_3830_ = v___x_3660_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v___x_3828_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
return v___x_3830_;
}
}
}
v___jp_3664_:
{
lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; 
v___x_3670_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_3671_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_3672_ = l_Lean_MessageData_ofConstName(v_declName_3649_, v___x_3663_);
v___x_3673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3673_, 0, v___x_3671_);
lean_ctor_set(v___x_3673_, 1, v___x_3672_);
v___x_3674_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__1, &l_Lean_Linter_checkDeprecated___closed__1_once, _init_l_Lean_Linter_checkDeprecated___closed__1);
v___x_3675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3675_, 0, v___x_3673_);
lean_ctor_set(v___x_3675_, 1, v___x_3674_);
v___x_3676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3676_, 0, v___x_3675_);
lean_ctor_set(v___x_3676_, 1, v_extraMsg_3665_);
v___x_3677_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3677_, 0, v___x_3670_);
lean_ctor_set(v___x_3677_, 1, v___x_3676_);
v___x_3678_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40(v___x_3677_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_);
return v___x_3678_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkDeprecated___boxed(lean_object* v_declName_3833_, lean_object* v_hint_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_){
_start:
{
lean_object* v_res_3840_; 
v_res_3840_ = l_Lean_Linter_checkDeprecated(v_declName_3833_, v_hint_3834_, v_a_3835_, v_a_3836_, v_a_3837_, v_a_3838_);
lean_dec(v_a_3838_);
lean_dec_ref(v_a_3837_);
lean_dec(v_a_3836_);
lean_dec_ref(v_a_3835_);
return v_res_3840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0(lean_object* v_o_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_){
_start:
{
lean_object* v___x_3847_; 
v___x_3847_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(v_o_3841_, v___y_3845_);
return v___x_3847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___boxed(lean_object* v_o_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_){
_start:
{
lean_object* v_res_3854_; 
v_res_3854_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0(v_o_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_);
lean_dec(v___y_3852_);
lean_dec_ref(v___y_3851_);
lean_dec(v___y_3850_);
lean_dec_ref(v___y_3849_);
return v_res_3854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkDeprecatedAt(lean_object* v_ref_3855_, lean_object* v_declName_3856_, lean_object* v_hint_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_){
_start:
{
lean_object* v_toCold_3863_; lean_object* v_currRecDepth_3864_; lean_object* v_ref_3865_; uint16_t v_optionFlags_3866_; uint8_t v_suppressElabErrors_3867_; uint8_t v_checkDeprecated_3868_; uint8_t v_isRecordingDeps_3869_; lean_object* v_ref_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; 
v_toCold_3863_ = lean_ctor_get(v_a_3860_, 0);
v_currRecDepth_3864_ = lean_ctor_get(v_a_3860_, 1);
v_ref_3865_ = lean_ctor_get(v_a_3860_, 2);
v_optionFlags_3866_ = lean_ctor_get_uint16(v_a_3860_, sizeof(void*)*3);
v_suppressElabErrors_3867_ = lean_ctor_get_uint8(v_a_3860_, sizeof(void*)*3 + 2);
v_checkDeprecated_3868_ = lean_ctor_get_uint8(v_a_3860_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3869_ = lean_ctor_get_uint8(v_a_3860_, sizeof(void*)*3 + 4);
v_ref_3870_ = l_Lean_replaceRef(v_ref_3855_, v_ref_3865_);
lean_inc(v_currRecDepth_3864_);
lean_inc_ref(v_toCold_3863_);
v___x_3871_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3871_, 0, v_toCold_3863_);
lean_ctor_set(v___x_3871_, 1, v_currRecDepth_3864_);
lean_ctor_set(v___x_3871_, 2, v_ref_3870_);
lean_ctor_set_uint16(v___x_3871_, sizeof(void*)*3, v_optionFlags_3866_);
lean_ctor_set_uint8(v___x_3871_, sizeof(void*)*3 + 2, v_suppressElabErrors_3867_);
lean_ctor_set_uint8(v___x_3871_, sizeof(void*)*3 + 3, v_checkDeprecated_3868_);
lean_ctor_set_uint8(v___x_3871_, sizeof(void*)*3 + 4, v_isRecordingDeps_3869_);
v___x_3872_ = l_Lean_Core_shouldCheckDeprecated___redArg(v_ref_3855_, v___x_3871_);
if (lean_obj_tag(v___x_3872_) == 0)
{
lean_object* v_a_3873_; lean_object* v___x_3875_; uint8_t v_isShared_3876_; uint8_t v_isSharedCheck_3883_; 
v_a_3873_ = lean_ctor_get(v___x_3872_, 0);
v_isSharedCheck_3883_ = !lean_is_exclusive(v___x_3872_);
if (v_isSharedCheck_3883_ == 0)
{
v___x_3875_ = v___x_3872_;
v_isShared_3876_ = v_isSharedCheck_3883_;
goto v_resetjp_3874_;
}
else
{
lean_inc(v_a_3873_);
lean_dec(v___x_3872_);
v___x_3875_ = lean_box(0);
v_isShared_3876_ = v_isSharedCheck_3883_;
goto v_resetjp_3874_;
}
v_resetjp_3874_:
{
uint8_t v___x_3877_; 
v___x_3877_ = lean_unbox(v_a_3873_);
lean_dec(v_a_3873_);
if (v___x_3877_ == 0)
{
lean_object* v___x_3878_; lean_object* v___x_3880_; 
lean_dec_ref_known(v___x_3871_, 3);
lean_dec(v_hint_3857_);
lean_dec(v_declName_3856_);
v___x_3878_ = lean_box(0);
if (v_isShared_3876_ == 0)
{
lean_ctor_set(v___x_3875_, 0, v___x_3878_);
v___x_3880_ = v___x_3875_;
goto v_reusejp_3879_;
}
else
{
lean_object* v_reuseFailAlloc_3881_; 
v_reuseFailAlloc_3881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3881_, 0, v___x_3878_);
v___x_3880_ = v_reuseFailAlloc_3881_;
goto v_reusejp_3879_;
}
v_reusejp_3879_:
{
return v___x_3880_;
}
}
else
{
lean_object* v___x_3882_; 
lean_del_object(v___x_3875_);
v___x_3882_ = l_Lean_Linter_checkDeprecated(v_declName_3856_, v_hint_3857_, v_a_3858_, v_a_3859_, v___x_3871_, v_a_3861_);
lean_dec_ref_known(v___x_3871_, 3);
return v___x_3882_;
}
}
}
else
{
lean_object* v_a_3884_; lean_object* v___x_3886_; uint8_t v_isShared_3887_; uint8_t v_isSharedCheck_3891_; 
lean_dec_ref_known(v___x_3871_, 3);
lean_dec(v_hint_3857_);
lean_dec(v_declName_3856_);
v_a_3884_ = lean_ctor_get(v___x_3872_, 0);
v_isSharedCheck_3891_ = !lean_is_exclusive(v___x_3872_);
if (v_isSharedCheck_3891_ == 0)
{
v___x_3886_ = v___x_3872_;
v_isShared_3887_ = v_isSharedCheck_3891_;
goto v_resetjp_3885_;
}
else
{
lean_inc(v_a_3884_);
lean_dec(v___x_3872_);
v___x_3886_ = lean_box(0);
v_isShared_3887_ = v_isSharedCheck_3891_;
goto v_resetjp_3885_;
}
v_resetjp_3885_:
{
lean_object* v___x_3889_; 
if (v_isShared_3887_ == 0)
{
v___x_3889_ = v___x_3886_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v_a_3884_);
v___x_3889_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
return v___x_3889_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkDeprecatedAt___boxed(lean_object* v_ref_3892_, lean_object* v_declName_3893_, lean_object* v_hint_3894_, lean_object* v_a_3895_, lean_object* v_a_3896_, lean_object* v_a_3897_, lean_object* v_a_3898_, lean_object* v_a_3899_){
_start:
{
lean_object* v_res_3900_; 
v_res_3900_ = l_Lean_Linter_checkDeprecatedAt(v_ref_3892_, v_declName_3893_, v_hint_3894_, v_a_3895_, v_a_3896_, v_a_3897_, v_a_3898_);
lean_dec(v_a_3898_);
lean_dec_ref(v_a_3897_);
lean_dec(v_a_3896_);
lean_dec_ref(v_a_3895_);
lean_dec(v_ref_3892_);
return v_res_3900_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_mkListRemovalSuggestion_spec__0(size_t v_sz_3901_, size_t v_i_3902_, lean_object* v_bs_3903_){
_start:
{
uint8_t v___x_3904_; 
v___x_3904_ = lean_usize_dec_lt(v_i_3902_, v_sz_3901_);
if (v___x_3904_ == 0)
{
lean_object* v___x_3905_; 
v___x_3905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3905_, 0, v_bs_3903_);
return v___x_3905_;
}
else
{
lean_object* v_v_3906_; lean_object* v___x_3907_; 
v_v_3906_ = lean_array_uget_borrowed(v_bs_3903_, v_i_3902_);
v___x_3907_ = l_Lean_Syntax_getRange_x3f(v_v_3906_, v___x_3904_);
if (lean_obj_tag(v___x_3907_) == 0)
{
lean_object* v___x_3908_; 
lean_dec_ref(v_bs_3903_);
v___x_3908_ = lean_box(0);
return v___x_3908_;
}
else
{
lean_object* v_val_3909_; lean_object* v___x_3910_; lean_object* v_bs_x27_3911_; size_t v___x_3912_; size_t v___x_3913_; lean_object* v___x_3914_; 
v_val_3909_ = lean_ctor_get(v___x_3907_, 0);
lean_inc(v_val_3909_);
lean_dec_ref_known(v___x_3907_, 1);
v___x_3910_ = lean_unsigned_to_nat(0u);
v_bs_x27_3911_ = lean_array_uset(v_bs_3903_, v_i_3902_, v___x_3910_);
v___x_3912_ = ((size_t)1ULL);
v___x_3913_ = lean_usize_add(v_i_3902_, v___x_3912_);
v___x_3914_ = lean_array_uset(v_bs_x27_3911_, v_i_3902_, v_val_3909_);
v_i_3902_ = v___x_3913_;
v_bs_3903_ = v___x_3914_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_mkListRemovalSuggestion_spec__0___boxed(lean_object* v_sz_3916_, lean_object* v_i_3917_, lean_object* v_bs_3918_){
_start:
{
size_t v_sz_boxed_3919_; size_t v_i_boxed_3920_; lean_object* v_res_3921_; 
v_sz_boxed_3919_ = lean_unbox_usize(v_sz_3916_);
lean_dec(v_sz_3916_);
v_i_boxed_3920_ = lean_unbox_usize(v_i_3917_);
lean_dec(v_i_3917_);
v_res_3921_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_mkListRemovalSuggestion_spec__0(v_sz_boxed_3919_, v_i_boxed_3920_, v_bs_3918_);
return v_res_3921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_mkListRemovalSuggestion___redArg(lean_object* v_whole_3927_, lean_object* v_elems_3928_, lean_object* v_i_3929_, lean_object* v_a_3930_){
_start:
{
lean_object* v_toCold_3935_; lean_object* v_fileMap_3936_; lean_object* v_source_3937_; uint8_t v___x_3938_; lean_object* v___x_3939_; 
v_toCold_3935_ = lean_ctor_get(v_a_3930_, 0);
v_fileMap_3936_ = lean_ctor_get(v_toCold_3935_, 1);
v_source_3937_ = lean_ctor_get(v_fileMap_3936_, 0);
v___x_3938_ = 1;
v___x_3939_ = l_Lean_Syntax_getSubstring_x3f(v_whole_3927_, v___x_3938_, v___x_3938_);
if (lean_obj_tag(v___x_3939_) == 0)
{
lean_dec_ref(v_elems_3928_);
lean_dec(v_whole_3927_);
goto v___jp_3932_;
}
else
{
lean_object* v_val_3940_; lean_object* v___x_3942_; uint8_t v_isShared_3943_; uint8_t v_isSharedCheck_4010_; 
v_val_3940_ = lean_ctor_get(v___x_3939_, 0);
v_isSharedCheck_4010_ = !lean_is_exclusive(v___x_3939_);
if (v_isSharedCheck_4010_ == 0)
{
v___x_3942_ = v___x_3939_;
v_isShared_3943_ = v_isSharedCheck_4010_;
goto v_resetjp_3941_;
}
else
{
lean_inc(v_val_3940_);
lean_dec(v___x_3939_);
v___x_3942_ = lean_box(0);
v_isShared_3943_ = v_isSharedCheck_4010_;
goto v_resetjp_3941_;
}
v_resetjp_3941_:
{
lean_object* v_str_3944_; uint8_t v___x_3945_; 
v_str_3944_ = lean_ctor_get(v_val_3940_, 0);
lean_inc_ref(v_str_3944_);
lean_dec(v_val_3940_);
v___x_3945_ = lean_string_dec_eq(v_str_3944_, v_source_3937_);
lean_dec_ref(v_str_3944_);
if (v___x_3945_ == 0)
{
lean_del_object(v___x_3942_);
lean_dec_ref(v_elems_3928_);
lean_dec(v_whole_3927_);
goto v___jp_3932_;
}
else
{
lean_object* v___x_3946_; 
v___x_3946_ = l_Lean_Syntax_getRange_x3f(v_whole_3927_, v___x_3938_);
if (lean_obj_tag(v___x_3946_) == 1)
{
lean_object* v_val_3947_; lean_object* v___x_3949_; uint8_t v_isShared_3950_; uint8_t v_isSharedCheck_4007_; 
v_val_3947_ = lean_ctor_get(v___x_3946_, 0);
v_isSharedCheck_4007_ = !lean_is_exclusive(v___x_3946_);
if (v_isSharedCheck_4007_ == 0)
{
v___x_3949_ = v___x_3946_;
v_isShared_3950_ = v_isSharedCheck_4007_;
goto v_resetjp_3948_;
}
else
{
lean_inc(v_val_3947_);
lean_dec(v___x_3946_);
v___x_3949_ = lean_box(0);
v_isShared_3950_ = v_isSharedCheck_4007_;
goto v_resetjp_3948_;
}
v_resetjp_3948_:
{
lean_object* v_fst_3952_; lean_object* v_snd_3953_; size_t v_sz_3971_; size_t v___x_3972_; lean_object* v___x_3973_; 
v_sz_3971_ = lean_array_size(v_elems_3928_);
v___x_3972_ = ((size_t)0ULL);
v___x_3973_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_mkListRemovalSuggestion_spec__0(v_sz_3971_, v___x_3972_, v_elems_3928_);
if (lean_obj_tag(v___x_3973_) == 1)
{
lean_object* v_val_3974_; lean_object* v___x_3976_; uint8_t v_isShared_3977_; uint8_t v_isSharedCheck_4004_; 
v_val_3974_ = lean_ctor_get(v___x_3973_, 0);
v_isSharedCheck_4004_ = !lean_is_exclusive(v___x_3973_);
if (v_isSharedCheck_4004_ == 0)
{
v___x_3976_ = v___x_3973_;
v_isShared_3977_ = v_isSharedCheck_4004_;
goto v_resetjp_3975_;
}
else
{
lean_inc(v_val_3974_);
lean_dec(v___x_3973_);
v___x_3976_ = lean_box(0);
v_isShared_3977_ = v_isSharedCheck_4004_;
goto v_resetjp_3975_;
}
v_resetjp_3975_:
{
lean_object* v___x_3978_; uint8_t v___x_3979_; 
v___x_3978_ = lean_array_get_size(v_val_3974_);
v___x_3979_ = lean_nat_dec_lt(v_i_3929_, v___x_3978_);
if (v___x_3979_ == 0)
{
lean_object* v___x_3980_; lean_object* v___x_3981_; 
lean_del_object(v___x_3976_);
lean_dec(v_val_3974_);
lean_del_object(v___x_3949_);
lean_dec(v_val_3947_);
lean_del_object(v___x_3942_);
lean_dec(v_whole_3927_);
v___x_3980_ = lean_box(0);
v___x_3981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3981_, 0, v___x_3980_);
return v___x_3981_;
}
else
{
lean_object* v___x_3982_; uint8_t v___x_3983_; 
v___x_3982_ = lean_unsigned_to_nat(1u);
v___x_3983_ = lean_nat_dec_eq(v___x_3978_, v___x_3982_);
if (v___x_3983_ == 0)
{
lean_object* v___x_3984_; lean_object* v___x_3985_; uint8_t v___x_3986_; 
lean_del_object(v___x_3976_);
v___x_3984_ = lean_array_fget_borrowed(v_val_3974_, v_i_3929_);
v___x_3985_ = lean_nat_add(v_i_3929_, v___x_3982_);
v___x_3986_ = lean_nat_dec_lt(v___x_3985_, v___x_3978_);
if (v___x_3986_ == 0)
{
lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v_stop_3990_; lean_object* v_stop_3991_; 
lean_inc(v___x_3984_);
lean_dec(v___x_3985_);
v___x_3987_ = l_Lean_Syntax_instInhabitedRange_default;
v___x_3988_ = lean_nat_sub(v_i_3929_, v___x_3982_);
v___x_3989_ = lean_array_get(v___x_3987_, v_val_3974_, v___x_3988_);
lean_dec(v___x_3988_);
lean_dec(v_val_3974_);
v_stop_3990_ = lean_ctor_get(v___x_3989_, 1);
lean_inc(v_stop_3990_);
lean_dec(v___x_3989_);
v_stop_3991_ = lean_ctor_get(v___x_3984_, 1);
lean_inc(v_stop_3991_);
lean_dec(v___x_3984_);
v_fst_3952_ = v_stop_3990_;
v_snd_3953_ = v_stop_3991_;
goto v___jp_3951_;
}
else
{
lean_object* v_start_3992_; lean_object* v___x_3993_; lean_object* v_start_3994_; 
v_start_3992_ = lean_ctor_get(v___x_3984_, 0);
lean_inc(v_start_3992_);
v___x_3993_ = lean_array_fget(v_val_3974_, v___x_3985_);
lean_dec(v___x_3985_);
lean_dec(v_val_3974_);
v_start_3994_ = lean_ctor_get(v___x_3993_, 0);
lean_inc(v_start_3994_);
lean_dec(v___x_3993_);
v_fst_3952_ = v_start_3992_;
v_snd_3953_ = v_start_3994_;
goto v___jp_3951_;
}
}
else
{
lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3998_; 
lean_dec(v_val_3974_);
lean_del_object(v___x_3949_);
lean_dec(v_val_3947_);
lean_del_object(v___x_3942_);
v___x_3995_ = lean_box(0);
v___x_3996_ = ((lean_object*)(l_Lean_Linter_mkListRemovalSuggestion___redArg___closed__1));
if (v_isShared_3977_ == 0)
{
lean_ctor_set(v___x_3976_, 0, v_whole_3927_);
v___x_3998_ = v___x_3976_;
goto v_reusejp_3997_;
}
else
{
lean_object* v_reuseFailAlloc_4003_; 
v_reuseFailAlloc_4003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4003_, 0, v_whole_3927_);
v___x_3998_ = v_reuseFailAlloc_4003_;
goto v_reusejp_3997_;
}
v_reusejp_3997_:
{
uint8_t v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; 
v___x_3999_ = 0;
v___x_4000_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4000_, 0, v___x_3996_);
lean_ctor_set(v___x_4000_, 1, v___x_3998_);
lean_ctor_set(v___x_4000_, 2, v___x_3995_);
lean_ctor_set_uint8(v___x_4000_, sizeof(void*)*3, v___x_3999_);
v___x_4001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4001_, 0, v___x_4000_);
v___x_4002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4002_, 0, v___x_4001_);
return v___x_4002_;
}
}
}
}
}
else
{
lean_object* v___x_4005_; lean_object* v___x_4006_; 
lean_dec(v___x_3973_);
lean_del_object(v___x_3949_);
lean_dec(v_val_3947_);
lean_del_object(v___x_3942_);
lean_dec(v_whole_3927_);
v___x_4005_ = lean_box(0);
v___x_4006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4006_, 0, v___x_4005_);
return v___x_4006_;
}
v___jp_3951_:
{
lean_object* v_start_3954_; lean_object* v_stop_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3963_; 
v_start_3954_ = lean_ctor_get(v_val_3947_, 0);
lean_inc(v_start_3954_);
v_stop_3955_ = lean_ctor_get(v_val_3947_, 1);
lean_inc(v_stop_3955_);
lean_dec(v_val_3947_);
v___x_3956_ = lean_string_utf8_extract(v_source_3937_, v_start_3954_, v_fst_3952_);
lean_dec(v_fst_3952_);
lean_dec(v_start_3954_);
v___x_3957_ = lean_string_utf8_extract(v_source_3937_, v_snd_3953_, v_stop_3955_);
lean_dec(v_stop_3955_);
lean_dec(v_snd_3953_);
v___x_3958_ = lean_string_append(v___x_3956_, v___x_3957_);
lean_dec_ref(v___x_3957_);
v___x_3959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3958_);
v___x_3960_ = lean_box(0);
v___x_3961_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3961_, 0, v___x_3959_);
lean_ctor_set(v___x_3961_, 1, v___x_3960_);
lean_ctor_set(v___x_3961_, 2, v___x_3960_);
lean_ctor_set(v___x_3961_, 3, v___x_3960_);
lean_ctor_set(v___x_3961_, 4, v___x_3960_);
lean_ctor_set(v___x_3961_, 5, v___x_3960_);
if (v_isShared_3950_ == 0)
{
lean_ctor_set(v___x_3949_, 0, v_whole_3927_);
v___x_3963_ = v___x_3949_;
goto v_reusejp_3962_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v_whole_3927_);
v___x_3963_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3962_;
}
v_reusejp_3962_:
{
uint8_t v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3967_; 
v___x_3964_ = 0;
v___x_3965_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3965_, 0, v___x_3961_);
lean_ctor_set(v___x_3965_, 1, v___x_3963_);
lean_ctor_set(v___x_3965_, 2, v___x_3960_);
lean_ctor_set_uint8(v___x_3965_, sizeof(void*)*3, v___x_3964_);
if (v_isShared_3943_ == 0)
{
lean_ctor_set(v___x_3942_, 0, v___x_3965_);
v___x_3967_ = v___x_3942_;
goto v_reusejp_3966_;
}
else
{
lean_object* v_reuseFailAlloc_3969_; 
v_reuseFailAlloc_3969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3969_, 0, v___x_3965_);
v___x_3967_ = v_reuseFailAlloc_3969_;
goto v_reusejp_3966_;
}
v_reusejp_3966_:
{
lean_object* v___x_3968_; 
v___x_3968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3968_, 0, v___x_3967_);
return v___x_3968_;
}
}
}
}
}
else
{
lean_object* v___x_4008_; lean_object* v___x_4009_; 
lean_dec(v___x_3946_);
lean_del_object(v___x_3942_);
lean_dec_ref(v_elems_3928_);
lean_dec(v_whole_3927_);
v___x_4008_ = lean_box(0);
v___x_4009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4009_, 0, v___x_4008_);
return v___x_4009_;
}
}
}
}
v___jp_3932_:
{
lean_object* v___x_3933_; lean_object* v___x_3934_; 
v___x_3933_ = lean_box(0);
v___x_3934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3934_, 0, v___x_3933_);
return v___x_3934_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_mkListRemovalSuggestion___redArg___boxed(lean_object* v_whole_4011_, lean_object* v_elems_4012_, lean_object* v_i_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_){
_start:
{
lean_object* v_res_4016_; 
v_res_4016_ = l_Lean_Linter_mkListRemovalSuggestion___redArg(v_whole_4011_, v_elems_4012_, v_i_4013_, v_a_4014_);
lean_dec_ref(v_a_4014_);
lean_dec(v_i_4013_);
return v_res_4016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_mkListRemovalSuggestion(lean_object* v_whole_4017_, lean_object* v_elems_4018_, lean_object* v_i_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_){
_start:
{
lean_object* v___x_4023_; 
v___x_4023_ = l_Lean_Linter_mkListRemovalSuggestion___redArg(v_whole_4017_, v_elems_4018_, v_i_4019_, v_a_4020_);
return v___x_4023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_mkListRemovalSuggestion___boxed(lean_object* v_whole_4024_, lean_object* v_elems_4025_, lean_object* v_i_4026_, lean_object* v_a_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_){
_start:
{
lean_object* v_res_4030_; 
v_res_4030_ = l_Lean_Linter_mkListRemovalSuggestion(v_whole_4024_, v_elems_4025_, v_i_4026_, v_a_4027_, v_a_4028_);
lean_dec(v_a_4028_);
lean_dec_ref(v_a_4027_);
lean_dec(v_i_4026_);
return v_res_4030_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecatedAutomationAttr___closed__1(void){
_start:
{
lean_object* v___x_4032_; lean_object* v___x_4033_; 
v___x_4032_ = ((lean_object*)(l_Lean_Linter_checkDeprecatedAutomationAttr___closed__0));
v___x_4033_ = l_Lean_stringToMessageData(v___x_4032_);
return v___x_4033_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecatedAutomationAttr___closed__3(void){
_start:
{
lean_object* v___x_4035_; lean_object* v___x_4036_; 
v___x_4035_ = ((lean_object*)(l_Lean_Linter_checkDeprecatedAutomationAttr___closed__2));
v___x_4036_ = l_Lean_stringToMessageData(v___x_4035_);
return v___x_4036_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecatedAutomationAttr___closed__5(void){
_start:
{
lean_object* v___x_4038_; lean_object* v___x_4039_; 
v___x_4038_ = ((lean_object*)(l_Lean_Linter_checkDeprecatedAutomationAttr___closed__4));
v___x_4039_ = l_Lean_stringToMessageData(v___x_4038_);
return v___x_4039_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecatedAutomationAttr___closed__7(void){
_start:
{
lean_object* v___x_4041_; lean_object* v___x_4042_; 
v___x_4041_ = ((lean_object*)(l_Lean_Linter_checkDeprecatedAutomationAttr___closed__6));
v___x_4042_ = l_Lean_stringToMessageData(v___x_4041_);
return v___x_4042_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecatedAutomationAttr___closed__9(void){
_start:
{
lean_object* v___x_4044_; lean_object* v___x_4045_; 
v___x_4044_ = ((lean_object*)(l_Lean_Linter_checkDeprecatedAutomationAttr___closed__8));
v___x_4045_ = l_Lean_stringToMessageData(v___x_4044_);
return v___x_4045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkDeprecatedAutomationAttr(lean_object* v_ref_4046_, lean_object* v_declName_4047_, lean_object* v_attrName_4048_, lean_object* v_removal_x3f_4049_, lean_object* v_a_4050_, lean_object* v_a_4051_, lean_object* v_a_4052_, lean_object* v_a_4053_){
_start:
{
lean_object* v_toCold_4055_; lean_object* v_currRecDepth_4056_; lean_object* v_ref_4057_; uint16_t v_optionFlags_4058_; uint8_t v_suppressElabErrors_4059_; uint8_t v_checkDeprecated_4060_; uint8_t v_isRecordingDeps_4061_; lean_object* v_ref_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v_a_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4137_; 
v_toCold_4055_ = lean_ctor_get(v_a_4052_, 0);
v_currRecDepth_4056_ = lean_ctor_get(v_a_4052_, 1);
v_ref_4057_ = lean_ctor_get(v_a_4052_, 2);
v_optionFlags_4058_ = lean_ctor_get_uint16(v_a_4052_, sizeof(void*)*3);
v_suppressElabErrors_4059_ = lean_ctor_get_uint8(v_a_4052_, sizeof(void*)*3 + 2);
v_checkDeprecated_4060_ = lean_ctor_get_uint8(v_a_4052_, sizeof(void*)*3 + 3);
v_isRecordingDeps_4061_ = lean_ctor_get_uint8(v_a_4052_, sizeof(void*)*3 + 4);
v_ref_4062_ = l_Lean_replaceRef(v_ref_4046_, v_ref_4057_);
lean_inc(v_currRecDepth_4056_);
lean_inc_ref(v_toCold_4055_);
v___x_4063_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_4063_, 0, v_toCold_4055_);
lean_ctor_set(v___x_4063_, 1, v_currRecDepth_4056_);
lean_ctor_set(v___x_4063_, 2, v_ref_4062_);
lean_ctor_set_uint16(v___x_4063_, sizeof(void*)*3, v_optionFlags_4058_);
lean_ctor_set_uint8(v___x_4063_, sizeof(void*)*3 + 2, v_suppressElabErrors_4059_);
lean_ctor_set_uint8(v___x_4063_, sizeof(void*)*3 + 3, v_checkDeprecated_4060_);
lean_ctor_set_uint8(v___x_4063_, sizeof(void*)*3 + 4, v_isRecordingDeps_4061_);
v___x_4064_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0(v_a_4050_, v_a_4051_, v___x_4063_, v_a_4053_);
v_a_4065_ = lean_ctor_get(v___x_4064_, 0);
v_isSharedCheck_4137_ = !lean_is_exclusive(v___x_4064_);
if (v_isSharedCheck_4137_ == 0)
{
v___x_4067_ = v___x_4064_;
v_isShared_4068_ = v_isSharedCheck_4137_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_a_4065_);
lean_dec(v___x_4064_);
v___x_4067_ = lean_box(0);
v_isShared_4068_ = v_isSharedCheck_4137_;
goto v_resetjp_4066_;
}
v_resetjp_4066_:
{
lean_object* v___x_4069_; uint8_t v___x_4070_; 
v___x_4069_ = l_Lean_Linter_linter_deprecated;
v___x_4070_ = l_Lean_Linter_getLinterValue(v___x_4069_, v_a_4065_);
lean_dec(v_a_4065_);
if (v___x_4070_ == 0)
{
lean_object* v___x_4071_; lean_object* v___x_4073_; 
lean_dec_ref_known(v___x_4063_, 3);
lean_dec(v_removal_x3f_4049_);
lean_dec(v_attrName_4048_);
lean_dec(v_declName_4047_);
v___x_4071_ = lean_box(0);
if (v_isShared_4068_ == 0)
{
lean_ctor_set(v___x_4067_, 0, v___x_4071_);
v___x_4073_ = v___x_4067_;
goto v_reusejp_4072_;
}
else
{
lean_object* v_reuseFailAlloc_4074_; 
v_reuseFailAlloc_4074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4074_, 0, v___x_4071_);
v___x_4073_ = v_reuseFailAlloc_4074_;
goto v_reusejp_4072_;
}
v_reusejp_4072_:
{
return v___x_4073_;
}
}
else
{
lean_object* v___x_4075_; lean_object* v___x_4076_; uint8_t v___x_4077_; lean_object* v_hint_4079_; lean_object* v___y_4080_; lean_object* v___y_4081_; lean_object* v___y_4082_; lean_object* v___y_4083_; 
v___x_4075_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___x_4063_);
v___x_4076_ = l_Lean_Linter_linter_deprecated_automationAttr;
v___x_4077_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__5(v___x_4075_, v___x_4076_);
lean_dec_ref(v___x_4075_);
if (v___x_4077_ == 0)
{
lean_object* v___x_4103_; lean_object* v___x_4105_; 
lean_dec_ref_known(v___x_4063_, 3);
lean_dec(v_removal_x3f_4049_);
lean_dec(v_attrName_4048_);
lean_dec(v_declName_4047_);
v___x_4103_ = lean_box(0);
if (v_isShared_4068_ == 0)
{
lean_ctor_set(v___x_4067_, 0, v___x_4103_);
v___x_4105_ = v___x_4067_;
goto v_reusejp_4104_;
}
else
{
lean_object* v_reuseFailAlloc_4106_; 
v_reuseFailAlloc_4106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4106_, 0, v___x_4103_);
v___x_4105_ = v_reuseFailAlloc_4106_;
goto v_reusejp_4104_;
}
v_reusejp_4104_:
{
return v___x_4105_;
}
}
else
{
lean_object* v___x_4107_; 
v___x_4107_ = l_Lean_Syntax_getHeadInfo(v_ref_4046_);
if (lean_obj_tag(v___x_4107_) == 0)
{
lean_object* v___x_4108_; lean_object* v_env_4109_; uint8_t v___x_4110_; 
lean_dec_ref_known(v___x_4107_, 4);
v___x_4108_ = lean_st_ref_get(v_a_4053_);
v_env_4109_ = lean_ctor_get(v___x_4108_, 0);
lean_inc_ref(v_env_4109_);
lean_dec(v___x_4108_);
lean_inc(v_declName_4047_);
v___x_4110_ = l_Lean_Linter_isDeprecated(v_env_4109_, v_declName_4047_);
if (v___x_4110_ == 0)
{
lean_object* v___x_4111_; lean_object* v___x_4113_; 
lean_dec_ref_known(v___x_4063_, 3);
lean_dec(v_removal_x3f_4049_);
lean_dec(v_attrName_4048_);
lean_dec(v_declName_4047_);
v___x_4111_ = lean_box(0);
if (v_isShared_4068_ == 0)
{
lean_ctor_set(v___x_4067_, 0, v___x_4111_);
v___x_4113_ = v___x_4067_;
goto v_reusejp_4112_;
}
else
{
lean_object* v_reuseFailAlloc_4114_; 
v_reuseFailAlloc_4114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4114_, 0, v___x_4111_);
v___x_4113_ = v_reuseFailAlloc_4114_;
goto v_reusejp_4112_;
}
v_reusejp_4112_:
{
return v___x_4113_;
}
}
else
{
lean_del_object(v___x_4067_);
if (lean_obj_tag(v_removal_x3f_4049_) == 0)
{
lean_object* v___x_4115_; 
v___x_4115_ = l_Lean_MessageData_nil;
v_hint_4079_ = v___x_4115_;
v___y_4080_ = v_a_4050_;
v___y_4081_ = v_a_4051_;
v___y_4082_ = v___x_4063_;
v___y_4083_ = v_a_4053_;
goto v___jp_4078_;
}
else
{
lean_object* v_val_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; uint8_t v___x_4122_; lean_object* v___x_4123_; 
v_val_4116_ = lean_ctor_get(v_removal_x3f_4049_, 0);
lean_inc(v_val_4116_);
lean_dec_ref_known(v_removal_x3f_4049_, 1);
v___x_4117_ = lean_obj_once(&l_Lean_Linter_checkDeprecatedAutomationAttr___closed__9, &l_Lean_Linter_checkDeprecatedAutomationAttr___closed__9_once, _init_l_Lean_Linter_checkDeprecatedAutomationAttr___closed__9);
v___x_4118_ = lean_unsigned_to_nat(1u);
v___x_4119_ = lean_mk_empty_array_with_capacity(v___x_4118_);
v___x_4120_ = lean_array_push(v___x_4119_, v_val_4116_);
v___x_4121_ = lean_box(0);
v___x_4122_ = 0;
v___x_4123_ = l_Lean_MessageData_hint(v___x_4117_, v___x_4120_, v___x_4121_, v___x_4121_, v___x_4122_, v___x_4063_, v_a_4053_);
lean_dec_ref(v___x_4120_);
if (lean_obj_tag(v___x_4123_) == 0)
{
lean_object* v_a_4124_; 
v_a_4124_ = lean_ctor_get(v___x_4123_, 0);
lean_inc(v_a_4124_);
lean_dec_ref_known(v___x_4123_, 1);
v_hint_4079_ = v_a_4124_;
v___y_4080_ = v_a_4050_;
v___y_4081_ = v_a_4051_;
v___y_4082_ = v___x_4063_;
v___y_4083_ = v_a_4053_;
goto v___jp_4078_;
}
else
{
lean_object* v_a_4125_; lean_object* v___x_4127_; uint8_t v_isShared_4128_; uint8_t v_isSharedCheck_4132_; 
lean_dec_ref_known(v___x_4063_, 3);
lean_dec(v_attrName_4048_);
lean_dec(v_declName_4047_);
v_a_4125_ = lean_ctor_get(v___x_4123_, 0);
v_isSharedCheck_4132_ = !lean_is_exclusive(v___x_4123_);
if (v_isSharedCheck_4132_ == 0)
{
v___x_4127_ = v___x_4123_;
v_isShared_4128_ = v_isSharedCheck_4132_;
goto v_resetjp_4126_;
}
else
{
lean_inc(v_a_4125_);
lean_dec(v___x_4123_);
v___x_4127_ = lean_box(0);
v_isShared_4128_ = v_isSharedCheck_4132_;
goto v_resetjp_4126_;
}
v_resetjp_4126_:
{
lean_object* v___x_4130_; 
if (v_isShared_4128_ == 0)
{
v___x_4130_ = v___x_4127_;
goto v_reusejp_4129_;
}
else
{
lean_object* v_reuseFailAlloc_4131_; 
v_reuseFailAlloc_4131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4131_, 0, v_a_4125_);
v___x_4130_ = v_reuseFailAlloc_4131_;
goto v_reusejp_4129_;
}
v_reusejp_4129_:
{
return v___x_4130_;
}
}
}
}
}
}
else
{
lean_object* v___x_4133_; lean_object* v___x_4135_; 
lean_dec(v___x_4107_);
lean_dec_ref_known(v___x_4063_, 3);
lean_dec(v_removal_x3f_4049_);
lean_dec(v_attrName_4048_);
lean_dec(v_declName_4047_);
v___x_4133_ = lean_box(0);
if (v_isShared_4068_ == 0)
{
lean_ctor_set(v___x_4067_, 0, v___x_4133_);
v___x_4135_ = v___x_4067_;
goto v_reusejp_4134_;
}
else
{
lean_object* v_reuseFailAlloc_4136_; 
v_reuseFailAlloc_4136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4136_, 0, v___x_4133_);
v___x_4135_ = v_reuseFailAlloc_4136_;
goto v_reusejp_4134_;
}
v_reusejp_4134_:
{
return v___x_4135_;
}
}
}
v___jp_4078_:
{
lean_object* v_name_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; 
v_name_4084_ = lean_ctor_get(v___x_4076_, 0);
v___x_4085_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_4086_ = l_Lean_MessageData_ofConstName(v_declName_4047_, v___x_4077_);
v___x_4087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4087_, 0, v___x_4085_);
lean_ctor_set(v___x_4087_, 1, v___x_4086_);
v___x_4088_ = lean_obj_once(&l_Lean_Linter_checkDeprecatedAutomationAttr___closed__1, &l_Lean_Linter_checkDeprecatedAutomationAttr___closed__1_once, _init_l_Lean_Linter_checkDeprecatedAutomationAttr___closed__1);
v___x_4089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4089_, 0, v___x_4087_);
lean_ctor_set(v___x_4089_, 1, v___x_4088_);
v___x_4090_ = l_Lean_MessageData_ofName(v_attrName_4048_);
v___x_4091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4091_, 0, v___x_4089_);
lean_ctor_set(v___x_4091_, 1, v___x_4090_);
v___x_4092_ = lean_obj_once(&l_Lean_Linter_checkDeprecatedAutomationAttr___closed__3, &l_Lean_Linter_checkDeprecatedAutomationAttr___closed__3_once, _init_l_Lean_Linter_checkDeprecatedAutomationAttr___closed__3);
v___x_4093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4093_, 0, v___x_4091_);
lean_ctor_set(v___x_4093_, 1, v___x_4092_);
v___x_4094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4094_, 0, v___x_4093_);
lean_ctor_set(v___x_4094_, 1, v_hint_4079_);
v___x_4095_ = lean_obj_once(&l_Lean_Linter_checkDeprecatedAutomationAttr___closed__5, &l_Lean_Linter_checkDeprecatedAutomationAttr___closed__5_once, _init_l_Lean_Linter_checkDeprecatedAutomationAttr___closed__5);
lean_inc(v_name_4084_);
v___x_4096_ = l_Lean_MessageData_ofName(v_name_4084_);
v___x_4097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4097_, 0, v___x_4095_);
lean_ctor_set(v___x_4097_, 1, v___x_4096_);
v___x_4098_ = lean_obj_once(&l_Lean_Linter_checkDeprecatedAutomationAttr___closed__7, &l_Lean_Linter_checkDeprecatedAutomationAttr___closed__7_once, _init_l_Lean_Linter_checkDeprecatedAutomationAttr___closed__7);
v___x_4099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4099_, 0, v___x_4097_);
lean_ctor_set(v___x_4099_, 1, v___x_4098_);
v___x_4100_ = l_Lean_MessageData_note(v___x_4099_);
v___x_4101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4101_, 0, v___x_4094_);
lean_ctor_set(v___x_4101_, 1, v___x_4100_);
v___x_4102_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40(v___x_4101_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_);
lean_dec_ref(v___y_4082_);
return v___x_4102_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkDeprecatedAutomationAttr___boxed(lean_object* v_ref_4138_, lean_object* v_declName_4139_, lean_object* v_attrName_4140_, lean_object* v_removal_x3f_4141_, lean_object* v_a_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_, lean_object* v_a_4146_){
_start:
{
lean_object* v_res_4147_; 
v_res_4147_ = l_Lean_Linter_checkDeprecatedAutomationAttr(v_ref_4138_, v_declName_4139_, v_attrName_4140_, v_removal_x3f_4141_, v_a_4142_, v_a_4143_, v_a_4144_, v_a_4145_);
lean_dec(v_a_4145_);
lean_dec_ref(v_a_4144_);
lean_dec(v_a_4143_);
lean_dec_ref(v_a_4142_);
lean_dec(v_ref_4138_);
return v_res_4147_;
}
}
static uint64_t _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4154_; uint64_t v___x_4155_; 
v___x_4154_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2_));
v___x_4155_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4154_);
return v___x_4155_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; 
v___x_4156_ = lean_uint64_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2_);
v___x_4157_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2_));
v___x_4158_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4158_, 0, v___x_4157_);
lean_ctor_set_uint64(v___x_4158_, sizeof(void*)*1, v___x_4156_);
return v___x_4158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2_(lean_object* v___x_4159_, lean_object* v_ref_4160_, lean_object* v_declName_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_){
_start:
{
lean_object* v___x_4165_; uint8_t v___x_4166_; uint8_t v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; 
v___x_4165_ = lean_box(1);
v___x_4166_ = 0;
v___x_4167_ = 1;
v___x_4168_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2_);
v___x_4169_ = lean_unsigned_to_nat(0u);
v___x_4170_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_4171_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__27_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__27_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__27_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_4172_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__28_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_));
v___x_4173_ = lean_box(0);
lean_inc(v___x_4159_);
v___x_4174_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4174_, 0, v___x_4168_);
lean_ctor_set(v___x_4174_, 1, v___x_4159_);
lean_ctor_set(v___x_4174_, 2, v___x_4171_);
lean_ctor_set(v___x_4174_, 3, v___x_4172_);
lean_ctor_set(v___x_4174_, 4, v___x_4173_);
lean_ctor_set(v___x_4174_, 5, v___x_4169_);
lean_ctor_set(v___x_4174_, 6, v___x_4173_);
lean_ctor_set_uint8(v___x_4174_, sizeof(void*)*7, v___x_4166_);
lean_ctor_set_uint8(v___x_4174_, sizeof(void*)*7 + 1, v___x_4166_);
lean_ctor_set_uint8(v___x_4174_, sizeof(void*)*7 + 2, v___x_4166_);
lean_ctor_set_uint8(v___x_4174_, sizeof(void*)*7 + 3, v___x_4167_);
v___x_4175_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_4176_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_4177_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_251821608____hygCtx___hyg_2_);
v___x_4178_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4178_, 0, v___x_4175_);
lean_ctor_set(v___x_4178_, 1, v___x_4176_);
lean_ctor_set(v___x_4178_, 2, v___x_4159_);
lean_ctor_set(v___x_4178_, 3, v___x_4170_);
lean_ctor_set(v___x_4178_, 4, v___x_4177_);
v___x_4179_ = lean_st_mk_ref(v___x_4178_);
v___x_4180_ = l_Lean_Linter_checkDeprecatedAt(v_ref_4160_, v_declName_4161_, v___x_4165_, v___x_4174_, v___x_4179_, v___y_4162_, v___y_4163_);
lean_dec_ref_known(v___x_4174_, 7);
if (lean_obj_tag(v___x_4180_) == 0)
{
lean_object* v_a_4181_; lean_object* v___x_4183_; uint8_t v_isShared_4184_; uint8_t v_isSharedCheck_4189_; 
v_a_4181_ = lean_ctor_get(v___x_4180_, 0);
v_isSharedCheck_4189_ = !lean_is_exclusive(v___x_4180_);
if (v_isSharedCheck_4189_ == 0)
{
v___x_4183_ = v___x_4180_;
v_isShared_4184_ = v_isSharedCheck_4189_;
goto v_resetjp_4182_;
}
else
{
lean_inc(v_a_4181_);
lean_dec(v___x_4180_);
v___x_4183_ = lean_box(0);
v_isShared_4184_ = v_isSharedCheck_4189_;
goto v_resetjp_4182_;
}
v_resetjp_4182_:
{
lean_object* v___x_4185_; lean_object* v___x_4187_; 
v___x_4185_ = lean_st_ref_get(v___x_4179_);
lean_dec(v___x_4179_);
lean_dec(v___x_4185_);
if (v_isShared_4184_ == 0)
{
v___x_4187_ = v___x_4183_;
goto v_reusejp_4186_;
}
else
{
lean_object* v_reuseFailAlloc_4188_; 
v_reuseFailAlloc_4188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4188_, 0, v_a_4181_);
v___x_4187_ = v_reuseFailAlloc_4188_;
goto v_reusejp_4186_;
}
v_reusejp_4186_:
{
return v___x_4187_;
}
}
}
else
{
lean_dec(v___x_4179_);
return v___x_4180_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2____boxed(lean_object* v___x_4190_, lean_object* v_ref_4191_, lean_object* v_declName_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_){
_start:
{
lean_object* v_res_4196_; 
v_res_4196_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2_(v___x_4190_, v_ref_4191_, v_declName_4192_, v___y_4193_, v___y_4194_);
lean_dec(v___y_4194_);
lean_dec_ref(v___y_4193_);
lean_dec(v_ref_4191_);
return v_res_4196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; 
v___f_4200_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2_));
v___x_4201_ = l_Lean_Core_checkDeprecatedAtRef;
v___x_4202_ = lean_box(0);
v___x_4203_ = lean_st_ref_swap(v___x_4201_, v___f_4200_);
lean_dec(v___x_4203_);
v___x_4204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4204_, 0, v___x_4202_);
return v___x_4204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2____boxed(lean_object* v_a_4205_){
_start:
{
lean_object* v_res_4206_; 
v_res_4206_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3091180067____hygCtx___hyg_2_();
return v_res_4206_;
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
