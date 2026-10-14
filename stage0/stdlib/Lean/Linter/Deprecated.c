// Lean compiler output
// Module: Lean.Linter.Deprecated
// Imports: public import Lean.Meta.Basic import Lean.Linter.Init import Lean.Elab.InfoTree.Main import Lean.ExtraModUses import Lean.Meta.Hint import Init.Data.List.MapIdx import Init.Omega import Std.Time.Format import Std.Time.Zoned
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
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
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
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Syntax_ofRange(lean_object*, uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_hint(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_extractMacroScopes(lean_object*);
lean_object* l_Lean_MacroScopesView_review(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MacroScopesView_isSuffixOf(lean_object*, lean_object*);
lean_object* l_Lean_privateToUserName_x3f(lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
extern lean_object* l_Lean_ResolveName_backward_privateInPublic_warn;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_Name_componentsRev(lean_object*);
lean_object* l_Lean_Name_appendCore(lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
extern lean_object* l_Lean_rootNamespace;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_getRevAliases(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Name_getPrefix(lean_object*);
lean_object* l_Std_HashMap_instInhabited___redArg();
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___redArg();
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerParametricAttributeExt___redArg(lean_object*, uint8_t, lean_object*, uint8_t);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_MessageData_hint_x27(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_ConstantInfo_numLevelParams(lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_ConstantInfo_instantiateTypeLevelParams(lean_object*, lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
extern lean_object* l_Lean_Linter_linterSetsExt;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_registerParametricAttributeForExt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_ParametricAttribute_setParam___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___redArg(lean_object*, lean_object*);
lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
uint8_t l_Lean_isProtected(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_List_get___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__0_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Try this: +typeChanged"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__0_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__0_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44_spec__47(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44_spec__47___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48___closed__0_value;
static const lean_ctor_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Private declaration `"};
static const lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___closed__0 = (const lean_object*)&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___closed__0_value;
static lean_once_cell_t l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___closed__1;
static const lean_string_object l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 167, .m_capacity = 167, .m_length = 166, .m_data = "` accessed publicly; this is allowed only because the `backward.privateInPublic` option is enabled. \n\nDisable `backward.privateInPublic.warn` to silence this warning."};
static const lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___closed__2 = (const lean_object*)&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___closed__2_value;
static lean_once_cell_t l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___closed__3;
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__31(lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__31___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22___lam__0___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__0 = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__0_value;
static const lean_closure_object l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22___lam__0___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48___closed__1_value)} };
static const lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__1 = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22___closed__0 = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__24(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12___closed__0 = (const lean_object*)&l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__17___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__17___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5___lam__0___boxed, .m_arity = 7, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5___closed__0 = (const lean_object*)&l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___lam__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__0;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__1;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__2;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__3_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__4 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__4_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__7_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__8;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__9;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__10 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__10_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__11;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__12 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__12_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__13;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__15_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__16_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__18_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2___closed__0;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__0_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 134, .m_capacity = 134, .m_length = 133, .m_data = "`[deprecated]` attribute should specify the date or library version at which the deprecation was introduced, using `(since := \"...\")`"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__0_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__0_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__1_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__1_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__2_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 83, .m_capacity = 83, .m_length = 82, .m_data = "`[deprecated]` attribute should specify either a new name or a deprecation message"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__2_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__2_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__3_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__2_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__3_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__3_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__4_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__4_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__5_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "The updated constant has a different type:"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__5_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__5_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "\ninstead of"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 372, .m_capacity = 372, .m_length = 371, .m_data = "\n\nThis suggests that addressing the deprecation might be more involved than simply replacing the old name with the new name. This is often expected, but sometimes it indicates that the deprecation is in favor of the wrong declaration, or that there is a mistake in one of the statements.\n\nIf the type difference is intentional, use `+typeChanged` to silence this warning."};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__10_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__10_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__11_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Add `+typeChanged` to silence this warning."};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__11_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__11_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__12_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__11_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__12_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__12_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__13_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__13_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__14_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__14_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__15_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Invalid `[deprecated]` attribute syntax"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__15_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__15_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Add `+typeChanged`:"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__18_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__18_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__18_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__19_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__19_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__20_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " +typeChanged"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__20_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__20_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__21_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__20_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__21_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__21_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__22_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "+typeChanged"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__22_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__22_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__23_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__22_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__23_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__23_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__24_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__24_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__25_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__25_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 88, .m_capacity = 88, .m_length = 87, .m_data = "The `+typeChanged` marker is not needed because the updated constant has the same type."};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__27_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__27_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__27_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__28_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__28_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static const lean_array_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Deprecate in favor of `"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__36_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__36_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__37_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "` instead:"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__37_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__37_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__38_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__38_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__39_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "This warning can be disabled with `set_option "};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__39_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__39_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__40_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__40_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " false`"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = "` is itself deprecated, but without an explicit replacement; `"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__47_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "` is being deprecated in favor of a deprecated declaration"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__47_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__47_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__48_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__48_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__49_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "` is itself deprecated in favor of `"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__49_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__49_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__50_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__50_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__51_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "`; consider deprecating `"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__51_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__51_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__52_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__52_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__53_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "` in favor of `"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__53_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__53_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__54_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__54_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__55_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` instead"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__55_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__55_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__56_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__56_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__57_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Invalid `[deprecated]` attribute: `"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__57_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__57_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__58_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__58_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__59_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "` cannot be deprecated in favor of itself"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__59_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__59_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__60_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__60_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "deprecatedAttr"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(85, 246, 23, 143, 159, 138, 155, 162)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(78, 182, 79, 155, 204, 118, 39, 140)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "mark declaration as deprecated"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__17(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__17___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Linter_checkDeprecated___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48___closed__0_value)}};
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
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate_spec__1(lean_object* v_a_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = lean_nat_to_int(v_a_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate_spec__2(lean_object* v_a_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = l_Rat_ofInt(v_a_89_);
return v___x_90_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___lam__0___closed__0(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = lean_unsigned_to_nat(1000000000u);
v___x_92_ = lean_nat_to_int(v___x_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___lam__0(lean_object* v_tz_93_, lean_object* v_a_94_, lean_object* v___x_95_, lean_object* v_x_96_){
_start:
{
lean_object* v_offset_97_; lean_object* v_second_98_; lean_object* v_nano_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v_nanos_103_; lean_object* v___x_104_; lean_object* v_nanos_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v_offset_97_ = lean_ctor_get(v_tz_93_, 0);
v_second_98_ = lean_ctor_get(v_a_94_, 0);
v_nano_99_ = lean_ctor_get(v_a_94_, 1);
v___x_100_ = lean_nat_to_int(v___x_95_);
v___x_101_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___lam__0___closed__0, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___lam__0___closed__0_once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___lam__0___closed__0);
v___x_102_ = lean_int_mul(v_second_98_, v___x_101_);
v_nanos_103_ = lean_int_add(v___x_102_, v_nano_99_);
lean_dec(v___x_102_);
v___x_104_ = lean_int_mul(v_offset_97_, v___x_101_);
v_nanos_105_ = lean_int_add(v___x_104_, v___x_100_);
lean_dec(v___x_100_);
lean_dec(v___x_104_);
v___x_106_ = lean_int_add(v_nanos_103_, v_nanos_105_);
lean_dec(v_nanos_105_);
lean_dec(v_nanos_103_);
v___x_107_ = l_Std_Time_Duration_ofNanoseconds(v___x_106_);
lean_dec(v___x_106_);
v___x_108_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___lam__0___boxed(lean_object* v_tz_109_, lean_object* v_a_110_, lean_object* v___x_111_, lean_object* v_x_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___lam__0(v_tz_109_, v_a_110_, v___x_111_, v_x_112_);
lean_dec_ref(v_a_110_);
lean_dec_ref(v_tz_109_);
return v_res_113_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__0(void){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_114_ = lean_unsigned_to_nat(0u);
v___x_115_ = lean_nat_to_int(v___x_114_);
return v___x_115_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__3(void){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_119_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__2));
v___x_120_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__0, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__0_once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__0);
v___x_121_ = l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone(v___x_120_, v___x_119_, v___x_119_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate(){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = lean_get_current_time();
if (lean_obj_tag(v___x_148_) == 0)
{
lean_object* v_a_149_; lean_object* v___x_150_; 
v_a_149_ = lean_ctor_get(v___x_148_, 0);
lean_inc(v_a_149_);
lean_dec_ref_known(v___x_148_, 1);
v___x_150_ = l_Std_Time_Database_defaultGetLocalZoneRules();
if (lean_obj_tag(v___x_150_) == 0)
{
lean_object* v_a_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_173_; 
v_a_151_ = lean_ctor_get(v___x_150_, 0);
v_isSharedCheck_173_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_173_ == 0)
{
v___x_153_ = v___x_150_;
v_isShared_154_ = v_isSharedCheck_173_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_a_151_);
lean_dec(v___x_150_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_173_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v_offset_157_; lean_object* v_second_158_; lean_object* v_nano_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v_nanos_163_; lean_object* v___x_164_; lean_object* v_nanos_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v_date_169_; lean_object* v___x_171_; 
v___x_155_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForTimestamp(v_a_151_, v_a_149_);
v___x_156_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v___x_155_);
lean_dec_ref(v___x_155_);
v_offset_157_ = lean_ctor_get(v___x_156_, 0);
lean_inc(v_offset_157_);
lean_dec_ref(v___x_156_);
v_second_158_ = lean_ctor_get(v_a_149_, 0);
lean_inc(v_second_158_);
v_nano_159_ = lean_ctor_get(v_a_149_, 1);
lean_inc(v_nano_159_);
lean_dec(v_a_149_);
v___x_160_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__0, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__0_once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__0);
v___x_161_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___lam__0___closed__0, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___lam__0___closed__0_once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___lam__0___closed__0);
v___x_162_ = lean_int_mul(v_second_158_, v___x_161_);
lean_dec(v_second_158_);
v_nanos_163_ = lean_int_add(v___x_162_, v_nano_159_);
lean_dec(v_nano_159_);
lean_dec(v___x_162_);
v___x_164_ = lean_int_mul(v_offset_157_, v___x_161_);
lean_dec(v_offset_157_);
v_nanos_165_ = lean_int_add(v___x_164_, v___x_160_);
lean_dec(v___x_164_);
v___x_166_ = lean_int_add(v_nanos_163_, v_nanos_165_);
lean_dec(v_nanos_165_);
lean_dec(v_nanos_163_);
v___x_167_ = l_Std_Time_Duration_ofNanoseconds(v___x_166_);
lean_dec(v___x_166_);
v___x_168_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_167_);
v_date_169_ = lean_ctor_get(v___x_168_, 0);
lean_inc_ref(v_date_169_);
lean_dec_ref(v___x_168_);
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 0, v_date_169_);
v___x_171_ = v___x_153_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v_date_169_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
else
{
lean_dec_ref_known(v___x_150_, 1);
lean_dec(v_a_149_);
goto v___jp_123_;
}
}
else
{
lean_dec_ref_known(v___x_148_, 1);
goto v___jp_123_;
}
v___jp_123_:
{
lean_object* v___x_124_; 
v___x_124_ = lean_get_current_time();
if (lean_obj_tag(v___x_124_) == 0)
{
lean_object* v_a_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_139_; 
v_a_125_ = lean_ctor_get(v___x_124_, 0);
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_139_ == 0)
{
v___x_127_ = v___x_124_;
v_isShared_128_ = v_isSharedCheck_139_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_a_125_);
lean_dec(v___x_124_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_139_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v_tz_131_; lean_object* v___f_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v_date_135_; lean_object* v___x_137_; 
v___x_129_ = lean_unsigned_to_nat(0u);
v___x_130_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__3, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__3_once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__3);
v_tz_131_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v___x_130_, v_a_125_);
v___f_132_ = lean_alloc_closure((void*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___lam__0___boxed), 4, 3);
lean_closure_set(v___f_132_, 0, v_tz_131_);
lean_closure_set(v___f_132_, 1, v_a_125_);
lean_closure_set(v___f_132_, 2, v___x_129_);
v___x_133_ = lean_mk_thunk(v___f_132_);
v___x_134_ = lean_thunk_get_own(v___x_133_);
lean_dec_ref(v___x_133_);
v_date_135_ = lean_ctor_get(v___x_134_, 0);
lean_inc_ref(v_date_135_);
lean_dec(v___x_134_);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 0, v_date_135_);
v___x_137_ = v___x_127_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_date_135_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
else
{
lean_object* v_a_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_147_; 
v_a_140_ = lean_ctor_get(v___x_124_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_147_ == 0)
{
v___x_142_ = v___x_124_;
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_a_140_);
lean_dec(v___x_124_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_145_; 
if (v_isShared_143_ == 0)
{
v___x_145_ = v___x_142_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_a_140_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___boxed(lean_object* v_a_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate();
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate_spec__0(lean_object* v_a_176_){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_177_ = lean_nat_to_int(v_a_176_);
v___x_178_ = l_Rat_ofInt(v___x_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_mkSinceHint___lam__0(lean_object* v___x_180_, lean_object* v_x_181_){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = ((lean_object*)(l_Lean_Linter_mkSinceHint___lam__0___closed__0));
v___x_183_ = lean_string_append(v___x_182_, v___x_180_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_mkSinceHint___lam__0___boxed(lean_object* v___x_184_, lean_object* v_x_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Lean_Linter_mkSinceHint___lam__0(v___x_184_, v_x_185_);
lean_dec_ref(v_x_185_);
lean_dec_ref(v___x_184_);
return v_res_186_;
}
}
static lean_object* _init_l_Lean_Linter_mkSinceHint___closed__4(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = ((lean_object*)(l_Lean_Linter_mkSinceHint___closed__3));
v___x_193_ = l_Lean_MessageData_ofFormat(v___x_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_mkSinceHint(lean_object* v_stx_195_, lean_object* v_a_196_, lean_object* v_a_197_){
_start:
{
uint8_t v___x_199_; lean_object* v___x_200_; 
v___x_199_ = 1;
v___x_200_ = l_Lean_Syntax_getTailPos_x3f(v_stx_195_, v___x_199_);
if (lean_obj_tag(v___x_200_) == 1)
{
lean_object* v_val_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_249_; 
v_val_201_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_249_ == 0)
{
v___x_203_ = v___x_200_;
v_isShared_204_ = v_isSharedCheck_249_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_val_201_);
lean_dec(v___x_200_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_249_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v_ref_205_; lean_object* v___x_206_; 
v_ref_205_ = lean_ctor_get(v_a_196_, 2);
v___x_206_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate();
if (lean_obj_tag(v___x_206_) == 0)
{
lean_object* v_a_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___f_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_222_; 
v_a_207_ = lean_ctor_get(v___x_206_, 0);
lean_inc(v_a_207_);
lean_dec_ref_known(v___x_206_, 1);
v___x_208_ = ((lean_object*)(l_Lean_Linter_mkSinceHint___closed__0));
v___x_209_ = l_Std_Time_PlainDate_toLeanDateString(v_a_207_);
v___x_210_ = lean_string_append(v___x_208_, v___x_209_);
lean_dec_ref(v___x_209_);
v___x_211_ = ((lean_object*)(l_Lean_Linter_mkSinceHint___closed__1));
v___x_212_ = lean_string_append(v___x_210_, v___x_211_);
lean_inc_ref(v___x_212_);
v___f_213_ = lean_alloc_closure((void*)(l_Lean_Linter_mkSinceHint___lam__0___boxed), 2, 1);
lean_closure_set(v___f_213_, 0, v___x_212_);
v___x_214_ = lean_obj_once(&l_Lean_Linter_mkSinceHint___closed__4, &l_Lean_Linter_mkSinceHint___closed__4_once, _init_l_Lean_Linter_mkSinceHint___closed__4);
v___x_215_ = ((lean_object*)(l_Lean_Linter_mkSinceHint___closed__5));
v___x_216_ = lean_string_append(v___x_215_, v___x_212_);
v___x_217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
v___x_218_ = lean_box(0);
v___x_219_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_219_, 0, v___x_212_);
v___x_220_ = l_Lean_MessageData_ofFormat(v___x_219_);
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 0, v___x_220_);
v___x_222_ = v___x_203_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v___x_220_);
v___x_222_ = v_reuseFailAlloc_236_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; uint8_t v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; uint8_t v___x_234_; lean_object* v___x_235_; 
v___x_223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_223_, 0, v___f_213_);
v___x_224_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_224_, 0, v___x_217_);
lean_ctor_set(v___x_224_, 1, v___x_218_);
lean_ctor_set(v___x_224_, 2, v___x_218_);
lean_ctor_set(v___x_224_, 3, v___x_218_);
lean_ctor_set(v___x_224_, 4, v___x_222_);
lean_ctor_set(v___x_224_, 5, v___x_223_);
lean_inc(v_val_201_);
v___x_225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_225_, 0, v_val_201_);
lean_ctor_set(v___x_225_, 1, v_val_201_);
v___x_226_ = l_Lean_Syntax_ofRange(v___x_225_, v___x_199_);
v___x_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
v___x_228_ = 4;
v___x_229_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_229_, 0, v___x_224_);
lean_ctor_set(v___x_229_, 1, v___x_227_);
lean_ctor_set(v___x_229_, 2, v___x_218_);
lean_ctor_set_uint8(v___x_229_, sizeof(void*)*3, v___x_228_);
v___x_230_ = lean_unsigned_to_nat(1u);
v___x_231_ = lean_mk_empty_array_with_capacity(v___x_230_);
v___x_232_ = lean_array_push(v___x_231_, v___x_229_);
v___x_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_233_, 0, v_stx_195_);
v___x_234_ = 0;
v___x_235_ = l_Lean_MessageData_hint(v___x_214_, v___x_232_, v___x_233_, v___x_218_, v___x_234_, v_a_196_, v_a_197_);
lean_dec_ref(v___x_232_);
return v___x_235_;
}
}
else
{
lean_object* v_a_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_248_; 
lean_del_object(v___x_203_);
lean_dec(v_val_201_);
lean_dec(v_stx_195_);
v_a_237_ = lean_ctor_get(v___x_206_, 0);
v_isSharedCheck_248_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_248_ == 0)
{
v___x_239_ = v___x_206_;
v_isShared_240_ = v_isSharedCheck_248_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_a_237_);
lean_dec(v___x_206_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_248_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_246_; 
v___x_241_ = lean_io_error_to_string(v_a_237_);
v___x_242_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
v___x_243_ = l_Lean_MessageData_ofFormat(v___x_242_);
lean_inc(v_ref_205_);
v___x_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_244_, 0, v_ref_205_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 0, v___x_244_);
v___x_246_ = v___x_239_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v___x_244_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
}
}
}
else
{
lean_object* v___x_250_; lean_object* v___x_251_; 
lean_dec(v___x_200_);
lean_dec(v_stx_195_);
v___x_250_ = l_Lean_MessageData_nil;
v___x_251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
return v___x_251_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_mkSinceHint___boxed(lean_object* v_stx_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Lean_Linter_mkSinceHint(v_stx_252_, v_a_253_, v_a_254_);
lean_dec(v_a_254_);
lean_dec_ref(v_a_253_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq_spec__0(lean_object* v_a_260_, lean_object* v_a_261_){
_start:
{
if (lean_obj_tag(v_a_260_) == 0)
{
lean_object* v___x_262_; 
v___x_262_ = lean_array_to_list(v_a_261_);
return v___x_262_;
}
else
{
lean_object* v_tail_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v_tail_263_ = lean_ctor_get(v_a_260_, 1);
v___x_264_ = lean_array_get_size(v_a_261_);
v___x_265_ = ((lean_object*)(l_List_mapIdx_go___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq_spec__0___closed__1));
v___x_266_ = l_Lean_Name_num___override(v___x_265_, v___x_264_);
v___x_267_ = l_Lean_mkLevelParam(v___x_266_);
v___x_268_ = lean_array_push(v_a_261_, v___x_267_);
v_a_260_ = v_tail_263_;
v_a_261_ = v___x_268_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq_spec__0___boxed(lean_object* v_a_270_, lean_object* v_a_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_List_mapIdx_go___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq_spec__0(v_a_270_, v_a_271_);
lean_dec(v_a_270_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq(lean_object* v_decl_u2081_275_, lean_object* v_decl_u2082_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_){
_start:
{
lean_object* v___y_283_; lean_object* v___x_300_; lean_object* v___x_301_; uint8_t v___x_302_; 
v___x_300_ = l_Lean_ConstantInfo_numLevelParams(v_decl_u2081_275_);
v___x_301_ = l_Lean_ConstantInfo_numLevelParams(v_decl_u2082_276_);
v___x_302_ = lean_nat_dec_eq(v___x_300_, v___x_301_);
lean_dec(v___x_301_);
lean_dec(v___x_300_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = lean_box(v___x_302_);
v___x_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
return v___x_304_;
}
else
{
lean_object* v___x_305_; uint8_t v_transparency_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v_levels_309_; lean_object* v_type_u2081_310_; lean_object* v_type_u2082_311_; uint8_t v___x_312_; uint8_t v___x_313_; 
v___x_305_ = l_Lean_Meta_Context_config(v_a_277_);
v_transparency_306_ = lean_ctor_get_uint8(v___x_305_, 9);
lean_dec_ref(v___x_305_);
v___x_307_ = l_Lean_ConstantInfo_levelParams(v_decl_u2081_275_);
v___x_308_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq___closed__0));
v_levels_309_ = l_List_mapIdx_go___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq_spec__0(v___x_307_, v___x_308_);
lean_dec(v___x_307_);
lean_inc(v_levels_309_);
v_type_u2081_310_ = l_Lean_ConstantInfo_instantiateTypeLevelParams(v_decl_u2081_275_, v_levels_309_);
v_type_u2082_311_ = l_Lean_ConstantInfo_instantiateTypeLevelParams(v_decl_u2082_276_, v_levels_309_);
v___x_312_ = 2;
v___x_313_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_306_, v___x_312_);
if (v___x_313_ == 0)
{
lean_object* v_keyedConfig_314_; uint8_t v_trackZetaDelta_315_; lean_object* v_zetaDeltaSet_316_; lean_object* v_lctx_317_; lean_object* v_localInstances_318_; lean_object* v_defEqCtx_x3f_319_; lean_object* v_synthPendingDepth_320_; lean_object* v_customCanUnfoldPredicate_x3f_321_; uint8_t v_univApprox_322_; uint8_t v_inTypeClassResolution_323_; uint8_t v_cacheInferType_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v_keyedConfig_314_ = lean_ctor_get(v_a_277_, 0);
v_trackZetaDelta_315_ = lean_ctor_get_uint8(v_a_277_, sizeof(void*)*7);
v_zetaDeltaSet_316_ = lean_ctor_get(v_a_277_, 1);
v_lctx_317_ = lean_ctor_get(v_a_277_, 2);
v_localInstances_318_ = lean_ctor_get(v_a_277_, 3);
v_defEqCtx_x3f_319_ = lean_ctor_get(v_a_277_, 4);
v_synthPendingDepth_320_ = lean_ctor_get(v_a_277_, 5);
v_customCanUnfoldPredicate_x3f_321_ = lean_ctor_get(v_a_277_, 6);
v_univApprox_322_ = lean_ctor_get_uint8(v_a_277_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_323_ = lean_ctor_get_uint8(v_a_277_, sizeof(void*)*7 + 2);
v_cacheInferType_324_ = lean_ctor_get_uint8(v_a_277_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_314_);
v___x_325_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_312_, v_keyedConfig_314_);
lean_inc(v_customCanUnfoldPredicate_x3f_321_);
lean_inc(v_synthPendingDepth_320_);
lean_inc(v_defEqCtx_x3f_319_);
lean_inc_ref(v_localInstances_318_);
lean_inc_ref(v_lctx_317_);
lean_inc(v_zetaDeltaSet_316_);
v___x_326_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_326_, 0, v___x_325_);
lean_ctor_set(v___x_326_, 1, v_zetaDeltaSet_316_);
lean_ctor_set(v___x_326_, 2, v_lctx_317_);
lean_ctor_set(v___x_326_, 3, v_localInstances_318_);
lean_ctor_set(v___x_326_, 4, v_defEqCtx_x3f_319_);
lean_ctor_set(v___x_326_, 5, v_synthPendingDepth_320_);
lean_ctor_set(v___x_326_, 6, v_customCanUnfoldPredicate_x3f_321_);
lean_ctor_set_uint8(v___x_326_, sizeof(void*)*7, v_trackZetaDelta_315_);
lean_ctor_set_uint8(v___x_326_, sizeof(void*)*7 + 1, v_univApprox_322_);
lean_ctor_set_uint8(v___x_326_, sizeof(void*)*7 + 2, v_inTypeClassResolution_323_);
lean_ctor_set_uint8(v___x_326_, sizeof(void*)*7 + 3, v_cacheInferType_324_);
v___x_327_ = l_Lean_Meta_isExprDefEqGuarded(v_type_u2081_310_, v_type_u2082_311_, v___x_326_, v_a_278_, v_a_279_, v_a_280_);
lean_dec_ref_known(v___x_326_, 7);
v___y_283_ = v___x_327_;
goto v___jp_282_;
}
else
{
lean_object* v___x_328_; 
v___x_328_ = l_Lean_Meta_isExprDefEqGuarded(v_type_u2081_310_, v_type_u2082_311_, v_a_277_, v_a_278_, v_a_279_, v_a_280_);
v___y_283_ = v___x_328_;
goto v___jp_282_;
}
}
v___jp_282_:
{
if (lean_obj_tag(v___y_283_) == 0)
{
lean_object* v_a_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_291_; 
v_a_284_ = lean_ctor_get(v___y_283_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___y_283_);
if (v_isSharedCheck_291_ == 0)
{
v___x_286_ = v___y_283_;
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_a_284_);
lean_dec(v___y_283_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_289_; 
if (v_isShared_287_ == 0)
{
v___x_289_ = v___x_286_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_a_284_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
else
{
lean_object* v_a_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_299_; 
v_a_292_ = lean_ctor_get(v___y_283_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v___y_283_);
if (v_isSharedCheck_299_ == 0)
{
v___x_294_ = v___y_283_;
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_a_292_);
lean_dec(v___y_283_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_297_; 
if (v_isShared_295_ == 0)
{
v___x_297_ = v___x_294_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_a_292_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq___boxed(lean_object* v_decl_u2081_329_, lean_object* v_decl_u2082_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq(v_decl_u2081_329_, v_decl_u2082_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_333_);
lean_dec(v_a_332_);
lean_dec_ref(v_a_331_);
lean_dec_ref(v_decl_u2082_330_);
lean_dec_ref(v_decl_u2081_329_);
return v_res_336_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4(lean_object* v_opts_337_, lean_object* v_opt_338_){
_start:
{
lean_object* v_name_339_; lean_object* v_defValue_340_; lean_object* v_map_341_; lean_object* v___x_342_; 
v_name_339_ = lean_ctor_get(v_opt_338_, 0);
v_defValue_340_ = lean_ctor_get(v_opt_338_, 1);
v_map_341_ = lean_ctor_get(v_opts_337_, 0);
v___x_342_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_341_, v_name_339_);
if (lean_obj_tag(v___x_342_) == 0)
{
uint8_t v___x_343_; 
v___x_343_ = lean_unbox(v_defValue_340_);
return v___x_343_;
}
else
{
lean_object* v_val_344_; 
v_val_344_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_val_344_);
lean_dec_ref_known(v___x_342_, 1);
if (lean_obj_tag(v_val_344_) == 1)
{
uint8_t v_v_345_; 
v_v_345_ = lean_ctor_get_uint8(v_val_344_, 0);
lean_dec_ref_known(v_val_344_, 0);
return v_v_345_;
}
else
{
uint8_t v___x_346_; 
lean_dec(v_val_344_);
v___x_346_ = lean_unbox(v_defValue_340_);
return v___x_346_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4___boxed(lean_object* v_opts_347_, lean_object* v_opt_348_){
_start:
{
uint8_t v_res_349_; lean_object* v_r_350_; 
v_res_349_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4(v_opts_347_, v_opt_348_);
lean_dec_ref(v_opt_348_);
lean_dec_ref(v_opts_347_);
v_r_350_ = lean_box(v_res_349_);
return v_r_350_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6(lean_object* v_x_351_, lean_object* v_x_352_){
_start:
{
if (lean_obj_tag(v_x_351_) == 0)
{
if (lean_obj_tag(v_x_352_) == 0)
{
uint8_t v___x_353_; 
v___x_353_ = 1;
return v___x_353_;
}
else
{
uint8_t v___x_354_; 
v___x_354_ = 0;
return v___x_354_;
}
}
else
{
if (lean_obj_tag(v_x_352_) == 0)
{
uint8_t v___x_355_; 
v___x_355_ = 0;
return v___x_355_;
}
else
{
lean_object* v_val_356_; lean_object* v_val_357_; uint8_t v___x_358_; 
v_val_356_ = lean_ctor_get(v_x_351_, 0);
v_val_357_ = lean_ctor_get(v_x_352_, 0);
v___x_358_ = lean_name_eq(v_val_356_, v_val_357_);
return v___x_358_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6___boxed(lean_object* v_x_359_, lean_object* v_x_360_){
_start:
{
uint8_t v_res_361_; lean_object* v_r_362_; 
v_res_361_ = l_instBEqOption_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6(v_x_359_, v_x_360_);
lean_dec(v_x_360_);
lean_dec(v_x_359_);
v_r_362_ = lean_box(v_res_361_);
return v_r_362_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(lean_object* v_env_363_, lean_object* v_n_364_, lean_object* v_x_365_){
_start:
{
uint8_t v___x_366_; uint8_t v___x_367_; 
v___x_366_ = 1;
v___x_367_ = l_Lean_Environment_contains(v_env_363_, v_n_364_, v___x_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2____boxed(lean_object* v_env_368_, lean_object* v_n_369_, lean_object* v_x_370_){
_start:
{
uint8_t v_res_371_; lean_object* v_r_372_; 
v_res_371_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(v_env_368_, v_n_369_, v_x_370_);
lean_dec_ref(v_x_370_);
v_r_372_ = lean_box(v_res_371_);
return v_r_372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(lean_object* v_x_374_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__0_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2____boxed(lean_object* v_x_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(v_x_376_);
lean_dec_ref(v_x_376_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(lean_object* v_x_378_, lean_object* v_x_379_, lean_object* v_x_380_, lean_object* v___y_381_){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = lean_box(0);
v___x_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2____boxed(lean_object* v_x_385_, lean_object* v_x_386_, lean_object* v_x_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(v_x_385_, v_x_386_, v_x_387_, v___y_388_);
lean_dec(v___y_388_);
lean_dec_ref(v_x_387_);
lean_dec_ref(v_x_386_);
lean_dec(v_x_385_);
return v_res_390_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0(uint8_t v_suppressElabErrors_399_, uint8_t v___y_400_, lean_object* v_x_401_){
_start:
{
if (lean_obj_tag(v_x_401_) == 1)
{
lean_object* v_pre_402_; 
v_pre_402_ = lean_ctor_get(v_x_401_, 0);
switch(lean_obj_tag(v_pre_402_))
{
case 1:
{
lean_object* v_pre_403_; 
v_pre_403_ = lean_ctor_get(v_pre_402_, 0);
switch(lean_obj_tag(v_pre_403_))
{
case 0:
{
lean_object* v_str_404_; lean_object* v_str_405_; lean_object* v___x_406_; uint8_t v___x_407_; 
v_str_404_ = lean_ctor_get(v_x_401_, 1);
v_str_405_ = lean_ctor_get(v_pre_402_, 1);
v___x_406_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__0));
v___x_407_ = lean_string_dec_eq(v_str_405_, v___x_406_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; uint8_t v___x_409_; 
v___x_408_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__1));
v___x_409_ = lean_string_dec_eq(v_str_405_, v___x_408_);
if (v___x_409_ == 0)
{
return v___x_409_;
}
else
{
lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_410_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__2));
v___x_411_ = lean_string_dec_eq(v_str_404_, v___x_410_);
if (v___x_411_ == 0)
{
return v___x_411_;
}
else
{
return v_suppressElabErrors_399_;
}
}
}
else
{
lean_object* v___x_412_; uint8_t v___x_413_; 
v___x_412_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__3));
v___x_413_ = lean_string_dec_eq(v_str_404_, v___x_412_);
if (v___x_413_ == 0)
{
return v___x_413_;
}
else
{
return v_suppressElabErrors_399_;
}
}
}
case 1:
{
lean_object* v_pre_414_; 
v_pre_414_ = lean_ctor_get(v_pre_403_, 0);
if (lean_obj_tag(v_pre_414_) == 0)
{
lean_object* v_str_415_; lean_object* v_str_416_; lean_object* v_str_417_; lean_object* v___x_418_; uint8_t v___x_419_; 
v_str_415_ = lean_ctor_get(v_x_401_, 1);
v_str_416_ = lean_ctor_get(v_pre_402_, 1);
v_str_417_ = lean_ctor_get(v_pre_403_, 1);
v___x_418_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__4));
v___x_419_ = lean_string_dec_eq(v_str_417_, v___x_418_);
if (v___x_419_ == 0)
{
return v___x_419_;
}
else
{
lean_object* v___x_420_; uint8_t v___x_421_; 
v___x_420_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__5));
v___x_421_ = lean_string_dec_eq(v_str_416_, v___x_420_);
if (v___x_421_ == 0)
{
return v___x_421_;
}
else
{
lean_object* v___x_422_; uint8_t v___x_423_; 
v___x_422_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__6));
v___x_423_ = lean_string_dec_eq(v_str_415_, v___x_422_);
if (v___x_423_ == 0)
{
return v___x_423_;
}
else
{
return v_suppressElabErrors_399_;
}
}
}
}
else
{
return v___y_400_;
}
}
default: 
{
return v___y_400_;
}
}
}
case 0:
{
lean_object* v_str_424_; lean_object* v___x_425_; uint8_t v___x_426_; 
v_str_424_ = lean_ctor_get(v_x_401_, 1);
v___x_425_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__7));
v___x_426_ = lean_string_dec_eq(v_str_424_, v___x_425_);
if (v___x_426_ == 0)
{
return v___x_426_;
}
else
{
return v_suppressElabErrors_399_;
}
}
default: 
{
return v___y_400_;
}
}
}
else
{
return v___y_400_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___boxed(lean_object* v_suppressElabErrors_427_, lean_object* v___y_428_, lean_object* v_x_429_){
_start:
{
uint8_t v_suppressElabErrors_boxed_430_; uint8_t v___y_43585__boxed_431_; uint8_t v_res_432_; lean_object* v_r_433_; 
v_suppressElabErrors_boxed_430_ = lean_unbox(v_suppressElabErrors_427_);
v___y_43585__boxed_431_ = lean_unbox(v___y_428_);
v_res_432_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0(v_suppressElabErrors_boxed_430_, v___y_43585__boxed_431_, v_x_429_);
lean_dec(v_x_429_);
v_r_433_ = lean_box(v_res_432_);
return v_r_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44_spec__47(lean_object* v_msgData_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
lean_object* v___x_440_; lean_object* v_env_441_; uint8_t v___x_442_; lean_object* v_env_443_; lean_object* v___x_444_; lean_object* v_toCold_445_; lean_object* v_mctx_446_; lean_object* v_lctx_447_; lean_object* v_options_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_440_ = lean_st_ref_get(v___y_438_);
v_env_441_ = lean_ctor_get(v___x_440_, 0);
lean_inc_ref(v_env_441_);
lean_dec(v___x_440_);
v___x_442_ = 0;
v_env_443_ = l_Lean_Environment_setRecordingDeps(v_env_441_, v___x_442_);
v___x_444_ = lean_st_ref_get(v___y_436_);
v_toCold_445_ = lean_ctor_get(v___y_437_, 0);
v_mctx_446_ = lean_ctor_get(v___x_444_, 0);
lean_inc_ref(v_mctx_446_);
lean_dec(v___x_444_);
v_lctx_447_ = lean_ctor_get(v___y_435_, 2);
v_options_448_ = lean_ctor_get(v_toCold_445_, 2);
lean_inc_ref(v_options_448_);
lean_inc_ref(v_lctx_447_);
v___x_449_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_449_, 0, v_env_443_);
lean_ctor_set(v___x_449_, 1, v_mctx_446_);
lean_ctor_set(v___x_449_, 2, v_lctx_447_);
lean_ctor_set(v___x_449_, 3, v_options_448_);
v___x_450_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_450_, 0, v___x_449_);
lean_ctor_set(v___x_450_, 1, v_msgData_434_);
v___x_451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_451_, 0, v___x_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44_spec__47___boxed(lean_object* v_msgData_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44_spec__47(v_msgData_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48(lean_object* v_ref_462_, lean_object* v_msgData_463_, uint8_t v_severity_464_, uint8_t v_isSilent_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
lean_object* v_a_472_; uint8_t v___y_476_; lean_object* v___y_477_; uint8_t v___y_478_; lean_object* v___y_479_; lean_object* v___y_480_; lean_object* v___y_481_; lean_object* v___y_482_; lean_object* v_toCold_483_; lean_object* v___y_484_; lean_object* v___y_512_; lean_object* v___y_513_; uint8_t v___y_514_; uint8_t v___y_515_; lean_object* v___y_516_; uint8_t v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; uint8_t v___y_538_; lean_object* v___y_539_; lean_object* v___y_540_; uint8_t v___y_541_; uint8_t v___y_542_; lean_object* v___y_543_; lean_object* v___y_544_; uint8_t v___y_548_; uint8_t v___y_549_; uint8_t v___y_550_; uint8_t v___x_561_; uint8_t v___y_563_; uint8_t v___y_564_; uint8_t v___y_565_; uint8_t v___y_567_; uint8_t v___x_575_; 
v___x_561_ = 2;
v___x_575_ = l_Lean_instBEqMessageSeverity_beq(v_severity_464_, v___x_561_);
if (v___x_575_ == 0)
{
v___y_567_ = v___x_575_;
goto v___jp_566_;
}
else
{
uint8_t v___x_576_; 
lean_inc_ref(v_msgData_463_);
v___x_576_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_463_);
v___y_567_ = v___x_576_;
goto v___jp_566_;
}
v___jp_471_:
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_473_, 0, v_a_472_);
v___x_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
return v___x_474_;
}
v___jp_475_:
{
lean_object* v_currNamespace_485_; lean_object* v_openDecls_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v_env_491_; lean_object* v_nextMacroScope_492_; lean_object* v_ngen_493_; lean_object* v_auxDeclNGen_494_; lean_object* v_traceState_495_; lean_object* v_cache_496_; lean_object* v_recordedDeps_497_; lean_object* v_messages_498_; lean_object* v_infoState_499_; lean_object* v_snapshotTasks_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_510_; 
v_currNamespace_485_ = lean_ctor_get(v_toCold_483_, 4);
v_openDecls_486_ = lean_ctor_get(v_toCold_483_, 5);
lean_inc(v_openDecls_486_);
lean_inc(v_currNamespace_485_);
v___x_487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_487_, 0, v_currNamespace_485_);
lean_ctor_set(v___x_487_, 1, v_openDecls_486_);
v___x_488_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
lean_ctor_set(v___x_488_, 1, v___y_477_);
lean_inc_ref(v___y_481_);
lean_inc_ref(v___y_480_);
v___x_489_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_489_, 0, v___y_480_);
lean_ctor_set(v___x_489_, 1, v___y_482_);
lean_ctor_set(v___x_489_, 2, v___y_479_);
lean_ctor_set(v___x_489_, 3, v___y_481_);
lean_ctor_set(v___x_489_, 4, v___x_488_);
lean_ctor_set_uint8(v___x_489_, sizeof(void*)*5, v___y_478_);
lean_ctor_set_uint8(v___x_489_, sizeof(void*)*5 + 1, v___y_476_);
lean_ctor_set_uint8(v___x_489_, sizeof(void*)*5 + 2, v_isSilent_465_);
v___x_490_ = lean_st_ref_take(v___y_484_);
v_env_491_ = lean_ctor_get(v___x_490_, 0);
v_nextMacroScope_492_ = lean_ctor_get(v___x_490_, 1);
v_ngen_493_ = lean_ctor_get(v___x_490_, 2);
v_auxDeclNGen_494_ = lean_ctor_get(v___x_490_, 3);
v_traceState_495_ = lean_ctor_get(v___x_490_, 4);
v_cache_496_ = lean_ctor_get(v___x_490_, 5);
v_recordedDeps_497_ = lean_ctor_get(v___x_490_, 6);
v_messages_498_ = lean_ctor_get(v___x_490_, 7);
v_infoState_499_ = lean_ctor_get(v___x_490_, 8);
v_snapshotTasks_500_ = lean_ctor_get(v___x_490_, 9);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_510_ == 0)
{
v___x_502_ = v___x_490_;
v_isShared_503_ = v_isSharedCheck_510_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_snapshotTasks_500_);
lean_inc(v_infoState_499_);
lean_inc(v_messages_498_);
lean_inc(v_recordedDeps_497_);
lean_inc(v_cache_496_);
lean_inc(v_traceState_495_);
lean_inc(v_auxDeclNGen_494_);
lean_inc(v_ngen_493_);
lean_inc(v_nextMacroScope_492_);
lean_inc(v_env_491_);
lean_dec(v___x_490_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_510_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_507_; 
v___x_504_ = lean_box(0);
v___x_505_ = l_Lean_MessageLog_add(v___x_489_, v_messages_498_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 7, v___x_505_);
v___x_507_ = v___x_502_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_env_491_);
lean_ctor_set(v_reuseFailAlloc_509_, 1, v_nextMacroScope_492_);
lean_ctor_set(v_reuseFailAlloc_509_, 2, v_ngen_493_);
lean_ctor_set(v_reuseFailAlloc_509_, 3, v_auxDeclNGen_494_);
lean_ctor_set(v_reuseFailAlloc_509_, 4, v_traceState_495_);
lean_ctor_set(v_reuseFailAlloc_509_, 5, v_cache_496_);
lean_ctor_set(v_reuseFailAlloc_509_, 6, v_recordedDeps_497_);
lean_ctor_set(v_reuseFailAlloc_509_, 7, v___x_505_);
lean_ctor_set(v_reuseFailAlloc_509_, 8, v_infoState_499_);
lean_ctor_set(v_reuseFailAlloc_509_, 9, v_snapshotTasks_500_);
v___x_507_ = v_reuseFailAlloc_509_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
lean_object* v___x_508_; 
v___x_508_ = lean_st_ref_put(v___y_484_, v___x_507_);
v_a_472_ = v___x_504_;
goto v___jp_471_;
}
}
}
v___jp_511_:
{
lean_object* v_fileName_520_; lean_object* v_fileMap_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_536_; 
v_fileName_520_ = lean_ctor_get(v___y_518_, 0);
v_fileMap_521_ = lean_ctor_get(v___y_518_, 1);
v___x_522_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_463_);
v___x_523_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44_spec__47(v___x_522_, v___y_466_, v___y_467_, v___y_468_, v___y_469_);
v_a_524_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_536_ == 0)
{
v___x_526_ = v___x_523_;
v_isShared_527_ = v_isSharedCheck_536_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v___x_523_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_536_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_531_; 
lean_inc_ref_n(v_fileMap_521_, 2);
v___x_528_ = l_Lean_FileMap_toPosition(v_fileMap_521_, v___y_516_);
lean_dec(v___y_516_);
v___x_529_ = l_Lean_FileMap_toPosition(v_fileMap_521_, v___y_519_);
lean_dec(v___y_519_);
if (v_isShared_527_ == 0)
{
lean_ctor_set_tag(v___x_526_, 1);
lean_ctor_set(v___x_526_, 0, v___x_529_);
v___x_531_ = v___x_526_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_529_);
v___x_531_ = v_reuseFailAlloc_535_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
lean_object* v___x_532_; 
v___x_532_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48___closed__0));
if (v___y_515_ == 0)
{
lean_dec_ref(v___y_512_);
v___y_476_ = v___y_514_;
v___y_477_ = v_a_524_;
v___y_478_ = v___y_517_;
v___y_479_ = v___x_531_;
v___y_480_ = v_fileName_520_;
v___y_481_ = v___x_532_;
v___y_482_ = v___x_528_;
v_toCold_483_ = v___y_513_;
v___y_484_ = v___y_469_;
goto v___jp_475_;
}
else
{
uint8_t v___x_533_; 
lean_inc(v_a_524_);
v___x_533_ = l_Lean_MessageData_hasTag(v___y_512_, v_a_524_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; 
lean_dec_ref(v___x_531_);
lean_dec_ref(v___x_528_);
lean_dec(v_a_524_);
v___x_534_ = lean_box(0);
v_a_472_ = v___x_534_;
goto v___jp_471_;
}
else
{
v___y_476_ = v___y_514_;
v___y_477_ = v_a_524_;
v___y_478_ = v___y_517_;
v___y_479_ = v___x_531_;
v___y_480_ = v_fileName_520_;
v___y_481_ = v___x_532_;
v___y_482_ = v___x_528_;
v_toCold_483_ = v___y_513_;
v___y_484_ = v___y_469_;
goto v___jp_475_;
}
}
}
}
}
v___jp_537_:
{
lean_object* v___x_545_; 
v___x_545_ = l_Lean_Syntax_getTailPos_x3f(v___y_543_, v___y_542_);
lean_dec(v___y_543_);
if (lean_obj_tag(v___x_545_) == 0)
{
lean_inc(v___y_544_);
v___y_512_ = v___y_539_;
v___y_513_ = v___y_540_;
v___y_514_ = v___y_541_;
v___y_515_ = v___y_538_;
v___y_516_ = v___y_544_;
v___y_517_ = v___y_542_;
v___y_518_ = v___y_540_;
v___y_519_ = v___y_544_;
goto v___jp_511_;
}
else
{
lean_object* v_val_546_; 
v_val_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_val_546_);
lean_dec_ref_known(v___x_545_, 1);
v___y_512_ = v___y_539_;
v___y_513_ = v___y_540_;
v___y_514_ = v___y_541_;
v___y_515_ = v___y_538_;
v___y_516_ = v___y_544_;
v___y_517_ = v___y_542_;
v___y_518_ = v___y_540_;
v___y_519_ = v_val_546_;
goto v___jp_511_;
}
}
v___jp_547_:
{
lean_object* v_toCold_551_; lean_object* v_ref_552_; uint8_t v_suppressElabErrors_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___f_556_; lean_object* v_ref_557_; lean_object* v___x_558_; 
v_toCold_551_ = lean_ctor_get(v___y_468_, 0);
v_ref_552_ = lean_ctor_get(v___y_468_, 2);
v_suppressElabErrors_553_ = lean_ctor_get_uint8(v___y_468_, sizeof(void*)*3 + 2);
v___x_554_ = lean_box(v_suppressElabErrors_553_);
v___x_555_ = lean_box(v___y_548_);
v___f_556_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___boxed), 3, 2);
lean_closure_set(v___f_556_, 0, v___x_554_);
lean_closure_set(v___f_556_, 1, v___x_555_);
v_ref_557_ = l_Lean_replaceRef(v_ref_462_, v_ref_552_);
v___x_558_ = l_Lean_Syntax_getPos_x3f(v_ref_557_, v___y_549_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v___x_559_; 
v___x_559_ = lean_unsigned_to_nat(0u);
v___y_538_ = v_suppressElabErrors_553_;
v___y_539_ = v___f_556_;
v___y_540_ = v_toCold_551_;
v___y_541_ = v___y_550_;
v___y_542_ = v___y_549_;
v___y_543_ = v_ref_557_;
v___y_544_ = v___x_559_;
goto v___jp_537_;
}
else
{
lean_object* v_val_560_; 
v_val_560_ = lean_ctor_get(v___x_558_, 0);
lean_inc(v_val_560_);
lean_dec_ref_known(v___x_558_, 1);
v___y_538_ = v_suppressElabErrors_553_;
v___y_539_ = v___f_556_;
v___y_540_ = v_toCold_551_;
v___y_541_ = v___y_550_;
v___y_542_ = v___y_549_;
v___y_543_ = v_ref_557_;
v___y_544_ = v_val_560_;
goto v___jp_537_;
}
}
v___jp_562_:
{
if (v___y_565_ == 0)
{
v___y_548_ = v___y_563_;
v___y_549_ = v___y_564_;
v___y_550_ = v_severity_464_;
goto v___jp_547_;
}
else
{
v___y_548_ = v___y_563_;
v___y_549_ = v___y_564_;
v___y_550_ = v___x_561_;
goto v___jp_547_;
}
}
v___jp_566_:
{
if (v___y_567_ == 0)
{
uint8_t v___x_568_; uint8_t v___x_569_; 
v___x_568_ = 1;
v___x_569_ = l_Lean_instBEqMessageSeverity_beq(v_severity_464_, v___x_568_);
if (v___x_569_ == 0)
{
v___y_563_ = v___y_567_;
v___y_564_ = v___y_567_;
v___y_565_ = v___x_569_;
goto v___jp_562_;
}
else
{
lean_object* v___x_570_; lean_object* v___x_571_; uint8_t v___x_572_; 
v___x_570_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_468_);
v___x_571_ = l_Lean_warningAsError;
v___x_572_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4(v___x_570_, v___x_571_);
lean_dec_ref(v___x_570_);
v___y_563_ = v___y_567_;
v___y_564_ = v___y_567_;
v___y_565_ = v___x_572_;
goto v___jp_562_;
}
}
else
{
lean_object* v___x_573_; lean_object* v___x_574_; 
lean_dec_ref(v_msgData_463_);
v___x_573_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48___closed__1));
v___x_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
return v___x_574_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48___boxed(lean_object* v_ref_577_, lean_object* v_msgData_578_, lean_object* v_severity_579_, lean_object* v_isSilent_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
uint8_t v_severity_boxed_586_; uint8_t v_isSilent_boxed_587_; lean_object* v_res_588_; 
v_severity_boxed_586_ = lean_unbox(v_severity_579_);
v_isSilent_boxed_587_ = lean_unbox(v_isSilent_580_);
v_res_588_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48(v_ref_577_, v_msgData_578_, v_severity_boxed_586_, v_isSilent_boxed_587_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_581_);
lean_dec(v_ref_577_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46(lean_object* v_msgData_589_, uint8_t v_severity_590_, uint8_t v_isSilent_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
lean_object* v_ref_597_; lean_object* v___x_598_; 
v_ref_597_ = lean_ctor_get(v___y_594_, 2);
v___x_598_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48(v_ref_597_, v_msgData_589_, v_severity_590_, v_isSilent_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46___boxed(lean_object* v_msgData_599_, lean_object* v_severity_600_, lean_object* v_isSilent_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
uint8_t v_severity_boxed_607_; uint8_t v_isSilent_boxed_608_; lean_object* v_res_609_; 
v_severity_boxed_607_ = lean_unbox(v_severity_600_);
v_isSilent_boxed_608_ = lean_unbox(v_isSilent_601_);
v_res_609_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46(v_msgData_599_, v_severity_boxed_607_, v_isSilent_boxed_608_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44(lean_object* v_msgData_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
uint8_t v___x_616_; uint8_t v___x_617_; lean_object* v___x_618_; 
v___x_616_ = 1;
v___x_617_ = 0;
v___x_618_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46(v_msgData_610_, v___x_616_, v___x_617_, v___y_611_, v___y_612_, v___y_613_, v___y_614_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44___boxed(lean_object* v_msgData_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44(v_msgData_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43___redArg(lean_object* v_opt_626_, lean_object* v___y_627_){
_start:
{
lean_object* v___x_629_; uint8_t v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_629_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_627_);
v___x_630_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4(v___x_629_, v_opt_626_);
lean_dec_ref(v___x_629_);
v___x_631_ = lean_box(v___x_630_);
v___x_632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_632_, 0, v___x_631_);
v___x_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43___redArg___boxed(lean_object* v_opt_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43___redArg(v_opt_634_, v___y_635_);
lean_dec_ref(v___y_635_);
lean_dec_ref(v_opt_634_);
return v_res_637_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___closed__1(void){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___closed__0));
v___x_640_ = l_Lean_stringToMessageData(v___x_639_);
return v___x_640_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___closed__3(void){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___closed__2));
v___x_643_ = l_Lean_stringToMessageData(v___x_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40(lean_object* v_id_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_){
_start:
{
lean_object* v___x_650_; lean_object* v_env_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_674_; 
v___x_650_ = lean_st_ref_get(v___y_648_);
v_env_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc_ref(v_env_651_);
lean_dec(v___x_650_);
v___x_652_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_653_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43___redArg(v___x_652_, v___y_647_);
v_a_654_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_674_ == 0)
{
v___x_656_ = v___x_653_;
v_isShared_657_ = v_isSharedCheck_674_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_653_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_674_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
uint8_t v_isExporting_663_; 
v_isExporting_663_ = lean_ctor_get_uint8(v_env_651_, sizeof(void*)*13);
lean_dec_ref(v_env_651_);
if (v_isExporting_663_ == 0)
{
lean_dec(v_a_654_);
lean_dec(v_id_644_);
goto v___jp_658_;
}
else
{
lean_object* v_val_664_; uint8_t v___x_665_; 
v_val_664_ = lean_ctor_get(v_a_654_, 0);
lean_inc(v_val_664_);
lean_dec(v_a_654_);
v___x_665_ = l_Lean_isPrivateName(v_id_644_);
if (v___x_665_ == 0)
{
lean_dec(v_val_664_);
lean_dec(v_id_644_);
goto v___jp_658_;
}
else
{
uint8_t v___x_666_; 
v___x_666_ = lean_unbox(v_val_664_);
lean_dec(v_val_664_);
if (v___x_666_ == 0)
{
lean_dec(v_id_644_);
goto v___jp_658_;
}
else
{
lean_object* v___x_667_; uint8_t v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
lean_del_object(v___x_656_);
v___x_667_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___closed__1);
v___x_668_ = 0;
v___x_669_ = l_Lean_MessageData_ofConstName(v_id_644_, v___x_668_);
v___x_670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_670_, 0, v___x_667_);
lean_ctor_set(v___x_670_, 1, v___x_669_);
v___x_671_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___closed__3);
v___x_672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_672_, 0, v___x_670_);
lean_ctor_set(v___x_672_, 1, v___x_671_);
v___x_673_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44(v___x_672_, v___y_645_, v___y_646_, v___y_647_, v___y_648_);
return v___x_673_;
}
}
}
v___jp_658_:
{
lean_object* v___x_659_; lean_object* v___x_661_; 
v___x_659_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48___closed__1));
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v___x_659_);
v___x_661_ = v___x_656_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___boxed(lean_object* v_id_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40(v_id_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__31(lean_object* v_x_682_){
_start:
{
if (lean_obj_tag(v_x_682_) == 0)
{
lean_object* v___x_683_; 
v___x_683_ = lean_box(0);
return v___x_683_;
}
else
{
lean_object* v_head_684_; lean_object* v_tail_685_; lean_object* v_fst_686_; uint8_t v___x_687_; 
v_head_684_ = lean_ctor_get(v_x_682_, 0);
v_tail_685_ = lean_ctor_get(v_x_682_, 1);
v_fst_686_ = lean_ctor_get(v_head_684_, 0);
v___x_687_ = l_Lean_isPrivateName(v_fst_686_);
if (v___x_687_ == 0)
{
v_x_682_ = v_tail_685_;
goto _start;
}
else
{
lean_object* v___x_689_; 
lean_inc(v_head_684_);
v___x_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_689_, 0, v_head_684_);
return v___x_689_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__31___boxed(lean_object* v_x_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__31(v_x_690_);
lean_dec(v_x_690_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34(lean_object* v_id_692_, uint8_t v_enableLog_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
lean_object* v___x_699_; lean_object* v_toCold_700_; lean_object* v_env_701_; lean_object* v_currNamespace_702_; lean_object* v_openDecls_703_; lean_object* v___x_704_; lean_object* v_res_705_; lean_object* v___x_709_; 
v___x_699_ = lean_st_ref_get(v___y_697_);
v_toCold_700_ = lean_ctor_get(v___y_696_, 0);
v_env_701_ = lean_ctor_get(v___x_699_, 0);
lean_inc_ref(v_env_701_);
lean_dec(v___x_699_);
v_currNamespace_702_ = lean_ctor_get(v_toCold_700_, 4);
v_openDecls_703_ = lean_ctor_get(v_toCold_700_, 5);
v___x_704_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_696_);
lean_inc(v_openDecls_703_);
lean_inc(v_currNamespace_702_);
v_res_705_ = l_Lean_ResolveName_resolveGlobalName(v_env_701_, v___x_704_, v_currNamespace_702_, v_openDecls_703_, v_id_692_);
lean_dec_ref(v___x_704_);
v___x_709_ = lean_st_ref_get(v___y_697_);
if (v_enableLog_693_ == 0)
{
lean_dec(v___x_709_);
goto v___jp_706_;
}
else
{
lean_object* v_env_710_; uint8_t v_isExporting_711_; 
v_env_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc_ref(v_env_710_);
lean_dec(v___x_709_);
v_isExporting_711_ = lean_ctor_get_uint8(v_env_710_, sizeof(void*)*13);
lean_dec_ref(v_env_710_);
if (v_isExporting_711_ == 0)
{
goto v___jp_706_;
}
else
{
lean_object* v___x_712_; 
v___x_712_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__31(v_res_705_);
if (lean_obj_tag(v___x_712_) == 1)
{
lean_object* v_val_713_; lean_object* v_fst_714_; lean_object* v___x_715_; 
v_val_713_ = lean_ctor_get(v___x_712_, 0);
lean_inc(v_val_713_);
lean_dec_ref_known(v___x_712_, 1);
v_fst_714_ = lean_ctor_get(v_val_713_, 0);
lean_inc(v_fst_714_);
lean_dec(v_val_713_);
v___x_715_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40(v_fst_714_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_724_; 
v_a_716_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_724_ == 0)
{
v___x_718_ = v___x_715_;
v_isShared_719_ = v_isSharedCheck_724_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v___x_715_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_724_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
if (lean_obj_tag(v_a_716_) == 0)
{
lean_object* v___x_720_; lean_object* v___x_722_; 
lean_dec(v_res_705_);
v___x_720_ = lean_box(0);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 0, v___x_720_);
v___x_722_ = v___x_718_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_720_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
else
{
lean_dec_ref_known(v_a_716_, 1);
lean_del_object(v___x_718_);
goto v___jp_706_;
}
}
}
else
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
lean_dec(v_res_705_);
v_a_725_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_715_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_715_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
else
{
lean_dec(v___x_712_);
goto v___jp_706_;
}
}
}
v___jp_706_:
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_707_, 0, v_res_705_);
v___x_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_708_, 0, v___x_707_);
return v___x_708_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34___boxed(lean_object* v_id_733_, lean_object* v_enableLog_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
uint8_t v_enableLog_boxed_740_; lean_object* v_res_741_; 
v_enableLog_boxed_740_ = lean_unbox(v_enableLog_734_);
v_res_741_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34(v_id_733_, v_enableLog_boxed_740_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22___lam__0(lean_object* v___x_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_748_, 0, v___x_742_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22___lam__0___boxed(lean_object* v___x_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22___lam__0(v___x_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25(lean_object* v_n_u2080_760_, lean_object* v_filter_761_, lean_object* v_view_x3f_762_, lean_object* v_n_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v___y_773_; lean_object* v___y_774_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v___y_839_; 
if (lean_obj_tag(v_view_x3f_762_) == 1)
{
lean_object* v_val_866_; lean_object* v_imported_867_; lean_object* v_ctx_868_; lean_object* v_scopes_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_877_; 
v_val_866_ = lean_ctor_get(v_view_x3f_762_, 0);
lean_inc(v_val_866_);
lean_dec_ref_known(v_view_x3f_762_, 1);
v_imported_867_ = lean_ctor_get(v_val_866_, 1);
v_ctx_868_ = lean_ctor_get(v_val_866_, 2);
v_scopes_869_ = lean_ctor_get(v_val_866_, 3);
v_isSharedCheck_877_ = !lean_is_exclusive(v_val_866_);
if (v_isSharedCheck_877_ == 0)
{
lean_object* v_unused_878_; 
v_unused_878_ = lean_ctor_get(v_val_866_, 0);
lean_dec(v_unused_878_);
v___x_871_ = v_val_866_;
v_isShared_872_ = v_isSharedCheck_877_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_scopes_869_);
lean_inc(v_ctx_868_);
lean_inc(v_imported_867_);
lean_dec(v_val_866_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_877_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_874_; 
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 0, v_n_763_);
v___x_874_ = v___x_871_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_n_763_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v_imported_867_);
lean_ctor_set(v_reuseFailAlloc_876_, 2, v_ctx_868_);
lean_ctor_set(v_reuseFailAlloc_876_, 3, v_scopes_869_);
v___x_874_ = v_reuseFailAlloc_876_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
lean_object* v___x_875_; 
v___x_875_ = l_Lean_MacroScopesView_review(v___x_874_);
v___y_839_ = v___x_875_;
goto v___jp_838_;
}
}
}
else
{
lean_dec(v_view_x3f_762_);
v___y_839_ = v_n_763_;
goto v___jp_838_;
}
v___jp_769_:
{
lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_770_ = lean_box(0);
v___x_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_771_, 0, v___x_770_);
return v___x_771_;
}
v___jp_772_:
{
lean_object* v___x_775_; 
lean_inc_ref(v___y_774_);
lean_inc(v___y_767_);
lean_inc_ref(v___y_766_);
lean_inc(v___y_765_);
lean_inc_ref(v___y_764_);
v___x_775_ = lean_apply_5(v___y_774_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, lean_box(0));
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_795_; 
v_a_776_ = lean_ctor_get(v___x_775_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_795_ == 0)
{
v___x_778_ = v___x_775_;
v_isShared_779_ = v_isSharedCheck_795_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_775_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_795_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
if (lean_obj_tag(v_a_776_) == 0)
{
lean_object* v___x_780_; lean_object* v___x_782_; 
lean_dec(v___y_773_);
v___x_780_ = lean_box(0);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 0, v___x_780_);
v___x_782_ = v___x_778_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_780_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
else
{
lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_793_; 
v_isSharedCheck_793_ = !lean_is_exclusive(v_a_776_);
if (v_isSharedCheck_793_ == 0)
{
lean_object* v_unused_794_; 
v_unused_794_ = lean_ctor_get(v_a_776_, 0);
lean_dec(v_unused_794_);
v___x_785_ = v_a_776_;
v_isShared_786_ = v_isSharedCheck_793_;
goto v_resetjp_784_;
}
else
{
lean_dec(v_a_776_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_793_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 0, v___y_773_);
v___x_788_ = v___x_785_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___y_773_);
v___x_788_ = v_reuseFailAlloc_792_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
lean_object* v___x_790_; 
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 0, v___x_788_);
v___x_790_ = v___x_778_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_788_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
}
}
}
else
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
lean_dec(v___y_773_);
v_a_796_ = lean_ctor_get(v___x_775_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___x_775_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_775_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
v___jp_804_:
{
lean_object* v___x_807_; 
lean_inc_ref(v___y_806_);
lean_inc(v___y_767_);
lean_inc_ref(v___y_766_);
lean_inc(v___y_765_);
lean_inc_ref(v___y_764_);
v___x_807_ = lean_apply_5(v___y_806_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, lean_box(0));
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_829_; 
v_a_808_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_829_ == 0)
{
v___x_810_ = v___x_807_;
v_isShared_811_ = v_isSharedCheck_829_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_807_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_829_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
if (lean_obj_tag(v_a_808_) == 0)
{
lean_object* v___x_812_; lean_object* v___x_814_; 
lean_dec(v___y_805_);
lean_dec_ref(v_filter_761_);
v___x_812_ = lean_box(0);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 0, v___x_812_);
v___x_814_ = v___x_810_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v___x_812_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
else
{
lean_object* v___x_816_; 
lean_dec_ref_known(v_a_808_, 1);
lean_del_object(v___x_810_);
lean_inc(v___y_767_);
lean_inc_ref(v___y_766_);
lean_inc(v___y_765_);
lean_inc_ref(v___y_764_);
lean_inc(v___y_805_);
v___x_816_ = lean_apply_6(v_filter_761_, v___y_805_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, lean_box(0));
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v_a_817_; uint8_t v___x_818_; 
v_a_817_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_a_817_);
lean_dec_ref_known(v___x_816_, 1);
v___x_818_ = lean_unbox(v_a_817_);
lean_dec(v_a_817_);
if (v___x_818_ == 0)
{
lean_object* v___f_819_; 
v___f_819_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__0));
v___y_773_ = v___y_805_;
v___y_774_ = v___f_819_;
goto v___jp_772_;
}
else
{
lean_object* v___f_820_; 
v___f_820_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__1));
v___y_773_ = v___y_805_;
v___y_774_ = v___f_820_;
goto v___jp_772_;
}
}
else
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_828_; 
lean_dec(v___y_805_);
v_a_821_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_828_ == 0)
{
v___x_823_ = v___x_816_;
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_816_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_826_; 
if (v_isShared_824_ == 0)
{
v___x_826_ = v___x_823_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_a_821_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
}
}
else
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
lean_dec(v___y_805_);
lean_dec_ref(v_filter_761_);
v_a_830_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_807_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_807_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_a_830_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
v___jp_838_:
{
uint8_t v___x_840_; lean_object* v___x_841_; 
v___x_840_ = 0;
lean_inc(v___y_839_);
v___x_841_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34(v___y_839_, v___x_840_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_857_; 
v_a_842_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_857_ == 0)
{
v___x_844_ = v___x_841_;
v_isShared_845_ = v_isSharedCheck_857_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_841_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_857_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
if (lean_obj_tag(v_a_842_) == 0)
{
lean_object* v___x_846_; lean_object* v___x_848_; 
lean_dec(v___y_839_);
lean_dec_ref(v_filter_761_);
v___x_846_ = lean_box(0);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 0, v___x_846_);
v___x_848_ = v___x_844_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v___x_846_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
else
{
lean_object* v_val_850_; 
lean_del_object(v___x_844_);
v_val_850_ = lean_ctor_get(v_a_842_, 0);
lean_inc(v_val_850_);
lean_dec_ref_known(v_a_842_, 1);
if (lean_obj_tag(v_val_850_) == 1)
{
lean_object* v_head_851_; lean_object* v_tail_852_; 
v_head_851_ = lean_ctor_get(v_val_850_, 0);
lean_inc(v_head_851_);
v_tail_852_ = lean_ctor_get(v_val_850_, 1);
lean_inc(v_tail_852_);
lean_dec_ref_known(v_val_850_, 2);
if (lean_obj_tag(v_tail_852_) == 0)
{
lean_object* v_fst_853_; uint8_t v___x_854_; 
v_fst_853_ = lean_ctor_get(v_head_851_, 0);
lean_inc(v_fst_853_);
lean_dec(v_head_851_);
v___x_854_ = lean_name_eq(v_fst_853_, v_n_u2080_760_);
lean_dec(v_fst_853_);
if (v___x_854_ == 0)
{
lean_object* v___f_855_; 
v___f_855_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__0));
v___y_805_ = v___y_839_;
v___y_806_ = v___f_855_;
goto v___jp_804_;
}
else
{
lean_object* v___f_856_; 
v___f_856_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__1));
v___y_805_ = v___y_839_;
v___y_806_ = v___f_856_;
goto v___jp_804_;
}
}
else
{
lean_dec(v_tail_852_);
lean_dec(v_head_851_);
lean_dec(v___y_839_);
lean_dec_ref(v_filter_761_);
goto v___jp_769_;
}
}
else
{
lean_dec(v_val_850_);
lean_dec(v___y_839_);
lean_dec_ref(v_filter_761_);
goto v___jp_769_;
}
}
}
}
else
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_865_; 
lean_dec(v___y_839_);
lean_dec_ref(v_filter_761_);
v_a_858_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_865_ == 0)
{
v___x_860_ = v___x_841_;
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_841_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
if (v_isShared_861_ == 0)
{
v___x_863_ = v___x_860_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_858_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25___boxed(lean_object* v_n_u2080_879_, lean_object* v_filter_880_, lean_object* v_view_x3f_881_, lean_object* v_n_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25(v_n_u2080_879_, v_filter_880_, v_view_x3f_881_, v_n_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
lean_dec(v_n_u2080_879_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30___redArg(lean_object* v_n_u2080_889_, lean_object* v_filter_890_, lean_object* v_view_x3f_891_, lean_object* v_as_x27_892_, lean_object* v_b_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
if (lean_obj_tag(v_as_x27_892_) == 0)
{
lean_object* v___x_899_; lean_object* v___x_900_; 
lean_dec(v_view_x3f_891_);
lean_dec_ref(v_filter_890_);
v___x_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_899_, 0, v_b_893_);
v___x_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
return v___x_900_;
}
else
{
lean_object* v_head_901_; lean_object* v_tail_902_; lean_object* v_snd_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_941_; 
v_head_901_ = lean_ctor_get(v_as_x27_892_, 0);
v_tail_902_ = lean_ctor_get(v_as_x27_892_, 1);
v_snd_903_ = lean_ctor_get(v_b_893_, 1);
v_isSharedCheck_941_ = !lean_is_exclusive(v_b_893_);
if (v_isSharedCheck_941_ == 0)
{
lean_object* v_unused_942_; 
v_unused_942_ = lean_ctor_get(v_b_893_, 0);
lean_dec(v_unused_942_);
v___x_905_ = v_b_893_;
v_isShared_906_ = v_isSharedCheck_941_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_snd_903_);
lean_dec(v_b_893_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_941_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_907_ = lean_box(0);
v___x_908_ = l_Lean_Name_appendCore(v_head_901_, v_snd_903_);
lean_inc(v___x_908_);
lean_inc(v_view_x3f_891_);
lean_inc_ref(v_filter_890_);
v___x_909_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25(v_n_u2080_889_, v_filter_890_, v_view_x3f_891_, v___x_908_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_932_; 
v_a_910_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_932_ == 0)
{
v___x_912_ = v___x_909_;
v_isShared_913_ = v_isSharedCheck_932_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_909_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_932_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
if (lean_obj_tag(v_a_910_) == 0)
{
lean_object* v___x_915_; 
lean_del_object(v___x_912_);
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 1, v___x_908_);
lean_ctor_set(v___x_905_, 0, v___x_907_);
v___x_915_ = v___x_905_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v___x_907_);
lean_ctor_set(v_reuseFailAlloc_917_, 1, v___x_908_);
v___x_915_ = v_reuseFailAlloc_917_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
v_as_x27_892_ = v_tail_902_;
v_b_893_ = v___x_915_;
goto _start;
}
}
else
{
lean_object* v___x_919_; 
lean_dec(v_view_x3f_891_);
lean_dec_ref(v_filter_890_);
lean_inc_ref(v_a_910_);
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 1, v___x_908_);
lean_ctor_set(v___x_905_, 0, v_a_910_);
v___x_919_ = v___x_905_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_910_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v___x_908_);
v___x_919_ = v_reuseFailAlloc_931_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_929_; 
v_isSharedCheck_929_ = !lean_is_exclusive(v_a_910_);
if (v_isSharedCheck_929_ == 0)
{
lean_object* v_unused_930_; 
v_unused_930_ = lean_ctor_get(v_a_910_, 0);
lean_dec(v_unused_930_);
v___x_921_ = v_a_910_;
v_isShared_922_ = v_isSharedCheck_929_;
goto v_resetjp_920_;
}
else
{
lean_dec(v_a_910_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_929_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_924_; 
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 0, v___x_919_);
v___x_924_ = v___x_921_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v___x_919_);
v___x_924_ = v_reuseFailAlloc_928_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
lean_object* v___x_926_; 
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 0, v___x_924_);
v___x_926_ = v___x_912_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v___x_924_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_940_; 
lean_dec(v___x_908_);
lean_del_object(v___x_905_);
lean_dec(v_view_x3f_891_);
lean_dec_ref(v_filter_890_);
v_a_933_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_940_ == 0)
{
v___x_935_ = v___x_909_;
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v___x_909_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_938_; 
if (v_isShared_936_ == 0)
{
v___x_938_ = v___x_935_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_a_933_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30___redArg___boxed(lean_object* v_n_u2080_943_, lean_object* v_filter_944_, lean_object* v_view_x3f_945_, lean_object* v_as_x27_946_, lean_object* v_b_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30___redArg(v_n_u2080_943_, v_filter_944_, v_view_x3f_945_, v_as_x27_946_, v_b_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v_as_x27_946_);
lean_dec(v_n_u2080_943_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22(lean_object* v_n_u2080_957_, lean_object* v_filter_958_, lean_object* v_view_x3f_959_, lean_object* v_n_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v___y_967_; uint8_t v___x_1008_; 
v___x_1008_ = l_Lean_Name_hasMacroScopes(v_n_960_);
if (v___x_1008_ == 0)
{
lean_object* v___f_1009_; 
v___f_1009_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__1));
v___y_967_ = v___f_1009_;
goto v___jp_966_;
}
else
{
lean_object* v___f_1010_; 
v___f_1010_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__0));
v___y_967_ = v___f_1010_;
goto v___jp_966_;
}
v___jp_966_:
{
lean_object* v___x_968_; 
lean_inc_ref(v___y_967_);
lean_inc(v___y_964_);
lean_inc_ref(v___y_963_);
lean_inc(v___y_962_);
lean_inc_ref(v___y_961_);
v___x_968_ = lean_apply_5(v___y_967_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, lean_box(0));
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_999_; 
v_a_969_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_999_ == 0)
{
v___x_971_ = v___x_968_;
v_isShared_972_ = v_isSharedCheck_999_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_968_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_999_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
if (lean_obj_tag(v_a_969_) == 0)
{
lean_object* v___x_973_; lean_object* v___x_975_; 
lean_dec(v_n_960_);
lean_dec(v_view_x3f_959_);
lean_dec_ref(v_filter_958_);
v___x_973_ = lean_box(0);
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 0, v___x_973_);
v___x_975_ = v___x_971_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_973_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
else
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
lean_dec_ref_known(v_a_969_, 1);
lean_del_object(v___x_971_);
v___x_977_ = l_Lean_privateToUserName(v_n_960_);
v___x_978_ = l_Lean_Name_componentsRev(v___x_977_);
v___x_979_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22___closed__0));
v___x_980_ = l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30___redArg(v_n_u2080_957_, v_filter_958_, v_view_x3f_959_, v___x_978_, v___x_979_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
lean_dec(v___x_978_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_990_; 
v_a_981_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_990_ == 0)
{
v___x_983_ = v___x_980_;
v_isShared_984_ = v_isSharedCheck_990_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v___x_980_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_990_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v_val_985_; lean_object* v_fst_986_; lean_object* v___x_988_; 
v_val_985_ = lean_ctor_get(v_a_981_, 0);
lean_inc(v_val_985_);
lean_dec(v_a_981_);
v_fst_986_ = lean_ctor_get(v_val_985_, 0);
lean_inc(v_fst_986_);
lean_dec(v_val_985_);
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 0, v_fst_986_);
v___x_988_ = v___x_983_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_fst_986_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
v_a_991_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_980_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_980_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
}
}
else
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
lean_dec(v_n_960_);
lean_dec(v_view_x3f_959_);
lean_dec_ref(v_filter_958_);
v_a_1000_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1002_ = v___x_968_;
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_968_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1005_; 
if (v_isShared_1003_ == 0)
{
v___x_1005_ = v___x_1002_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_a_1000_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22___boxed(lean_object* v_n_u2080_1011_, lean_object* v_filter_1012_, lean_object* v_view_x3f_1013_, lean_object* v_n_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22(v_n_u2080_1011_, v_filter_1012_, v_view_x3f_1013_, v_n_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec(v_n_u2080_1011_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__23(lean_object* v_n_u2080_1021_, lean_object* v_filter_1022_, lean_object* v_as_1023_, lean_object* v_i_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v___x_1030_; uint8_t v___x_1031_; 
v___x_1030_ = lean_array_get_size(v_as_1023_);
v___x_1031_ = lean_nat_dec_lt(v_i_1024_, v___x_1030_);
if (v___x_1031_ == 0)
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
lean_dec(v_i_1024_);
lean_dec_ref(v_filter_1022_);
v___x_1032_ = lean_box(0);
v___x_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1032_);
return v___x_1033_;
}
else
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1034_ = lean_box(0);
v___x_1035_ = lean_array_fget_borrowed(v_as_1023_, v_i_1024_);
lean_inc(v___x_1035_);
lean_inc_ref(v_filter_1022_);
v___x_1036_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22(v_n_u2080_1021_, v_filter_1022_, v___x_1034_, v___x_1035_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v_a_1037_; 
v_a_1037_ = lean_ctor_get(v___x_1036_, 0);
if (lean_obj_tag(v_a_1037_) == 0)
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
lean_dec_ref_known(v___x_1036_, 1);
v___x_1038_ = lean_unsigned_to_nat(1u);
v___x_1039_ = lean_nat_add(v_i_1024_, v___x_1038_);
lean_dec(v_i_1024_);
v_i_1024_ = v___x_1039_;
goto _start;
}
else
{
lean_dec(v_i_1024_);
lean_dec_ref(v_filter_1022_);
return v___x_1036_;
}
}
else
{
lean_dec(v_i_1024_);
lean_dec_ref(v_filter_1022_);
return v___x_1036_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__23___boxed(lean_object* v_n_u2080_1041_, lean_object* v_filter_1042_, lean_object* v_as_1043_, lean_object* v_i_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__23(v_n_u2080_1041_, v_filter_1042_, v_as_1043_, v_i_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
lean_dec_ref(v_as_1043_);
lean_dec(v_n_u2080_1041_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__24(lean_object* v_n_u2081_1051_, lean_object* v_as_1052_, size_t v_i_1053_, size_t v_stop_1054_, lean_object* v_b_1055_){
_start:
{
lean_object* v___y_1057_; uint8_t v___x_1061_; 
v___x_1061_ = lean_usize_dec_eq(v_i_1053_, v_stop_1054_);
if (v___x_1061_ == 0)
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; uint8_t v___x_1065_; 
v___x_1062_ = lean_array_uget_borrowed(v_as_1052_, v_i_1053_);
v___x_1063_ = l_Lean_Name_getPrefix(v___x_1062_);
v___x_1064_ = l_Lean_Name_getPrefix(v_n_u2081_1051_);
v___x_1065_ = l_Lean_Name_isPrefixOf(v___x_1063_, v___x_1064_);
lean_dec(v___x_1064_);
lean_dec(v___x_1063_);
if (v___x_1065_ == 0)
{
v___y_1057_ = v_b_1055_;
goto v___jp_1056_;
}
else
{
lean_object* v___x_1066_; 
lean_inc(v___x_1062_);
v___x_1066_ = lean_array_push(v_b_1055_, v___x_1062_);
v___y_1057_ = v___x_1066_;
goto v___jp_1056_;
}
}
else
{
return v_b_1055_;
}
v___jp_1056_:
{
size_t v___x_1058_; size_t v___x_1059_; 
v___x_1058_ = ((size_t)1ULL);
v___x_1059_ = lean_usize_add(v_i_1053_, v___x_1058_);
v_i_1053_ = v___x_1059_;
v_b_1055_ = v___y_1057_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__24___boxed(lean_object* v_n_u2081_1067_, lean_object* v_as_1068_, lean_object* v_i_1069_, lean_object* v_stop_1070_, lean_object* v_b_1071_){
_start:
{
size_t v_i_boxed_1072_; size_t v_stop_boxed_1073_; lean_object* v_res_1074_; 
v_i_boxed_1072_ = lean_unbox_usize(v_i_1069_);
lean_dec(v_i_1069_);
v_stop_boxed_1073_ = lean_unbox_usize(v_stop_1070_);
lean_dec(v_stop_1070_);
v_res_1074_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__24(v_n_u2081_1067_, v_as_1068_, v_i_boxed_1072_, v_stop_boxed_1073_, v_b_1071_);
lean_dec_ref(v_as_1068_);
lean_dec(v_n_u2081_1067_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12(lean_object* v_n_u2080_1077_, uint8_t v_fullNames_1078_, uint8_t v_allowHorizAliases_1079_, lean_object* v_filter_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
lean_object* v_view_1086_; lean_object* v_name_1087_; lean_object* v_n_u2081_1088_; 
lean_inc(v_n_u2080_1077_);
v_view_1086_ = l_Lean_extractMacroScopes(v_n_u2080_1077_);
v_name_1087_ = lean_ctor_get(v_view_1086_, 0);
lean_inc(v_name_1087_);
v_n_u2081_1088_ = l_Lean_privateToUserName(v_name_1087_);
if (v_fullNames_1078_ == 0)
{
lean_object* v___x_1089_; lean_object* v_aliases_1091_; lean_object* v_env_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1089_ = lean_st_ref_get(v___y_1084_);
v_env_1106_ = lean_ctor_get(v___x_1089_, 0);
lean_inc_ref(v_env_1106_);
lean_dec(v___x_1089_);
lean_inc(v_n_u2080_1077_);
v___x_1107_ = l_Lean_getRevAliases(v_env_1106_, v_n_u2080_1077_);
v___x_1108_ = lean_array_mk(v___x_1107_);
if (v_allowHorizAliases_1079_ == 0)
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; uint8_t v___x_1112_; 
v___x_1109_ = lean_unsigned_to_nat(0u);
v___x_1110_ = lean_array_get_size(v___x_1108_);
v___x_1111_ = ((lean_object*)(l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12___closed__0));
v___x_1112_ = lean_nat_dec_lt(v___x_1109_, v___x_1110_);
if (v___x_1112_ == 0)
{
lean_dec_ref(v___x_1108_);
v_aliases_1091_ = v___x_1111_;
goto v___jp_1090_;
}
else
{
size_t v___x_1113_; size_t v___x_1114_; lean_object* v___x_1115_; 
v___x_1113_ = ((size_t)0ULL);
v___x_1114_ = lean_usize_of_nat(v___x_1110_);
v___x_1115_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__24(v_n_u2081_1088_, v___x_1108_, v___x_1113_, v___x_1114_, v___x_1111_);
lean_dec_ref(v___x_1108_);
v_aliases_1091_ = v___x_1115_;
goto v___jp_1090_;
}
}
else
{
v_aliases_1091_ = v___x_1108_;
goto v___jp_1090_;
}
v___jp_1090_:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1092_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_filter_1080_);
v___x_1093_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__23(v_n_u2080_1077_, v_filter_1080_, v_aliases_1091_, v___x_1092_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
lean_dec_ref(v_aliases_1091_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v_a_1094_; 
v_a_1094_ = lean_ctor_get(v___x_1093_, 0);
if (lean_obj_tag(v_a_1094_) == 0)
{
lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1104_; 
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1104_ == 0)
{
lean_object* v_unused_1105_; 
v_unused_1105_ = lean_ctor_get(v___x_1093_, 0);
lean_dec(v_unused_1105_);
v___x_1096_ = v___x_1093_;
v_isShared_1097_ = v_isSharedCheck_1104_;
goto v_resetjp_1095_;
}
else
{
lean_dec(v___x_1093_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1104_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1099_; 
if (v_isShared_1097_ == 0)
{
lean_ctor_set_tag(v___x_1096_, 1);
lean_ctor_set(v___x_1096_, 0, v_view_1086_);
v___x_1099_ = v___x_1096_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_view_1086_);
v___x_1099_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1100_ = l_Lean_rootNamespace;
v___x_1101_ = l_Lean_Name_append(v___x_1100_, v_n_u2081_1088_);
v___x_1102_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22(v_n_u2080_1077_, v_filter_1080_, v___x_1099_, v___x_1101_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
lean_dec(v_n_u2080_1077_);
return v___x_1102_;
}
}
}
else
{
lean_dec(v_n_u2081_1088_);
lean_dec_ref(v_view_1086_);
lean_dec_ref(v_filter_1080_);
lean_dec(v_n_u2080_1077_);
return v___x_1093_;
}
}
else
{
lean_dec(v_n_u2081_1088_);
lean_dec_ref(v_view_1086_);
lean_dec_ref(v_filter_1080_);
lean_dec(v_n_u2080_1077_);
return v___x_1093_;
}
}
}
else
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1116_, 0, v_view_1086_);
lean_inc(v_n_u2081_1088_);
lean_inc_ref(v___x_1116_);
lean_inc_ref(v_filter_1080_);
v___x_1117_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25(v_n_u2080_1077_, v_filter_1080_, v___x_1116_, v_n_u2081_1088_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
if (lean_obj_tag(v_a_1118_) == 0)
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
lean_dec_ref_known(v___x_1117_, 1);
v___x_1119_ = l_Lean_rootNamespace;
v___x_1120_ = l_Lean_Name_append(v___x_1119_, v_n_u2081_1088_);
v___x_1121_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25(v_n_u2080_1077_, v_filter_1080_, v___x_1116_, v___x_1120_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
lean_dec(v_n_u2080_1077_);
return v___x_1121_;
}
else
{
lean_dec_ref_known(v___x_1116_, 1);
lean_dec(v_n_u2081_1088_);
lean_dec_ref(v_filter_1080_);
lean_dec(v_n_u2080_1077_);
return v___x_1117_;
}
}
else
{
lean_dec_ref_known(v___x_1116_, 1);
lean_dec(v_n_u2081_1088_);
lean_dec_ref(v_filter_1080_);
lean_dec(v_n_u2080_1077_);
return v___x_1117_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12___boxed(lean_object* v_n_u2080_1122_, lean_object* v_fullNames_1123_, lean_object* v_allowHorizAliases_1124_, lean_object* v_filter_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
uint8_t v_fullNames_boxed_1131_; uint8_t v_allowHorizAliases_boxed_1132_; lean_object* v_res_1133_; 
v_fullNames_boxed_1131_ = lean_unbox(v_fullNames_1123_);
v_allowHorizAliases_boxed_1132_ = lean_unbox(v_allowHorizAliases_1124_);
v_res_1133_ = l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12(v_n_u2080_1122_, v_fullNames_boxed_1131_, v_allowHorizAliases_boxed_1132_, v_filter_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg___lam__0(lean_object* v_localDecl_1134_, lean_object* v_givenName_1135_){
_start:
{
lean_object* v___x_1136_; uint8_t v___x_1137_; 
v___x_1136_ = l_Lean_LocalDecl_userName(v_localDecl_1134_);
v___x_1137_ = lean_name_eq(v___x_1136_, v_givenName_1135_);
lean_dec(v___x_1136_);
if (v___x_1137_ == 0)
{
lean_object* v___x_1138_; 
lean_dec_ref(v_localDecl_1134_);
v___x_1138_ = lean_box(0);
return v___x_1138_;
}
else
{
lean_object* v___x_1139_; 
v___x_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1139_, 0, v_localDecl_1134_);
return v___x_1139_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg___lam__0___boxed(lean_object* v_localDecl_1140_, lean_object* v_givenName_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg___lam__0(v_localDecl_1140_, v_givenName_1141_);
lean_dec(v_givenName_1141_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__17___redArg(lean_object* v_t_1143_, lean_object* v_k_1144_){
_start:
{
if (lean_obj_tag(v_t_1143_) == 0)
{
lean_object* v_k_1145_; lean_object* v_v_1146_; lean_object* v_l_1147_; lean_object* v_r_1148_; uint8_t v___x_1149_; 
v_k_1145_ = lean_ctor_get(v_t_1143_, 1);
v_v_1146_ = lean_ctor_get(v_t_1143_, 2);
v_l_1147_ = lean_ctor_get(v_t_1143_, 3);
v_r_1148_ = lean_ctor_get(v_t_1143_, 4);
v___x_1149_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1144_, v_k_1145_);
switch(v___x_1149_)
{
case 0:
{
v_t_1143_ = v_l_1147_;
goto _start;
}
case 1:
{
lean_object* v___x_1151_; 
lean_inc(v_v_1146_);
v___x_1151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1151_, 0, v_v_1146_);
return v___x_1151_;
}
default: 
{
v_t_1143_ = v_r_1148_;
goto _start;
}
}
}
else
{
lean_object* v___x_1153_; 
v___x_1153_ = lean_box(0);
return v___x_1153_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__17___redArg___boxed(lean_object* v_t_1154_, lean_object* v_k_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__17___redArg(v_t_1154_, v_k_1155_);
lean_dec(v_k_1155_);
lean_dec(v_t_1154_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg(lean_object* v_givenName_1157_, uint8_t v_skipAuxDecl_1158_, lean_object* v_auxDeclToFullName_1159_, lean_object* v___x_1160_, lean_object* v_givenNameView_1161_, lean_object* v_as_1162_, lean_object* v_i_1163_){
_start:
{
lean_object* v_zero_1164_; uint8_t v_isZero_1165_; 
v_zero_1164_ = lean_unsigned_to_nat(0u);
v_isZero_1165_ = lean_nat_dec_eq(v_i_1163_, v_zero_1164_);
if (v_isZero_1165_ == 1)
{
lean_object* v___x_1166_; 
lean_dec(v_i_1163_);
lean_dec_ref(v_givenNameView_1161_);
lean_dec(v___x_1160_);
v___x_1166_ = lean_box(0);
return v___x_1166_;
}
else
{
lean_object* v_one_1167_; lean_object* v_n_1168_; lean_object* v___y_1170_; lean_object* v___x_1172_; 
v_one_1167_ = lean_unsigned_to_nat(1u);
v_n_1168_ = lean_nat_sub(v_i_1163_, v_one_1167_);
lean_dec(v_i_1163_);
v___x_1172_ = lean_array_fget_borrowed(v_as_1162_, v_n_1168_);
if (lean_obj_tag(v___x_1172_) == 0)
{
v___y_1170_ = v___x_1172_;
goto v___jp_1169_;
}
else
{
lean_object* v_val_1173_; uint8_t v___x_1174_; 
v_val_1173_ = lean_ctor_get(v___x_1172_, 0);
v___x_1174_ = l_Lean_LocalDecl_isAuxDecl(v_val_1173_);
if (v___x_1174_ == 0)
{
lean_object* v___x_1175_; 
lean_inc(v_val_1173_);
v___x_1175_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg___lam__0(v_val_1173_, v_givenName_1157_);
v___y_1170_ = v___x_1175_;
goto v___jp_1169_;
}
else
{
if (v_skipAuxDecl_1158_ == 0)
{
if (v___x_1174_ == 0)
{
v_i_1163_ = v_n_1168_;
goto _start;
}
else
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = l_Lean_LocalDecl_fvarId(v_val_1173_);
v___x_1178_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__17___redArg(v_auxDeclToFullName_1159_, v___x_1177_);
lean_dec(v___x_1177_);
if (lean_obj_tag(v___x_1178_) == 1)
{
lean_object* v_val_1179_; lean_object* v_fullDeclView_1180_; lean_object* v___y_1182_; lean_object* v_name_1203_; lean_object* v___x_1204_; 
v_val_1179_ = lean_ctor_get(v___x_1178_, 0);
lean_inc(v_val_1179_);
lean_dec_ref_known(v___x_1178_, 1);
v_fullDeclView_1180_ = l_Lean_extractMacroScopes(v_val_1179_);
v_name_1203_ = lean_ctor_get(v_fullDeclView_1180_, 0);
lean_inc(v_name_1203_);
v___x_1204_ = l_Lean_privateToUserName_x3f(v_name_1203_);
if (lean_obj_tag(v___x_1204_) == 0)
{
lean_inc(v_name_1203_);
v___y_1182_ = v_name_1203_;
goto v___jp_1181_;
}
else
{
lean_object* v_val_1205_; 
v_val_1205_ = lean_ctor_get(v___x_1204_, 0);
lean_inc(v_val_1205_);
lean_dec_ref_known(v___x_1204_, 1);
v___y_1182_ = v_val_1205_;
goto v___jp_1181_;
}
v___jp_1181_:
{
lean_object* v_imported_1183_; lean_object* v_ctx_1184_; lean_object* v_scopes_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1201_; 
v_imported_1183_ = lean_ctor_get(v_fullDeclView_1180_, 1);
v_ctx_1184_ = lean_ctor_get(v_fullDeclView_1180_, 2);
v_scopes_1185_ = lean_ctor_get(v_fullDeclView_1180_, 3);
v_isSharedCheck_1201_ = !lean_is_exclusive(v_fullDeclView_1180_);
if (v_isSharedCheck_1201_ == 0)
{
lean_object* v_unused_1202_; 
v_unused_1202_ = lean_ctor_get(v_fullDeclView_1180_, 0);
lean_dec(v_unused_1202_);
v___x_1187_ = v_fullDeclView_1180_;
v_isShared_1188_ = v_isSharedCheck_1201_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_scopes_1185_);
lean_inc(v_ctx_1184_);
lean_inc(v_imported_1183_);
lean_dec(v_fullDeclView_1180_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1201_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v_fullDeclView_1190_; 
if (v_isShared_1188_ == 0)
{
lean_ctor_set(v___x_1187_, 0, v___y_1182_);
v_fullDeclView_1190_ = v___x_1187_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___y_1182_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v_imported_1183_);
lean_ctor_set(v_reuseFailAlloc_1200_, 2, v_ctx_1184_);
lean_ctor_set(v_reuseFailAlloc_1200_, 3, v_scopes_1185_);
v_fullDeclView_1190_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
lean_object* v_fullDeclName_1191_; uint8_t v___x_1192_; 
lean_inc_ref(v_fullDeclView_1190_);
v_fullDeclName_1191_ = l_Lean_MacroScopesView_review(v_fullDeclView_1190_);
v___x_1192_ = l_Lean_Name_isPrefixOf(v___x_1160_, v_fullDeclName_1191_);
if (v___x_1192_ == 0)
{
lean_object* v___x_1193_; 
lean_dec_ref(v_fullDeclView_1190_);
lean_inc(v___x_1160_);
lean_inc_ref(v_givenNameView_1161_);
lean_inc(v_val_1173_);
v___x_1193_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_val_1173_, v_givenNameView_1161_, v_fullDeclName_1191_, v___x_1160_);
lean_dec(v_fullDeclName_1191_);
v___y_1170_ = v___x_1193_;
goto v___jp_1169_;
}
else
{
lean_object* v___x_1194_; lean_object* v_localDeclNameView_1195_; uint8_t v___x_1196_; 
lean_dec(v_fullDeclName_1191_);
v___x_1194_ = l_Lean_LocalDecl_userName(v_val_1173_);
v_localDeclNameView_1195_ = l_Lean_extractMacroScopes(v___x_1194_);
v___x_1196_ = l_Lean_MacroScopesView_isSuffixOf(v_localDeclNameView_1195_, v_givenNameView_1161_);
lean_dec_ref(v_localDeclNameView_1195_);
if (v___x_1196_ == 0)
{
lean_dec_ref(v_fullDeclView_1190_);
v_i_1163_ = v_n_1168_;
goto _start;
}
else
{
uint8_t v___x_1198_; 
v___x_1198_ = l_Lean_MacroScopesView_isSuffixOf(v_givenNameView_1161_, v_fullDeclView_1190_);
lean_dec_ref(v_fullDeclView_1190_);
if (v___x_1198_ == 0)
{
v_i_1163_ = v_n_1168_;
goto _start;
}
else
{
lean_inc_ref(v___x_1172_);
v___y_1170_ = v___x_1172_;
goto v___jp_1169_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1206_; 
lean_dec(v___x_1178_);
lean_inc(v_val_1173_);
v___x_1206_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg___lam__0(v_val_1173_, v_givenName_1157_);
v___y_1170_ = v___x_1206_;
goto v___jp_1169_;
}
}
}
else
{
v_i_1163_ = v_n_1168_;
goto _start;
}
}
}
v___jp_1169_:
{
if (lean_obj_tag(v___y_1170_) == 0)
{
v_i_1163_ = v_n_1168_;
goto _start;
}
else
{
lean_dec(v_n_1168_);
lean_dec_ref(v_givenNameView_1161_);
lean_dec(v___x_1160_);
return v___y_1170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg___boxed(lean_object* v_givenName_1208_, lean_object* v_skipAuxDecl_1209_, lean_object* v_auxDeclToFullName_1210_, lean_object* v___x_1211_, lean_object* v_givenNameView_1212_, lean_object* v_as_1213_, lean_object* v_i_1214_){
_start:
{
uint8_t v_skipAuxDecl_boxed_1215_; lean_object* v_res_1216_; 
v_skipAuxDecl_boxed_1215_ = lean_unbox(v_skipAuxDecl_1209_);
v_res_1216_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg(v_givenName_1208_, v_skipAuxDecl_boxed_1215_, v_auxDeclToFullName_1210_, v___x_1211_, v_givenNameView_1212_, v_as_1213_, v_i_1214_);
lean_dec_ref(v_as_1213_);
lean_dec(v_auxDeclToFullName_1210_);
lean_dec(v_givenName_1208_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24___redArg(lean_object* v_givenName_1217_, uint8_t v_skipAuxDecl_1218_, lean_object* v_auxDeclToFullName_1219_, lean_object* v___x_1220_, lean_object* v_givenNameView_1221_, lean_object* v_as_1222_, lean_object* v_i_1223_){
_start:
{
lean_object* v_zero_1224_; uint8_t v_isZero_1225_; 
v_zero_1224_ = lean_unsigned_to_nat(0u);
v_isZero_1225_ = lean_nat_dec_eq(v_i_1223_, v_zero_1224_);
if (v_isZero_1225_ == 1)
{
lean_object* v___x_1226_; 
lean_dec(v_i_1223_);
lean_dec_ref(v_givenNameView_1221_);
lean_dec(v___x_1220_);
v___x_1226_ = lean_box(0);
return v___x_1226_;
}
else
{
lean_object* v_one_1227_; lean_object* v_n_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v_one_1227_ = lean_unsigned_to_nat(1u);
v_n_1228_ = lean_nat_sub(v_i_1223_, v_one_1227_);
lean_dec(v_i_1223_);
v___x_1229_ = lean_array_fget_borrowed(v_as_1222_, v_n_1228_);
lean_inc_ref(v_givenNameView_1221_);
lean_inc(v___x_1220_);
v___x_1230_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21(v_givenName_1217_, v_skipAuxDecl_1218_, v_auxDeclToFullName_1219_, v___x_1220_, v_givenNameView_1221_, v___x_1229_);
if (lean_obj_tag(v___x_1230_) == 0)
{
v_i_1223_ = v_n_1228_;
goto _start;
}
else
{
lean_dec(v_n_1228_);
lean_dec_ref(v_givenNameView_1221_);
lean_dec(v___x_1220_);
return v___x_1230_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21(lean_object* v_givenName_1232_, uint8_t v_skipAuxDecl_1233_, lean_object* v_auxDeclToFullName_1234_, lean_object* v___x_1235_, lean_object* v_givenNameView_1236_, lean_object* v_x_1237_){
_start:
{
if (lean_obj_tag(v_x_1237_) == 0)
{
lean_object* v_cs_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v_cs_1238_ = lean_ctor_get(v_x_1237_, 0);
v___x_1239_ = lean_array_get_size(v_cs_1238_);
v___x_1240_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24___redArg(v_givenName_1232_, v_skipAuxDecl_1233_, v_auxDeclToFullName_1234_, v___x_1235_, v_givenNameView_1236_, v_cs_1238_, v___x_1239_);
return v___x_1240_;
}
else
{
lean_object* v_vs_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v_vs_1241_ = lean_ctor_get(v_x_1237_, 0);
v___x_1242_ = lean_array_get_size(v_vs_1241_);
v___x_1243_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg(v_givenName_1232_, v_skipAuxDecl_1233_, v_auxDeclToFullName_1234_, v___x_1235_, v_givenNameView_1236_, v_vs_1241_, v___x_1242_);
return v___x_1243_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21___boxed(lean_object* v_givenName_1244_, lean_object* v_skipAuxDecl_1245_, lean_object* v_auxDeclToFullName_1246_, lean_object* v___x_1247_, lean_object* v_givenNameView_1248_, lean_object* v_x_1249_){
_start:
{
uint8_t v_skipAuxDecl_boxed_1250_; lean_object* v_res_1251_; 
v_skipAuxDecl_boxed_1250_ = lean_unbox(v_skipAuxDecl_1245_);
v_res_1251_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21(v_givenName_1244_, v_skipAuxDecl_boxed_1250_, v_auxDeclToFullName_1246_, v___x_1247_, v_givenNameView_1248_, v_x_1249_);
lean_dec_ref(v_x_1249_);
lean_dec(v_auxDeclToFullName_1246_);
lean_dec(v_givenName_1244_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24___redArg___boxed(lean_object* v_givenName_1252_, lean_object* v_skipAuxDecl_1253_, lean_object* v_auxDeclToFullName_1254_, lean_object* v___x_1255_, lean_object* v_givenNameView_1256_, lean_object* v_as_1257_, lean_object* v_i_1258_){
_start:
{
uint8_t v_skipAuxDecl_boxed_1259_; lean_object* v_res_1260_; 
v_skipAuxDecl_boxed_1259_ = lean_unbox(v_skipAuxDecl_1253_);
v_res_1260_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24___redArg(v_givenName_1252_, v_skipAuxDecl_boxed_1259_, v_auxDeclToFullName_1254_, v___x_1255_, v_givenNameView_1256_, v_as_1257_, v_i_1258_);
lean_dec_ref(v_as_1257_);
lean_dec(v_auxDeclToFullName_1254_);
lean_dec(v_givenName_1252_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18(lean_object* v_givenName_1261_, uint8_t v_skipAuxDecl_1262_, lean_object* v_auxDeclToFullName_1263_, lean_object* v___x_1264_, lean_object* v_givenNameView_1265_, lean_object* v_t_1266_){
_start:
{
lean_object* v_root_1267_; lean_object* v_tail_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v_root_1267_ = lean_ctor_get(v_t_1266_, 0);
v_tail_1268_ = lean_ctor_get(v_t_1266_, 1);
v___x_1269_ = lean_array_get_size(v_tail_1268_);
lean_inc_ref(v_givenNameView_1265_);
lean_inc(v___x_1264_);
v___x_1270_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg(v_givenName_1261_, v_skipAuxDecl_1262_, v_auxDeclToFullName_1263_, v___x_1264_, v_givenNameView_1265_, v_tail_1268_, v___x_1269_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v___x_1271_; 
v___x_1271_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21(v_givenName_1261_, v_skipAuxDecl_1262_, v_auxDeclToFullName_1263_, v___x_1264_, v_givenNameView_1265_, v_root_1267_);
return v___x_1271_;
}
else
{
lean_dec_ref(v_givenNameView_1265_);
lean_dec(v___x_1264_);
return v___x_1270_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18___boxed(lean_object* v_givenName_1272_, lean_object* v_skipAuxDecl_1273_, lean_object* v_auxDeclToFullName_1274_, lean_object* v___x_1275_, lean_object* v_givenNameView_1276_, lean_object* v_t_1277_){
_start:
{
uint8_t v_skipAuxDecl_boxed_1278_; lean_object* v_res_1279_; 
v_skipAuxDecl_boxed_1278_ = lean_unbox(v_skipAuxDecl_1273_);
v_res_1279_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18(v_givenName_1272_, v_skipAuxDecl_boxed_1278_, v_auxDeclToFullName_1274_, v___x_1275_, v_givenNameView_1276_, v_t_1277_);
lean_dec_ref(v_t_1277_);
lean_dec(v_auxDeclToFullName_1274_);
lean_dec(v_givenName_1272_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___redArg(lean_object* v_localDecl_x3f_1280_, lean_object* v_givenName_1281_, lean_object* v_as_1282_, lean_object* v_i_1283_){
_start:
{
lean_object* v_zero_1284_; uint8_t v_isZero_1285_; 
v_zero_1284_ = lean_unsigned_to_nat(0u);
v_isZero_1285_ = lean_nat_dec_eq(v_i_1283_, v_zero_1284_);
if (v_isZero_1285_ == 1)
{
lean_object* v___x_1286_; 
lean_dec(v_i_1283_);
v___x_1286_ = lean_box(0);
return v___x_1286_;
}
else
{
lean_object* v_one_1287_; lean_object* v_n_1288_; lean_object* v___y_1290_; lean_object* v___x_1292_; 
v_one_1287_ = lean_unsigned_to_nat(1u);
v_n_1288_ = lean_nat_sub(v_i_1283_, v_one_1287_);
lean_dec(v_i_1283_);
v___x_1292_ = lean_array_fget_borrowed(v_as_1282_, v_n_1288_);
if (lean_obj_tag(v___x_1292_) == 0)
{
v___y_1290_ = v___x_1292_;
goto v___jp_1289_;
}
else
{
lean_object* v_val_1293_; uint8_t v___x_1294_; 
v_val_1293_ = lean_ctor_get(v___x_1292_, 0);
v___x_1294_ = l_Lean_LocalDecl_isAuxDecl(v_val_1293_);
if (v___x_1294_ == 0)
{
v___y_1290_ = v_localDecl_x3f_1280_;
goto v___jp_1289_;
}
else
{
lean_object* v___x_1295_; uint8_t v___x_1296_; 
v___x_1295_ = l_Lean_LocalDecl_userName(v_val_1293_);
v___x_1296_ = lean_name_eq(v___x_1295_, v_givenName_1281_);
lean_dec(v___x_1295_);
if (v___x_1296_ == 0)
{
v_i_1283_ = v_n_1288_;
goto _start;
}
else
{
v___y_1290_ = v___x_1292_;
goto v___jp_1289_;
}
}
}
v___jp_1289_:
{
if (lean_obj_tag(v___y_1290_) == 0)
{
v_i_1283_ = v_n_1288_;
goto _start;
}
else
{
lean_dec(v_n_1288_);
lean_inc_ref(v___y_1290_);
return v___y_1290_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___redArg___boxed(lean_object* v_localDecl_x3f_1298_, lean_object* v_givenName_1299_, lean_object* v_as_1300_, lean_object* v_i_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___redArg(v_localDecl_x3f_1298_, v_givenName_1299_, v_as_1300_, v_i_1301_);
lean_dec_ref(v_as_1300_);
lean_dec(v_givenName_1299_);
lean_dec(v_localDecl_x3f_1298_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28___redArg(lean_object* v_localDecl_x3f_1303_, lean_object* v_givenName_1304_, lean_object* v_as_1305_, lean_object* v_i_1306_){
_start:
{
lean_object* v_zero_1307_; uint8_t v_isZero_1308_; 
v_zero_1307_ = lean_unsigned_to_nat(0u);
v_isZero_1308_ = lean_nat_dec_eq(v_i_1306_, v_zero_1307_);
if (v_isZero_1308_ == 1)
{
lean_object* v___x_1309_; 
lean_dec(v_i_1306_);
v___x_1309_ = lean_box(0);
return v___x_1309_;
}
else
{
lean_object* v_one_1310_; lean_object* v_n_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v_one_1310_ = lean_unsigned_to_nat(1u);
v_n_1311_ = lean_nat_sub(v_i_1306_, v_one_1310_);
lean_dec(v_i_1306_);
v___x_1312_ = lean_array_fget_borrowed(v_as_1305_, v_n_1311_);
v___x_1313_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24(v_localDecl_x3f_1303_, v_givenName_1304_, v___x_1312_);
if (lean_obj_tag(v___x_1313_) == 0)
{
v_i_1306_ = v_n_1311_;
goto _start;
}
else
{
lean_dec(v_n_1311_);
return v___x_1313_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24(lean_object* v_localDecl_x3f_1315_, lean_object* v_givenName_1316_, lean_object* v_x_1317_){
_start:
{
if (lean_obj_tag(v_x_1317_) == 0)
{
lean_object* v_cs_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v_cs_1318_ = lean_ctor_get(v_x_1317_, 0);
v___x_1319_ = lean_array_get_size(v_cs_1318_);
v___x_1320_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28___redArg(v_localDecl_x3f_1315_, v_givenName_1316_, v_cs_1318_, v___x_1319_);
return v___x_1320_;
}
else
{
lean_object* v_vs_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v_vs_1321_ = lean_ctor_get(v_x_1317_, 0);
v___x_1322_ = lean_array_get_size(v_vs_1321_);
v___x_1323_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___redArg(v_localDecl_x3f_1315_, v_givenName_1316_, v_vs_1321_, v___x_1322_);
return v___x_1323_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24___boxed(lean_object* v_localDecl_x3f_1324_, lean_object* v_givenName_1325_, lean_object* v_x_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24(v_localDecl_x3f_1324_, v_givenName_1325_, v_x_1326_);
lean_dec_ref(v_x_1326_);
lean_dec(v_givenName_1325_);
lean_dec(v_localDecl_x3f_1324_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28___redArg___boxed(lean_object* v_localDecl_x3f_1328_, lean_object* v_givenName_1329_, lean_object* v_as_1330_, lean_object* v_i_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28___redArg(v_localDecl_x3f_1328_, v_givenName_1329_, v_as_1330_, v_i_1331_);
lean_dec_ref(v_as_1330_);
lean_dec(v_givenName_1329_);
lean_dec(v_localDecl_x3f_1328_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19(lean_object* v_localDecl_x3f_1333_, lean_object* v_givenName_1334_, lean_object* v_t_1335_){
_start:
{
lean_object* v_root_1336_; lean_object* v_tail_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
v_root_1336_ = lean_ctor_get(v_t_1335_, 0);
v_tail_1337_ = lean_ctor_get(v_t_1335_, 1);
v___x_1338_ = lean_array_get_size(v_tail_1337_);
v___x_1339_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___redArg(v_localDecl_x3f_1333_, v_givenName_1334_, v_tail_1337_, v___x_1338_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v___x_1340_; 
v___x_1340_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24(v_localDecl_x3f_1333_, v_givenName_1334_, v_root_1336_);
return v___x_1340_;
}
else
{
return v___x_1339_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19___boxed(lean_object* v_localDecl_x3f_1341_, lean_object* v_givenName_1342_, lean_object* v_t_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19(v_localDecl_x3f_1341_, v_givenName_1342_, v_t_1343_);
lean_dec_ref(v_t_1343_);
lean_dec(v_givenName_1342_);
lean_dec(v_localDecl_x3f_1341_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11___lam__0(lean_object* v_auxDeclToFullName_1345_, lean_object* v_currNamespace_1346_, lean_object* v_decls_1347_, lean_object* v_givenNameView_1348_, uint8_t v_skipAuxDecl_1349_){
_start:
{
lean_object* v_givenName_1350_; lean_object* v_localDecl_x3f_1351_; 
lean_inc_ref(v_givenNameView_1348_);
v_givenName_1350_ = l_Lean_MacroScopesView_review(v_givenNameView_1348_);
v_localDecl_x3f_1351_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18(v_givenName_1350_, v_skipAuxDecl_1349_, v_auxDeclToFullName_1345_, v_currNamespace_1346_, v_givenNameView_1348_, v_decls_1347_);
if (lean_obj_tag(v_localDecl_x3f_1351_) == 0)
{
if (v_skipAuxDecl_1349_ == 0)
{
lean_object* v___x_1352_; 
v___x_1352_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19(v_localDecl_x3f_1351_, v_givenName_1350_, v_decls_1347_);
lean_dec(v_givenName_1350_);
return v___x_1352_;
}
else
{
lean_dec(v_givenName_1350_);
return v_localDecl_x3f_1351_;
}
}
else
{
lean_dec(v_givenName_1350_);
return v_localDecl_x3f_1351_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11___lam__0___boxed(lean_object* v_auxDeclToFullName_1353_, lean_object* v_currNamespace_1354_, lean_object* v_decls_1355_, lean_object* v_givenNameView_1356_, lean_object* v_skipAuxDecl_1357_){
_start:
{
uint8_t v_skipAuxDecl_boxed_1358_; lean_object* v_res_1359_; 
v_skipAuxDecl_boxed_1358_ = lean_unbox(v_skipAuxDecl_1357_);
v_res_1359_ = l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11___lam__0(v_auxDeclToFullName_1353_, v_currNamespace_1354_, v_decls_1355_, v_givenNameView_1356_, v_skipAuxDecl_boxed_1358_);
lean_dec_ref(v_decls_1355_);
lean_dec(v_auxDeclToFullName_1353_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__27(lean_object* v_a_1360_, lean_object* v_a_1361_){
_start:
{
if (lean_obj_tag(v_a_1360_) == 0)
{
lean_object* v___x_1362_; 
v___x_1362_ = l_List_reverse___redArg(v_a_1361_);
return v___x_1362_;
}
else
{
lean_object* v_head_1363_; lean_object* v_tail_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1375_; 
v_head_1363_ = lean_ctor_get(v_a_1360_, 0);
v_tail_1364_ = lean_ctor_get(v_a_1360_, 1);
v_isSharedCheck_1375_ = !lean_is_exclusive(v_a_1360_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1366_ = v_a_1360_;
v_isShared_1367_ = v_isSharedCheck_1375_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_tail_1364_);
lean_inc(v_head_1363_);
lean_dec(v_a_1360_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1375_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v_snd_1368_; uint8_t v___x_1369_; 
v_snd_1368_ = lean_ctor_get(v_head_1363_, 1);
v___x_1369_ = l_List_isEmpty___redArg(v_snd_1368_);
if (v___x_1369_ == 0)
{
lean_del_object(v___x_1366_);
lean_dec(v_head_1363_);
v_a_1360_ = v_tail_1364_;
goto _start;
}
else
{
lean_object* v___x_1372_; 
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 1, v_a_1361_);
v___x_1372_ = v___x_1366_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_head_1363_);
lean_ctor_set(v_reuseFailAlloc_1374_, 1, v_a_1361_);
v___x_1372_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
v_a_1360_ = v_tail_1364_;
v_a_1361_ = v___x_1372_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44(lean_object* v_ref_1376_, lean_object* v_msgData_1377_, uint8_t v_severity_1378_, uint8_t v_isSilent_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
uint8_t v___y_1386_; lean_object* v___y_1387_; uint8_t v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v_toCold_1393_; lean_object* v___y_1394_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; uint8_t v___y_1426_; uint8_t v___y_1427_; uint8_t v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1450_; uint8_t v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; uint8_t v___y_1454_; uint8_t v___y_1455_; lean_object* v___y_1456_; uint8_t v___y_1460_; uint8_t v___y_1461_; uint8_t v___y_1462_; uint8_t v___x_1473_; uint8_t v___y_1475_; uint8_t v___y_1476_; uint8_t v___y_1477_; uint8_t v___y_1479_; uint8_t v___x_1487_; 
v___x_1473_ = 2;
v___x_1487_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1378_, v___x_1473_);
if (v___x_1487_ == 0)
{
v___y_1479_ = v___x_1487_;
goto v___jp_1478_;
}
else
{
uint8_t v___x_1488_; 
lean_inc_ref(v_msgData_1377_);
v___x_1488_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1377_);
v___y_1479_ = v___x_1488_;
goto v___jp_1478_;
}
v___jp_1385_:
{
lean_object* v_currNamespace_1395_; lean_object* v_openDecls_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v_env_1401_; lean_object* v_nextMacroScope_1402_; lean_object* v_ngen_1403_; lean_object* v_auxDeclNGen_1404_; lean_object* v_traceState_1405_; lean_object* v_cache_1406_; lean_object* v_recordedDeps_1407_; lean_object* v_messages_1408_; lean_object* v_infoState_1409_; lean_object* v_snapshotTasks_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1421_; 
v_currNamespace_1395_ = lean_ctor_get(v_toCold_1393_, 4);
v_openDecls_1396_ = lean_ctor_get(v_toCold_1393_, 5);
lean_inc(v_openDecls_1396_);
lean_inc(v_currNamespace_1395_);
v___x_1397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1397_, 0, v_currNamespace_1395_);
lean_ctor_set(v___x_1397_, 1, v_openDecls_1396_);
v___x_1398_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1397_);
lean_ctor_set(v___x_1398_, 1, v___y_1387_);
lean_inc_ref(v___y_1389_);
lean_inc_ref(v___y_1392_);
v___x_1399_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1399_, 0, v___y_1392_);
lean_ctor_set(v___x_1399_, 1, v___y_1391_);
lean_ctor_set(v___x_1399_, 2, v___y_1390_);
lean_ctor_set(v___x_1399_, 3, v___y_1389_);
lean_ctor_set(v___x_1399_, 4, v___x_1398_);
lean_ctor_set_uint8(v___x_1399_, sizeof(void*)*5, v___y_1388_);
lean_ctor_set_uint8(v___x_1399_, sizeof(void*)*5 + 1, v___y_1386_);
lean_ctor_set_uint8(v___x_1399_, sizeof(void*)*5 + 2, v_isSilent_1379_);
v___x_1400_ = lean_st_ref_take(v___y_1394_);
v_env_1401_ = lean_ctor_get(v___x_1400_, 0);
v_nextMacroScope_1402_ = lean_ctor_get(v___x_1400_, 1);
v_ngen_1403_ = lean_ctor_get(v___x_1400_, 2);
v_auxDeclNGen_1404_ = lean_ctor_get(v___x_1400_, 3);
v_traceState_1405_ = lean_ctor_get(v___x_1400_, 4);
v_cache_1406_ = lean_ctor_get(v___x_1400_, 5);
v_recordedDeps_1407_ = lean_ctor_get(v___x_1400_, 6);
v_messages_1408_ = lean_ctor_get(v___x_1400_, 7);
v_infoState_1409_ = lean_ctor_get(v___x_1400_, 8);
v_snapshotTasks_1410_ = lean_ctor_get(v___x_1400_, 9);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1412_ = v___x_1400_;
v_isShared_1413_ = v_isSharedCheck_1421_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_snapshotTasks_1410_);
lean_inc(v_infoState_1409_);
lean_inc(v_messages_1408_);
lean_inc(v_recordedDeps_1407_);
lean_inc(v_cache_1406_);
lean_inc(v_traceState_1405_);
lean_inc(v_auxDeclNGen_1404_);
lean_inc(v_ngen_1403_);
lean_inc(v_nextMacroScope_1402_);
lean_inc(v_env_1401_);
lean_dec(v___x_1400_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1421_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1417_; 
v___x_1414_ = lean_box(0);
v___x_1415_ = l_Lean_MessageLog_add(v___x_1399_, v_messages_1408_);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 7, v___x_1415_);
v___x_1417_ = v___x_1412_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_env_1401_);
lean_ctor_set(v_reuseFailAlloc_1420_, 1, v_nextMacroScope_1402_);
lean_ctor_set(v_reuseFailAlloc_1420_, 2, v_ngen_1403_);
lean_ctor_set(v_reuseFailAlloc_1420_, 3, v_auxDeclNGen_1404_);
lean_ctor_set(v_reuseFailAlloc_1420_, 4, v_traceState_1405_);
lean_ctor_set(v_reuseFailAlloc_1420_, 5, v_cache_1406_);
lean_ctor_set(v_reuseFailAlloc_1420_, 6, v_recordedDeps_1407_);
lean_ctor_set(v_reuseFailAlloc_1420_, 7, v___x_1415_);
lean_ctor_set(v_reuseFailAlloc_1420_, 8, v_infoState_1409_);
lean_ctor_set(v_reuseFailAlloc_1420_, 9, v_snapshotTasks_1410_);
v___x_1417_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1418_ = lean_st_ref_put(v___y_1394_, v___x_1417_);
v___x_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1414_);
return v___x_1419_;
}
}
}
v___jp_1422_:
{
lean_object* v_fileName_1431_; lean_object* v_fileMap_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v_a_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1448_; 
v_fileName_1431_ = lean_ctor_get(v___y_1425_, 0);
v_fileMap_1432_ = lean_ctor_get(v___y_1425_, 1);
v___x_1433_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1377_);
v___x_1434_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44_spec__47(v___x_1433_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
v_a_1435_ = lean_ctor_get(v___x_1434_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1437_ = v___x_1434_;
v_isShared_1438_ = v_isSharedCheck_1448_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_a_1435_);
lean_dec(v___x_1434_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1448_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
lean_inc_ref_n(v_fileMap_1432_, 2);
v___x_1439_ = l_Lean_FileMap_toPosition(v_fileMap_1432_, v___y_1429_);
lean_dec(v___y_1429_);
v___x_1440_ = l_Lean_FileMap_toPosition(v_fileMap_1432_, v___y_1430_);
lean_dec(v___y_1430_);
v___x_1441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1440_);
v___x_1442_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48___closed__0));
if (v___y_1427_ == 0)
{
lean_del_object(v___x_1437_);
lean_dec_ref(v___y_1424_);
v___y_1386_ = v___y_1426_;
v___y_1387_ = v_a_1435_;
v___y_1388_ = v___y_1428_;
v___y_1389_ = v___x_1442_;
v___y_1390_ = v___x_1441_;
v___y_1391_ = v___x_1439_;
v___y_1392_ = v_fileName_1431_;
v_toCold_1393_ = v___y_1423_;
v___y_1394_ = v___y_1383_;
goto v___jp_1385_;
}
else
{
uint8_t v___x_1443_; 
lean_inc(v_a_1435_);
v___x_1443_ = l_Lean_MessageData_hasTag(v___y_1424_, v_a_1435_);
if (v___x_1443_ == 0)
{
lean_object* v___x_1444_; lean_object* v___x_1446_; 
lean_dec_ref_known(v___x_1441_, 1);
lean_dec_ref(v___x_1439_);
lean_dec(v_a_1435_);
v___x_1444_ = lean_box(0);
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 0, v___x_1444_);
v___x_1446_ = v___x_1437_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1444_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
else
{
lean_del_object(v___x_1437_);
v___y_1386_ = v___y_1426_;
v___y_1387_ = v_a_1435_;
v___y_1388_ = v___y_1428_;
v___y_1389_ = v___x_1442_;
v___y_1390_ = v___x_1441_;
v___y_1391_ = v___x_1439_;
v___y_1392_ = v_fileName_1431_;
v_toCold_1393_ = v___y_1423_;
v___y_1394_ = v___y_1383_;
goto v___jp_1385_;
}
}
}
}
v___jp_1449_:
{
lean_object* v___x_1457_; 
v___x_1457_ = l_Lean_Syntax_getTailPos_x3f(v___y_1453_, v___y_1455_);
lean_dec(v___y_1453_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_inc(v___y_1456_);
v___y_1423_ = v___y_1450_;
v___y_1424_ = v___y_1452_;
v___y_1425_ = v___y_1450_;
v___y_1426_ = v___y_1454_;
v___y_1427_ = v___y_1451_;
v___y_1428_ = v___y_1455_;
v___y_1429_ = v___y_1456_;
v___y_1430_ = v___y_1456_;
goto v___jp_1422_;
}
else
{
lean_object* v_val_1458_; 
v_val_1458_ = lean_ctor_get(v___x_1457_, 0);
lean_inc(v_val_1458_);
lean_dec_ref_known(v___x_1457_, 1);
v___y_1423_ = v___y_1450_;
v___y_1424_ = v___y_1452_;
v___y_1425_ = v___y_1450_;
v___y_1426_ = v___y_1454_;
v___y_1427_ = v___y_1451_;
v___y_1428_ = v___y_1455_;
v___y_1429_ = v___y_1456_;
v___y_1430_ = v_val_1458_;
goto v___jp_1422_;
}
}
v___jp_1459_:
{
lean_object* v_toCold_1463_; lean_object* v_ref_1464_; uint8_t v_suppressElabErrors_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___f_1468_; lean_object* v_ref_1469_; lean_object* v___x_1470_; 
v_toCold_1463_ = lean_ctor_get(v___y_1382_, 0);
v_ref_1464_ = lean_ctor_get(v___y_1382_, 2);
v_suppressElabErrors_1465_ = lean_ctor_get_uint8(v___y_1382_, sizeof(void*)*3 + 2);
v___x_1466_ = lean_box(v_suppressElabErrors_1465_);
v___x_1467_ = lean_box(v___y_1460_);
v___f_1468_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1468_, 0, v___x_1466_);
lean_closure_set(v___f_1468_, 1, v___x_1467_);
v_ref_1469_ = l_Lean_replaceRef(v_ref_1376_, v_ref_1464_);
v___x_1470_ = l_Lean_Syntax_getPos_x3f(v_ref_1469_, v___y_1461_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v___x_1471_; 
v___x_1471_ = lean_unsigned_to_nat(0u);
v___y_1450_ = v_toCold_1463_;
v___y_1451_ = v_suppressElabErrors_1465_;
v___y_1452_ = v___f_1468_;
v___y_1453_ = v_ref_1469_;
v___y_1454_ = v___y_1462_;
v___y_1455_ = v___y_1461_;
v___y_1456_ = v___x_1471_;
goto v___jp_1449_;
}
else
{
lean_object* v_val_1472_; 
v_val_1472_ = lean_ctor_get(v___x_1470_, 0);
lean_inc(v_val_1472_);
lean_dec_ref_known(v___x_1470_, 1);
v___y_1450_ = v_toCold_1463_;
v___y_1451_ = v_suppressElabErrors_1465_;
v___y_1452_ = v___f_1468_;
v___y_1453_ = v_ref_1469_;
v___y_1454_ = v___y_1462_;
v___y_1455_ = v___y_1461_;
v___y_1456_ = v_val_1472_;
goto v___jp_1449_;
}
}
v___jp_1474_:
{
if (v___y_1477_ == 0)
{
v___y_1460_ = v___y_1475_;
v___y_1461_ = v___y_1476_;
v___y_1462_ = v_severity_1378_;
goto v___jp_1459_;
}
else
{
v___y_1460_ = v___y_1475_;
v___y_1461_ = v___y_1476_;
v___y_1462_ = v___x_1473_;
goto v___jp_1459_;
}
}
v___jp_1478_:
{
if (v___y_1479_ == 0)
{
uint8_t v___x_1480_; uint8_t v___x_1481_; 
v___x_1480_ = 1;
v___x_1481_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1378_, v___x_1480_);
if (v___x_1481_ == 0)
{
v___y_1475_ = v___y_1479_;
v___y_1476_ = v___y_1479_;
v___y_1477_ = v___x_1481_;
goto v___jp_1474_;
}
else
{
lean_object* v___x_1482_; lean_object* v___x_1483_; uint8_t v___x_1484_; 
v___x_1482_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1382_);
v___x_1483_ = l_Lean_warningAsError;
v___x_1484_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4(v___x_1482_, v___x_1483_);
lean_dec_ref(v___x_1482_);
v___y_1475_ = v___y_1479_;
v___y_1476_ = v___y_1479_;
v___y_1477_ = v___x_1484_;
goto v___jp_1474_;
}
}
else
{
lean_object* v___x_1485_; lean_object* v___x_1486_; 
lean_dec_ref(v_msgData_1377_);
v___x_1485_ = lean_box(0);
v___x_1486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1485_);
return v___x_1486_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44___boxed(lean_object* v_ref_1489_, lean_object* v_msgData_1490_, lean_object* v_severity_1491_, lean_object* v_isSilent_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
uint8_t v_severity_boxed_1498_; uint8_t v_isSilent_boxed_1499_; lean_object* v_res_1500_; 
v_severity_boxed_1498_ = lean_unbox(v_severity_1491_);
v_isSilent_boxed_1499_ = lean_unbox(v_isSilent_1492_);
v_res_1500_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44(v_ref_1489_, v_msgData_1490_, v_severity_boxed_1498_, v_isSilent_boxed_1499_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v_ref_1489_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42(lean_object* v_msgData_1501_, uint8_t v_severity_1502_, uint8_t v_isSilent_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v_ref_1509_; lean_object* v___x_1510_; 
v_ref_1509_ = lean_ctor_get(v___y_1506_, 2);
v___x_1510_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44(v_ref_1509_, v_msgData_1501_, v_severity_1502_, v_isSilent_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42___boxed(lean_object* v_msgData_1511_, lean_object* v_severity_1512_, lean_object* v_isSilent_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
uint8_t v_severity_boxed_1519_; uint8_t v_isSilent_boxed_1520_; lean_object* v_res_1521_; 
v_severity_boxed_1519_ = lean_unbox(v_severity_1512_);
v_isSilent_boxed_1520_ = lean_unbox(v_isSilent_1513_);
v_res_1521_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42(v_msgData_1511_, v_severity_boxed_1519_, v_isSilent_boxed_1520_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38(lean_object* v_msgData_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
uint8_t v___x_1528_; uint8_t v___x_1529_; lean_object* v___x_1530_; 
v___x_1528_ = 1;
v___x_1529_ = 0;
v___x_1530_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42(v_msgData_1522_, v___x_1528_, v___x_1529_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38___boxed(lean_object* v_msgData_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
lean_object* v_res_1537_; 
v_res_1537_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38(v_msgData_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
return v_res_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37___redArg(lean_object* v_opt_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v___x_1541_; uint8_t v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1541_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1539_);
v___x_1542_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4(v___x_1541_, v_opt_1538_);
lean_dec_ref(v___x_1541_);
v___x_1543_ = lean_box(v___x_1542_);
v___x_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1543_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37___redArg___boxed(lean_object* v_opt_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_){
_start:
{
lean_object* v_res_1548_; 
v_res_1548_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37___redArg(v_opt_1545_, v___y_1546_);
lean_dec_ref(v___y_1546_);
lean_dec_ref(v_opt_1545_);
return v_res_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32(lean_object* v_id_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_){
_start:
{
lean_object* v___x_1555_; lean_object* v_env_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1578_; 
v___x_1555_ = lean_st_ref_get(v___y_1553_);
v_env_1556_ = lean_ctor_get(v___x_1555_, 0);
lean_inc_ref(v_env_1556_);
lean_dec(v___x_1555_);
v___x_1557_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1558_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37___redArg(v___x_1557_, v___y_1552_);
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1561_ = v___x_1558_;
v_isShared_1562_ = v_isSharedCheck_1578_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1558_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1578_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
uint8_t v_isExporting_1568_; 
v_isExporting_1568_ = lean_ctor_get_uint8(v_env_1556_, sizeof(void*)*13);
lean_dec_ref(v_env_1556_);
if (v_isExporting_1568_ == 0)
{
lean_dec(v_a_1559_);
lean_dec(v_id_1549_);
goto v___jp_1563_;
}
else
{
uint8_t v___x_1569_; 
v___x_1569_ = l_Lean_isPrivateName(v_id_1549_);
if (v___x_1569_ == 0)
{
lean_dec(v_a_1559_);
lean_dec(v_id_1549_);
goto v___jp_1563_;
}
else
{
uint8_t v___x_1570_; 
v___x_1570_ = lean_unbox(v_a_1559_);
lean_dec(v_a_1559_);
if (v___x_1570_ == 0)
{
lean_dec(v_id_1549_);
goto v___jp_1563_;
}
else
{
lean_object* v___x_1571_; uint8_t v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
lean_del_object(v___x_1561_);
v___x_1571_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___closed__1);
v___x_1572_ = 0;
v___x_1573_ = l_Lean_MessageData_ofConstName(v_id_1549_, v___x_1572_);
v___x_1574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1571_);
lean_ctor_set(v___x_1574_, 1, v___x_1573_);
v___x_1575_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___closed__3);
v___x_1576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1574_);
lean_ctor_set(v___x_1576_, 1, v___x_1575_);
v___x_1577_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38(v___x_1576_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
return v___x_1577_;
}
}
}
v___jp_1563_:
{
lean_object* v___x_1564_; lean_object* v___x_1566_; 
v___x_1564_ = lean_box(0);
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 0, v___x_1564_);
v___x_1566_ = v___x_1561_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1564_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___boxed(lean_object* v_id_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32(v_id_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26(lean_object* v_id_1586_, uint8_t v_enableLog_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_){
_start:
{
lean_object* v___x_1593_; lean_object* v_toCold_1594_; lean_object* v_env_1595_; lean_object* v_currNamespace_1596_; lean_object* v_openDecls_1597_; lean_object* v___x_1598_; lean_object* v_res_1599_; lean_object* v___x_1600_; 
v___x_1593_ = lean_st_ref_get(v___y_1591_);
v_toCold_1594_ = lean_ctor_get(v___y_1590_, 0);
v_env_1595_ = lean_ctor_get(v___x_1593_, 0);
lean_inc_ref(v_env_1595_);
lean_dec(v___x_1593_);
v_currNamespace_1596_ = lean_ctor_get(v_toCold_1594_, 4);
v_openDecls_1597_ = lean_ctor_get(v_toCold_1594_, 5);
v___x_1598_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1590_);
lean_inc(v_openDecls_1597_);
lean_inc(v_currNamespace_1596_);
v_res_1599_ = l_Lean_ResolveName_resolveGlobalName(v_env_1595_, v___x_1598_, v_currNamespace_1596_, v_openDecls_1597_, v_id_1586_);
lean_dec_ref(v___x_1598_);
v___x_1600_ = lean_st_ref_get(v___y_1591_);
if (v_enableLog_1587_ == 0)
{
lean_object* v___x_1601_; 
lean_dec(v___x_1600_);
v___x_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1601_, 0, v_res_1599_);
return v___x_1601_;
}
else
{
lean_object* v_env_1602_; uint8_t v_isExporting_1603_; 
v_env_1602_ = lean_ctor_get(v___x_1600_, 0);
lean_inc_ref(v_env_1602_);
lean_dec(v___x_1600_);
v_isExporting_1603_ = lean_ctor_get_uint8(v_env_1602_, sizeof(void*)*13);
lean_dec_ref(v_env_1602_);
if (v_isExporting_1603_ == 0)
{
lean_object* v___x_1604_; 
v___x_1604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1604_, 0, v_res_1599_);
return v___x_1604_;
}
else
{
lean_object* v___x_1605_; 
v___x_1605_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__31(v_res_1599_);
if (lean_obj_tag(v___x_1605_) == 1)
{
lean_object* v_val_1606_; lean_object* v_fst_1607_; lean_object* v___x_1608_; 
v_val_1606_ = lean_ctor_get(v___x_1605_, 0);
lean_inc(v_val_1606_);
lean_dec_ref_known(v___x_1605_, 1);
v_fst_1607_ = lean_ctor_get(v_val_1606_, 0);
lean_inc(v_fst_1607_);
lean_dec(v_val_1606_);
v___x_1608_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32(v_fst_1607_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1615_; 
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1615_ == 0)
{
lean_object* v_unused_1616_; 
v_unused_1616_ = lean_ctor_get(v___x_1608_, 0);
lean_dec(v_unused_1616_);
v___x_1610_ = v___x_1608_;
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
else
{
lean_dec(v___x_1608_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1613_; 
if (v_isShared_1611_ == 0)
{
lean_ctor_set(v___x_1610_, 0, v_res_1599_);
v___x_1613_ = v___x_1610_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_res_1599_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
else
{
lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1624_; 
lean_dec(v_res_1599_);
v_a_1617_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1619_ = v___x_1608_;
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v___x_1608_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1622_; 
if (v_isShared_1620_ == 0)
{
v___x_1622_ = v___x_1619_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_a_1617_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
}
else
{
lean_object* v___x_1625_; 
lean_dec(v___x_1605_);
v___x_1625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1625_, 0, v_res_1599_);
return v___x_1625_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26___boxed(lean_object* v_id_1626_, lean_object* v_enableLog_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
uint8_t v_enableLog_boxed_1633_; lean_object* v_res_1634_; 
v_enableLog_boxed_1633_ = lean_unbox(v_enableLog_1627_);
v_res_1634_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26(v_id_1626_, v_enableLog_boxed_1633_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20(lean_object* v_view_1635_, lean_object* v_findLocalDecl_x3f_1636_, lean_object* v_n_1637_, lean_object* v_projs_1638_, uint8_t v_globalDeclFound_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
lean_object* v___y_1646_; lean_object* v___y_1647_; uint8_t v_globalDeclFoundNext_1648_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v_imported_1655_; lean_object* v_ctx_1656_; lean_object* v_scopes_1657_; lean_object* v_givenNameView_1658_; uint8_t v___y_1660_; 
v_imported_1655_ = lean_ctor_get(v_view_1635_, 1);
v_ctx_1656_ = lean_ctor_get(v_view_1635_, 2);
v_scopes_1657_ = lean_ctor_get(v_view_1635_, 3);
lean_inc(v_scopes_1657_);
lean_inc(v_ctx_1656_);
lean_inc(v_imported_1655_);
lean_inc(v_n_1637_);
v_givenNameView_1658_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_givenNameView_1658_, 0, v_n_1637_);
lean_ctor_set(v_givenNameView_1658_, 1, v_imported_1655_);
lean_ctor_set(v_givenNameView_1658_, 2, v_ctx_1656_);
lean_ctor_set(v_givenNameView_1658_, 3, v_scopes_1657_);
if (v_globalDeclFound_1639_ == 0)
{
v___y_1660_ = v_globalDeclFound_1639_;
goto v___jp_1659_;
}
else
{
uint8_t v___x_1695_; 
v___x_1695_ = l_List_isEmpty___redArg(v_projs_1638_);
if (v___x_1695_ == 0)
{
v___y_1660_ = v_globalDeclFound_1639_;
goto v___jp_1659_;
}
else
{
uint8_t v___x_1696_; 
v___x_1696_ = 0;
v___y_1660_ = v___x_1696_;
goto v___jp_1659_;
}
}
v___jp_1645_:
{
lean_object* v___x_1653_; 
v___x_1653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___y_1647_);
lean_ctor_set(v___x_1653_, 1, v_projs_1638_);
v_n_1637_ = v___y_1646_;
v_projs_1638_ = v___x_1653_;
v_globalDeclFound_1639_ = v_globalDeclFoundNext_1648_;
v___y_1640_ = v___y_1649_;
v___y_1641_ = v___y_1650_;
v___y_1642_ = v___y_1651_;
v___y_1643_ = v___y_1652_;
goto _start;
}
v___jp_1659_:
{
lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1661_ = lean_box(v___y_1660_);
lean_inc_ref(v_findLocalDecl_x3f_1636_);
lean_inc_ref(v_givenNameView_1658_);
v___x_1662_ = lean_apply_2(v_findLocalDecl_x3f_1636_, v_givenNameView_1658_, v___x_1661_);
if (lean_obj_tag(v___x_1662_) == 0)
{
if (lean_obj_tag(v_n_1637_) == 1)
{
if (v_globalDeclFound_1639_ == 0)
{
lean_object* v_pre_1663_; lean_object* v_str_1664_; uint8_t v_globalDeclFoundNext_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
v_pre_1663_ = lean_ctor_get(v_n_1637_, 0);
lean_inc(v_pre_1663_);
v_str_1664_ = lean_ctor_get(v_n_1637_, 1);
lean_inc_ref(v_str_1664_);
lean_dec_ref_known(v_n_1637_, 2);
v_globalDeclFoundNext_1665_ = 1;
v___x_1666_ = l_Lean_MacroScopesView_review(v_givenNameView_1658_);
v___x_1667_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26(v___x_1666_, v_globalDeclFound_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_object* v_a_1668_; lean_object* v___x_1669_; lean_object* v_r_1670_; uint8_t v___x_1671_; 
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
lean_inc(v_a_1668_);
lean_dec_ref_known(v___x_1667_, 1);
v___x_1669_ = lean_box(0);
v_r_1670_ = l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__27(v_a_1668_, v___x_1669_);
v___x_1671_ = l_List_isEmpty___redArg(v_r_1670_);
lean_dec(v_r_1670_);
if (v___x_1671_ == 0)
{
v___y_1646_ = v_pre_1663_;
v___y_1647_ = v_str_1664_;
v_globalDeclFoundNext_1648_ = v_globalDeclFoundNext_1665_;
v___y_1649_ = v___y_1640_;
v___y_1650_ = v___y_1641_;
v___y_1651_ = v___y_1642_;
v___y_1652_ = v___y_1643_;
goto v___jp_1645_;
}
else
{
v___y_1646_ = v_pre_1663_;
v___y_1647_ = v_str_1664_;
v_globalDeclFoundNext_1648_ = v_globalDeclFound_1639_;
v___y_1649_ = v___y_1640_;
v___y_1650_ = v___y_1641_;
v___y_1651_ = v___y_1642_;
v___y_1652_ = v___y_1643_;
goto v___jp_1645_;
}
}
else
{
lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1679_; 
lean_dec_ref(v_str_1664_);
lean_dec(v_pre_1663_);
lean_dec(v_projs_1638_);
lean_dec_ref(v_findLocalDecl_x3f_1636_);
v_a_1672_ = lean_ctor_get(v___x_1667_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1674_ = v___x_1667_;
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v___x_1667_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1677_; 
if (v_isShared_1675_ == 0)
{
v___x_1677_ = v___x_1674_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_a_1672_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
}
else
{
lean_object* v_pre_1680_; lean_object* v_str_1681_; 
lean_dec_ref_known(v_givenNameView_1658_, 4);
v_pre_1680_ = lean_ctor_get(v_n_1637_, 0);
lean_inc(v_pre_1680_);
v_str_1681_ = lean_ctor_get(v_n_1637_, 1);
lean_inc_ref(v_str_1681_);
lean_dec_ref_known(v_n_1637_, 2);
v___y_1646_ = v_pre_1680_;
v___y_1647_ = v_str_1681_;
v_globalDeclFoundNext_1648_ = v_globalDeclFound_1639_;
v___y_1649_ = v___y_1640_;
v___y_1650_ = v___y_1641_;
v___y_1651_ = v___y_1642_;
v___y_1652_ = v___y_1643_;
goto v___jp_1645_;
}
}
else
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
lean_dec_ref_known(v_givenNameView_1658_, 4);
lean_dec(v_projs_1638_);
lean_dec(v_n_1637_);
lean_dec_ref(v_findLocalDecl_x3f_1636_);
v___x_1682_ = lean_box(0);
v___x_1683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1682_);
return v___x_1683_;
}
}
else
{
lean_object* v_val_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1694_; 
lean_dec_ref_known(v_givenNameView_1658_, 4);
lean_dec(v_n_1637_);
lean_dec_ref(v_findLocalDecl_x3f_1636_);
v_val_1684_ = lean_ctor_get(v___x_1662_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1686_ = v___x_1662_;
v_isShared_1687_ = v_isSharedCheck_1694_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_val_1684_);
lean_dec(v___x_1662_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1694_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1691_; 
v___x_1688_ = l_Lean_LocalDecl_toExpr(v_val_1684_);
v___x_1689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1688_);
lean_ctor_set(v___x_1689_, 1, v_projs_1638_);
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 0, v___x_1689_);
v___x_1691_ = v___x_1686_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v___x_1689_);
v___x_1691_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
lean_object* v___x_1692_; 
v___x_1692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1691_);
return v___x_1692_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20___boxed(lean_object* v_view_1697_, lean_object* v_findLocalDecl_x3f_1698_, lean_object* v_n_1699_, lean_object* v_projs_1700_, lean_object* v_globalDeclFound_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
uint8_t v_globalDeclFound_boxed_1707_; lean_object* v_res_1708_; 
v_globalDeclFound_boxed_1707_ = lean_unbox(v_globalDeclFound_1701_);
v_res_1708_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20(v_view_1697_, v_findLocalDecl_x3f_1698_, v_n_1699_, v_projs_1700_, v_globalDeclFound_boxed_1707_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec_ref(v_view_1697_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11(lean_object* v_n_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
lean_object* v_lctx_1715_; lean_object* v_toCold_1716_; lean_object* v_decls_1717_; lean_object* v_auxDeclToFullName_1718_; lean_object* v_currNamespace_1719_; lean_object* v_view_1720_; lean_object* v_name_1721_; lean_object* v_findLocalDecl_x3f_1722_; lean_object* v___x_1723_; uint8_t v___x_1724_; lean_object* v___x_1725_; 
v_lctx_1715_ = lean_ctor_get(v___y_1710_, 2);
v_toCold_1716_ = lean_ctor_get(v___y_1712_, 0);
v_decls_1717_ = lean_ctor_get(v_lctx_1715_, 1);
v_auxDeclToFullName_1718_ = lean_ctor_get(v_lctx_1715_, 2);
v_currNamespace_1719_ = lean_ctor_get(v_toCold_1716_, 4);
v_view_1720_ = l_Lean_extractMacroScopes(v_n_1709_);
v_name_1721_ = lean_ctor_get(v_view_1720_, 0);
lean_inc(v_name_1721_);
lean_inc_ref(v_decls_1717_);
lean_inc(v_currNamespace_1719_);
lean_inc(v_auxDeclToFullName_1718_);
v_findLocalDecl_x3f_1722_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11___lam__0___boxed), 5, 3);
lean_closure_set(v_findLocalDecl_x3f_1722_, 0, v_auxDeclToFullName_1718_);
lean_closure_set(v_findLocalDecl_x3f_1722_, 1, v_currNamespace_1719_);
lean_closure_set(v_findLocalDecl_x3f_1722_, 2, v_decls_1717_);
v___x_1723_ = lean_box(0);
v___x_1724_ = 0;
v___x_1725_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20(v_view_1720_, v_findLocalDecl_x3f_1722_, v_name_1721_, v___x_1723_, v___x_1724_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
lean_dec_ref(v_view_1720_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11___boxed(lean_object* v_n_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11(v_n_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5___lam__0(uint8_t v___x_1733_, lean_object* v_n_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v___x_1740_; 
v___x_1740_ = l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11(v_n_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v_a_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1754_; 
v_a_1741_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1743_ = v___x_1740_;
v_isShared_1744_ = v_isSharedCheck_1754_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_a_1741_);
lean_dec(v___x_1740_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1754_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
if (lean_obj_tag(v_a_1741_) == 0)
{
uint8_t v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1748_; 
v___x_1745_ = 1;
v___x_1746_ = lean_box(v___x_1745_);
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 0, v___x_1746_);
v___x_1748_ = v___x_1743_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v___x_1746_);
v___x_1748_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
return v___x_1748_;
}
}
else
{
lean_object* v___x_1750_; lean_object* v___x_1752_; 
lean_dec_ref_known(v_a_1741_, 1);
v___x_1750_ = lean_box(v___x_1733_);
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 0, v___x_1750_);
v___x_1752_ = v___x_1743_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v___x_1750_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
}
else
{
lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1762_; 
v_a_1755_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1757_ = v___x_1740_;
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___x_1740_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1760_; 
if (v_isShared_1758_ == 0)
{
v___x_1760_ = v___x_1757_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_a_1755_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5___lam__0___boxed(lean_object* v___x_1763_, lean_object* v_n_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
uint8_t v___x_45478__boxed_1770_; lean_object* v_res_1771_; 
v___x_45478__boxed_1770_ = lean_unbox(v___x_1763_);
v_res_1771_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5___lam__0(v___x_45478__boxed_1770_, v_n_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5(lean_object* v_n_u2080_1775_, uint8_t v_fullNames_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
uint8_t v___x_1782_; lean_object* v___f_1783_; lean_object* v___x_1784_; 
v___x_1782_ = 0;
v___f_1783_ = ((lean_object*)(l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5___closed__0));
v___x_1784_ = l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12(v_n_u2080_1775_, v_fullNames_1776_, v___x_1782_, v___f_1783_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
return v___x_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5___boxed(lean_object* v_n_u2080_1785_, lean_object* v_fullNames_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
uint8_t v_fullNames_boxed_1792_; lean_object* v_res_1793_; 
v_fullNames_boxed_1792_ = lean_unbox(v_fullNames_1786_);
v_res_1793_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5(v_n_u2080_1785_, v_fullNames_boxed_1792_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3_spec__8___redArg(lean_object* v_o_1794_, lean_object* v___y_1795_){
_start:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v_env_1799_; lean_object* v___x_1800_; lean_object* v_toEnvExtension_1801_; lean_object* v_asyncMode_1802_; lean_object* v___x_1803_; uint8_t v___x_1804_; lean_object* v___x_1805_; lean_object* v_merged_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1814_; 
v___x_1797_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_1798_ = lean_st_ref_get(v___y_1795_);
v_env_1799_ = lean_ctor_get(v___x_1798_, 0);
lean_inc_ref(v_env_1799_);
lean_dec(v___x_1798_);
v___x_1800_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_1801_ = lean_ctor_get(v___x_1800_, 0);
v_asyncMode_1802_ = lean_ctor_get(v_toEnvExtension_1801_, 2);
v___x_1803_ = lean_box(0);
v___x_1804_ = 0;
v___x_1805_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1797_, v___x_1800_, v_env_1799_, v_asyncMode_1802_, v___x_1803_, v___x_1804_);
v_merged_1806_ = lean_ctor_get(v___x_1805_, 0);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1814_ == 0)
{
lean_object* v_unused_1815_; 
v_unused_1815_ = lean_ctor_get(v___x_1805_, 1);
lean_dec(v_unused_1815_);
v___x_1808_ = v___x_1805_;
v_isShared_1809_ = v_isSharedCheck_1814_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_merged_1806_);
lean_dec(v___x_1805_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1814_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1811_; 
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 1, v_merged_1806_);
lean_ctor_set(v___x_1808_, 0, v_o_1794_);
v___x_1811_ = v___x_1808_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_o_1794_);
lean_ctor_set(v_reuseFailAlloc_1813_, 1, v_merged_1806_);
v___x_1811_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
lean_object* v___x_1812_; 
v___x_1812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1811_);
return v___x_1812_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3_spec__8___redArg___boxed(lean_object* v_o_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3_spec__8___redArg(v_o_1816_, v___y_1817_);
lean_dec(v___y_1817_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3(lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1823_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1820_);
v___x_1824_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3_spec__8___redArg(v___x_1823_, v___y_1821_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3___boxed(lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3(v___y_1825_, v___y_1826_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___lam__0(lean_object* v___x_1829_, lean_object* v_entry_1830_, lean_object* v_s_1831_){
_start:
{
lean_object* v_addEntryFn_1832_; lean_object* v_importedEntries_1833_; lean_object* v_state_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1842_; 
v_addEntryFn_1832_ = lean_ctor_get(v___x_1829_, 3);
lean_inc(v_addEntryFn_1832_);
lean_dec_ref(v___x_1829_);
v_importedEntries_1833_ = lean_ctor_get(v_s_1831_, 0);
v_state_1834_ = lean_ctor_get(v_s_1831_, 1);
v_isSharedCheck_1842_ = !lean_is_exclusive(v_s_1831_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1836_ = v_s_1831_;
v_isShared_1837_ = v_isSharedCheck_1842_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_state_1834_);
lean_inc(v_importedEntries_1833_);
lean_dec(v_s_1831_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1842_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v_state_1838_; lean_object* v___x_1840_; 
v_state_1838_ = lean_apply_2(v_addEntryFn_1832_, v_state_1834_, v_entry_1830_);
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 1, v_state_1838_);
v___x_1840_ = v___x_1836_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_importedEntries_1833_);
lean_ctor_set(v_reuseFailAlloc_1841_, 1, v_state_1838_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1843_; 
v___x_1843_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1843_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1844_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1844_);
return v___x_1845_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1846_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1847_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_1848_ = lean_unsigned_to_nat(0u);
v___x_1849_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1848_);
lean_ctor_set(v___x_1849_, 1, v___x_1848_);
lean_ctor_set(v___x_1849_, 2, v___x_1848_);
lean_ctor_set(v___x_1849_, 3, v___x_1848_);
lean_ctor_set(v___x_1849_, 4, v___x_1847_);
lean_ctor_set(v___x_1849_, 5, v___x_1847_);
lean_ctor_set(v___x_1849_, 6, v___x_1847_);
lean_ctor_set(v___x_1849_, 7, v___x_1847_);
lean_ctor_set(v___x_1849_, 8, v___x_1847_);
lean_ctor_set(v___x_1849_, 9, v___x_1847_);
lean_ctor_set(v___x_1849_, 10, v___x_1847_);
lean_ctor_set(v___x_1849_, 11, v___x_1846_);
return v___x_1849_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1850_ = lean_unsigned_to_nat(32u);
v___x_1851_ = lean_mk_empty_array_with_capacity(v___x_1850_);
v___x_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1851_);
return v___x_1852_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1853_ = ((size_t)5ULL);
v___x_1854_ = lean_unsigned_to_nat(0u);
v___x_1855_ = lean_unsigned_to_nat(32u);
v___x_1856_ = lean_mk_empty_array_with_capacity(v___x_1855_);
v___x_1857_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_1858_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1858_, 0, v___x_1857_);
lean_ctor_set(v___x_1858_, 1, v___x_1856_);
lean_ctor_set(v___x_1858_, 2, v___x_1854_);
lean_ctor_set(v___x_1858_, 3, v___x_1854_);
lean_ctor_set_usize(v___x_1858_, 4, v___x_1853_);
return v___x_1858_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1859_ = lean_box(1);
v___x_1860_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_1861_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_1862_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1861_);
lean_ctor_set(v___x_1862_, 1, v___x_1860_);
lean_ctor_set(v___x_1862_, 2, v___x_1859_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
lean_object* v___x_1867_; lean_object* v_toCold_1868_; lean_object* v_env_1869_; lean_object* v_options_1870_; uint8_t v___x_1871_; lean_object* v_env_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1867_ = lean_st_ref_get(v___y_1865_);
v_toCold_1868_ = lean_ctor_get(v___y_1864_, 0);
v_env_1869_ = lean_ctor_get(v___x_1867_, 0);
lean_inc_ref(v_env_1869_);
lean_dec(v___x_1867_);
v_options_1870_ = lean_ctor_get(v_toCold_1868_, 2);
v___x_1871_ = 0;
v_env_1872_ = l_Lean_Environment_setRecordingDeps(v_env_1869_, v___x_1871_);
v___x_1873_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_1874_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_1870_);
v___x_1875_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1875_, 0, v_env_1872_);
lean_ctor_set(v___x_1875_, 1, v___x_1873_);
lean_ctor_set(v___x_1875_, 2, v___x_1874_);
lean_ctor_set(v___x_1875_, 3, v_options_1870_);
v___x_1876_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1875_);
lean_ctor_set(v___x_1876_, 1, v_msgData_1863_);
v___x_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0(v_msgData_1878_, v___y_1879_, v___y_1880_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
return v_res_1882_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0(void){
_start:
{
lean_object* v___x_1883_; double v___x_1884_; 
v___x_1883_ = lean_unsigned_to_nat(0u);
v___x_1884_ = lean_float_of_nat(v___x_1883_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__9(lean_object* v_cls_1887_, lean_object* v_msg_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v_ref_1892_; lean_object* v___x_1893_; lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1939_; 
v_ref_1892_ = lean_ctor_get(v___y_1889_, 2);
v___x_1893_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0(v_msg_1888_, v___y_1889_, v___y_1890_);
v_a_1894_ = lean_ctor_get(v___x_1893_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1896_ = v___x_1893_;
v_isShared_1897_ = v_isSharedCheck_1939_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1893_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1939_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1898_; lean_object* v_traceState_1899_; lean_object* v_env_1900_; lean_object* v_nextMacroScope_1901_; lean_object* v_ngen_1902_; lean_object* v_auxDeclNGen_1903_; lean_object* v_cache_1904_; lean_object* v_recordedDeps_1905_; lean_object* v_messages_1906_; lean_object* v_infoState_1907_; lean_object* v_snapshotTasks_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1938_; 
v___x_1898_ = lean_st_ref_take(v___y_1890_);
v_traceState_1899_ = lean_ctor_get(v___x_1898_, 4);
v_env_1900_ = lean_ctor_get(v___x_1898_, 0);
v_nextMacroScope_1901_ = lean_ctor_get(v___x_1898_, 1);
v_ngen_1902_ = lean_ctor_get(v___x_1898_, 2);
v_auxDeclNGen_1903_ = lean_ctor_get(v___x_1898_, 3);
v_cache_1904_ = lean_ctor_get(v___x_1898_, 5);
v_recordedDeps_1905_ = lean_ctor_get(v___x_1898_, 6);
v_messages_1906_ = lean_ctor_get(v___x_1898_, 7);
v_infoState_1907_ = lean_ctor_get(v___x_1898_, 8);
v_snapshotTasks_1908_ = lean_ctor_get(v___x_1898_, 9);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1910_ = v___x_1898_;
v_isShared_1911_ = v_isSharedCheck_1938_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_snapshotTasks_1908_);
lean_inc(v_infoState_1907_);
lean_inc(v_messages_1906_);
lean_inc(v_recordedDeps_1905_);
lean_inc(v_cache_1904_);
lean_inc(v_traceState_1899_);
lean_inc(v_auxDeclNGen_1903_);
lean_inc(v_ngen_1902_);
lean_inc(v_nextMacroScope_1901_);
lean_inc(v_env_1900_);
lean_dec(v___x_1898_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1938_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
uint64_t v_tid_1912_; lean_object* v_traces_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1937_; 
v_tid_1912_ = lean_ctor_get_uint64(v_traceState_1899_, sizeof(void*)*1);
v_traces_1913_ = lean_ctor_get(v_traceState_1899_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v_traceState_1899_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1915_ = v_traceState_1899_;
v_isShared_1916_ = v_isSharedCheck_1937_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_traces_1913_);
lean_dec(v_traceState_1899_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1937_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; double v___x_1919_; uint8_t v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1928_; 
v___x_1917_ = lean_box(0);
v___x_1918_ = lean_box(0);
v___x_1919_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0);
v___x_1920_ = 0;
v___x_1921_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48___closed__0));
v___x_1922_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1922_, 0, v_cls_1887_);
lean_ctor_set(v___x_1922_, 1, v___x_1918_);
lean_ctor_set(v___x_1922_, 2, v___x_1921_);
lean_ctor_set_float(v___x_1922_, sizeof(void*)*3, v___x_1919_);
lean_ctor_set_float(v___x_1922_, sizeof(void*)*3 + 8, v___x_1919_);
lean_ctor_set_uint8(v___x_1922_, sizeof(void*)*3 + 16, v___x_1920_);
v___x_1923_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__1));
v___x_1924_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1922_);
lean_ctor_set(v___x_1924_, 1, v_a_1894_);
lean_ctor_set(v___x_1924_, 2, v___x_1923_);
lean_inc(v_ref_1892_);
v___x_1925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1925_, 0, v_ref_1892_);
lean_ctor_set(v___x_1925_, 1, v___x_1924_);
v___x_1926_ = l_Lean_PersistentArray_push___redArg(v_traces_1913_, v___x_1925_);
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 0, v___x_1926_);
v___x_1928_ = v___x_1915_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v___x_1926_);
lean_ctor_set_uint64(v_reuseFailAlloc_1936_, sizeof(void*)*1, v_tid_1912_);
v___x_1928_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
lean_object* v___x_1930_; 
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 4, v___x_1928_);
v___x_1930_ = v___x_1910_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_env_1900_);
lean_ctor_set(v_reuseFailAlloc_1935_, 1, v_nextMacroScope_1901_);
lean_ctor_set(v_reuseFailAlloc_1935_, 2, v_ngen_1902_);
lean_ctor_set(v_reuseFailAlloc_1935_, 3, v_auxDeclNGen_1903_);
lean_ctor_set(v_reuseFailAlloc_1935_, 4, v___x_1928_);
lean_ctor_set(v_reuseFailAlloc_1935_, 5, v_cache_1904_);
lean_ctor_set(v_reuseFailAlloc_1935_, 6, v_recordedDeps_1905_);
lean_ctor_set(v_reuseFailAlloc_1935_, 7, v_messages_1906_);
lean_ctor_set(v_reuseFailAlloc_1935_, 8, v_infoState_1907_);
lean_ctor_set(v_reuseFailAlloc_1935_, 9, v_snapshotTasks_1908_);
v___x_1930_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
lean_object* v___x_1931_; lean_object* v___x_1933_; 
v___x_1931_ = lean_st_ref_put(v___y_1890_, v___x_1930_);
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 0, v___x_1917_);
v___x_1933_ = v___x_1896_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v___x_1917_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__9___boxed(lean_object* v_cls_1940_, lean_object* v_msg_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__9(v_cls_1940_, v_msg_1941_, v___y_1942_, v___y_1943_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
return v_res_1945_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17___redArg(lean_object* v_keys_1946_, lean_object* v_i_1947_, lean_object* v_k_1948_){
_start:
{
lean_object* v___x_1949_; uint8_t v___x_1950_; 
v___x_1949_ = lean_array_get_size(v_keys_1946_);
v___x_1950_ = lean_nat_dec_lt(v_i_1947_, v___x_1949_);
if (v___x_1950_ == 0)
{
lean_dec(v_i_1947_);
return v___x_1950_;
}
else
{
lean_object* v_k_x27_1951_; uint8_t v___x_1952_; 
v_k_x27_1951_ = lean_array_fget_borrowed(v_keys_1946_, v_i_1947_);
v___x_1952_ = l_Lean_instBEqExtraModUse_beq(v_k_1948_, v_k_x27_1951_);
if (v___x_1952_ == 0)
{
lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1953_ = lean_unsigned_to_nat(1u);
v___x_1954_ = lean_nat_add(v_i_1947_, v___x_1953_);
lean_dec(v_i_1947_);
v_i_1947_ = v___x_1954_;
goto _start;
}
else
{
lean_dec(v_i_1947_);
return v___x_1950_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17___redArg___boxed(lean_object* v_keys_1956_, lean_object* v_i_1957_, lean_object* v_k_1958_){
_start:
{
uint8_t v_res_1959_; lean_object* v_r_1960_; 
v_res_1959_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17___redArg(v_keys_1956_, v_i_1957_, v_k_1958_);
lean_dec_ref(v_k_1958_);
lean_dec_ref(v_keys_1956_);
v_r_1960_ = lean_box(v_res_1959_);
return v_r_1960_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12___redArg(lean_object* v_x_1961_, size_t v_x_1962_, lean_object* v_x_1963_){
_start:
{
if (lean_obj_tag(v_x_1961_) == 0)
{
lean_object* v_es_1964_; lean_object* v___x_1965_; size_t v___x_1966_; size_t v___x_1967_; lean_object* v_j_1968_; lean_object* v___x_1969_; 
v_es_1964_ = lean_ctor_get(v_x_1961_, 0);
v___x_1965_ = lean_box(2);
v___x_1966_ = ((size_t)31ULL);
v___x_1967_ = lean_usize_land(v_x_1962_, v___x_1966_);
v_j_1968_ = lean_usize_to_nat(v___x_1967_);
v___x_1969_ = lean_array_get_borrowed(v___x_1965_, v_es_1964_, v_j_1968_);
lean_dec(v_j_1968_);
switch(lean_obj_tag(v___x_1969_))
{
case 0:
{
lean_object* v_key_1970_; uint8_t v___x_1971_; 
v_key_1970_ = lean_ctor_get(v___x_1969_, 0);
v___x_1971_ = l_Lean_instBEqExtraModUse_beq(v_x_1963_, v_key_1970_);
return v___x_1971_;
}
case 1:
{
lean_object* v_node_1972_; size_t v___x_1973_; size_t v___x_1974_; 
v_node_1972_ = lean_ctor_get(v___x_1969_, 0);
v___x_1973_ = ((size_t)5ULL);
v___x_1974_ = lean_usize_shift_right(v_x_1962_, v___x_1973_);
v_x_1961_ = v_node_1972_;
v_x_1962_ = v___x_1974_;
goto _start;
}
default: 
{
uint8_t v___x_1976_; 
v___x_1976_ = 0;
return v___x_1976_;
}
}
}
else
{
lean_object* v_ks_1977_; lean_object* v___x_1978_; uint8_t v___x_1979_; 
v_ks_1977_ = lean_ctor_get(v_x_1961_, 0);
v___x_1978_ = lean_unsigned_to_nat(0u);
v___x_1979_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17___redArg(v_ks_1977_, v___x_1978_, v_x_1963_);
return v___x_1979_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12___redArg___boxed(lean_object* v_x_1980_, lean_object* v_x_1981_, lean_object* v_x_1982_){
_start:
{
size_t v_x_45846__boxed_1983_; uint8_t v_res_1984_; lean_object* v_r_1985_; 
v_x_45846__boxed_1983_ = lean_unbox_usize(v_x_1981_);
lean_dec(v_x_1981_);
v_res_1984_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12___redArg(v_x_1980_, v_x_45846__boxed_1983_, v_x_1982_);
lean_dec_ref(v_x_1982_);
lean_dec_ref(v_x_1980_);
v_r_1985_ = lean_box(v_res_1984_);
return v_r_1985_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg(lean_object* v_x_1986_, lean_object* v_x_1987_){
_start:
{
uint64_t v___x_1988_; size_t v___x_1989_; uint8_t v___x_1990_; 
v___x_1988_ = l_Lean_instHashableExtraModUse_hash(v_x_1987_);
v___x_1989_ = lean_uint64_to_usize(v___x_1988_);
v___x_1990_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12___redArg(v_x_1986_, v___x_1989_, v_x_1987_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_x_1991_, lean_object* v_x_1992_){
_start:
{
uint8_t v_res_1993_; lean_object* v_r_1994_; 
v_res_1993_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg(v_x_1991_, v_x_1992_);
lean_dec_ref(v_x_1992_);
lean_dec_ref(v_x_1991_);
v_r_1994_ = lean_box(v_res_1993_);
return v_r_1994_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1995_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_1996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1995_);
return v___x_1996_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1997_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__0);
v___x_1998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1998_, 0, v___x_1997_);
lean_ctor_set(v___x_1998_, 1, v___x_1997_);
return v___x_1998_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__2(void){
_start:
{
lean_object* v___x_1999_; 
v___x_1999_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_1999_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__6(void){
_start:
{
lean_object* v___x_2004_; lean_object* v___x_2005_; 
v___x_2004_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__5));
v___x_2005_ = l_Lean_stringToMessageData(v___x_2004_);
return v___x_2005_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__8(void){
_start:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; 
v___x_2007_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__7));
v___x_2008_ = l_Lean_stringToMessageData(v___x_2007_);
return v___x_2008_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__9(void){
_start:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; 
v___x_2009_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48___closed__0));
v___x_2010_ = l_Lean_stringToMessageData(v___x_2009_);
return v___x_2010_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__11(void){
_start:
{
lean_object* v_cls_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; 
v_cls_2013_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__4));
v___x_2014_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__10));
v___x_2015_ = l_Lean_Name_append(v___x_2014_, v_cls_2013_);
return v___x_2015_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__13(void){
_start:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; 
v___x_2017_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__12));
v___x_2018_ = l_Lean_stringToMessageData(v___x_2017_);
return v___x_2018_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__14(void){
_start:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2019_ = ((lean_object*)(l_Lean_Linter_mkSinceHint___closed__5));
v___x_2020_ = l_Lean_stringToMessageData(v___x_2019_);
return v___x_2020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4(lean_object* v_mod_2025_, uint8_t v_isMeta_2026_, lean_object* v_hint_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_){
_start:
{
lean_object* v___y_2032_; lean_object* v___y_2033_; lean_object* v___y_2034_; lean_object* v___y_2035_; lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v___y_2038_; lean_object* v___y_2039_; lean_object* v___y_2040_; lean_object* v___y_2041_; lean_object* v___y_2042_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v_env_2049_; uint8_t v_isExporting_2050_; lean_object* v_entry_2051_; lean_object* v___x_2052_; lean_object* v_env_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; uint8_t v___x_2058_; 
v___x_2047_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__2);
v___x_2048_ = lean_st_ref_get(v___y_2029_);
v_env_2049_ = lean_ctor_get(v___x_2048_, 0);
lean_inc_ref(v_env_2049_);
lean_dec(v___x_2048_);
v_isExporting_2050_ = lean_ctor_get_uint8(v_env_2049_, sizeof(void*)*13);
lean_dec_ref(v_env_2049_);
lean_inc(v_mod_2025_);
v_entry_2051_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2051_, 0, v_mod_2025_);
lean_ctor_set_uint8(v_entry_2051_, sizeof(void*)*1, v_isExporting_2050_);
lean_ctor_set_uint8(v_entry_2051_, sizeof(void*)*1 + 1, v_isMeta_2026_);
v___x_2052_ = lean_st_ref_get(v___y_2029_);
v_env_2053_ = lean_ctor_get(v___x_2052_, 0);
lean_inc_ref(v_env_2053_);
lean_dec(v___x_2052_);
v___x_2054_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2055_ = lean_box(1);
v___x_2056_ = lean_box(0);
v___x_2057_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2047_, v___x_2054_, v_env_2053_, v___x_2055_, v___x_2056_);
v___x_2058_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg(v___x_2057_, v_entry_2051_);
lean_dec(v___x_2057_);
if (v___x_2058_ == 0)
{
lean_object* v_toCold_2059_; lean_object* v_options_2060_; lean_object* v_inheritedTraceOptions_2061_; uint8_t v_hasTrace_2062_; lean_object* v___f_2063_; uint8_t v___x_2064_; lean_object* v___y_2066_; 
v_toCold_2059_ = lean_ctor_get(v___y_2028_, 0);
v_options_2060_ = lean_ctor_get(v_toCold_2059_, 2);
v_inheritedTraceOptions_2061_ = lean_ctor_get(v_toCold_2059_, 11);
v_hasTrace_2062_ = lean_ctor_get_uint8(v_options_2060_, sizeof(void*)*1);
v___f_2063_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___lam__0), 3, 2);
lean_closure_set(v___f_2063_, 0, v___x_2054_);
lean_closure_set(v___f_2063_, 1, v_entry_2051_);
v___x_2064_ = 1;
if (v_hasTrace_2062_ == 0)
{
lean_dec(v_hint_2027_);
lean_dec(v_mod_2025_);
v___y_2066_ = v___y_2029_;
goto v___jp_2065_;
}
else
{
lean_object* v_cls_2084_; lean_object* v___y_2086_; lean_object* v___y_2087_; lean_object* v___y_2091_; lean_object* v___y_2092_; lean_object* v___x_2104_; uint8_t v___x_2105_; 
v_cls_2084_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__4));
v___x_2104_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__11);
v___x_2105_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2061_, v_options_2060_, v___x_2104_);
if (v___x_2105_ == 0)
{
lean_dec(v_hint_2027_);
lean_dec(v_mod_2025_);
v___y_2066_ = v___y_2029_;
goto v___jp_2065_;
}
else
{
lean_object* v___x_2106_; lean_object* v___y_2108_; 
v___x_2106_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__13);
if (v_isExporting_2050_ == 0)
{
lean_object* v___x_2115_; 
v___x_2115_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__17));
v___y_2108_ = v___x_2115_;
goto v___jp_2107_;
}
else
{
lean_object* v___x_2116_; 
v___x_2116_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__18));
v___y_2108_ = v___x_2116_;
goto v___jp_2107_;
}
v___jp_2107_:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; 
lean_inc_ref(v___y_2108_);
v___x_2109_ = l_Lean_stringToMessageData(v___y_2108_);
v___x_2110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2106_);
lean_ctor_set(v___x_2110_, 1, v___x_2109_);
v___x_2111_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__14);
v___x_2112_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2110_);
lean_ctor_set(v___x_2112_, 1, v___x_2111_);
if (v_isMeta_2026_ == 0)
{
lean_object* v___x_2113_; 
v___x_2113_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__15));
v___y_2091_ = v___x_2112_;
v___y_2092_ = v___x_2113_;
goto v___jp_2090_;
}
else
{
lean_object* v___x_2114_; 
v___x_2114_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__16));
v___y_2091_ = v___x_2112_;
v___y_2092_ = v___x_2114_;
goto v___jp_2090_;
}
}
}
v___jp_2085_:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2088_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2088_, 0, v___y_2086_);
lean_ctor_set(v___x_2088_, 1, v___y_2087_);
v___x_2089_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__9(v_cls_2084_, v___x_2088_, v___y_2028_, v___y_2029_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_dec_ref_known(v___x_2089_, 1);
v___y_2066_ = v___y_2029_;
goto v___jp_2065_;
}
else
{
lean_dec_ref(v___f_2063_);
return v___x_2089_;
}
}
v___jp_2090_:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; uint8_t v___x_2099_; 
lean_inc_ref(v___y_2092_);
v___x_2093_ = l_Lean_stringToMessageData(v___y_2092_);
v___x_2094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2094_, 0, v___y_2091_);
lean_ctor_set(v___x_2094_, 1, v___x_2093_);
v___x_2095_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__6);
v___x_2096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2094_);
lean_ctor_set(v___x_2096_, 1, v___x_2095_);
v___x_2097_ = l_Lean_MessageData_ofName(v_mod_2025_);
v___x_2098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2096_);
lean_ctor_set(v___x_2098_, 1, v___x_2097_);
v___x_2099_ = l_Lean_Name_isAnonymous(v_hint_2027_);
if (v___x_2099_ == 0)
{
lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2100_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__8);
v___x_2101_ = l_Lean_MessageData_ofName(v_hint_2027_);
v___x_2102_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2100_);
lean_ctor_set(v___x_2102_, 1, v___x_2101_);
v___y_2086_ = v___x_2098_;
v___y_2087_ = v___x_2102_;
goto v___jp_2085_;
}
else
{
lean_object* v___x_2103_; 
lean_dec(v_hint_2027_);
v___x_2103_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__9);
v___y_2086_ = v___x_2098_;
v___y_2087_ = v___x_2103_;
goto v___jp_2085_;
}
}
}
v___jp_2065_:
{
lean_object* v___x_2067_; lean_object* v_toEnvExtension_2068_; lean_object* v_env_2069_; lean_object* v_nextMacroScope_2070_; lean_object* v_ngen_2071_; lean_object* v_auxDeclNGen_2072_; lean_object* v_traceState_2073_; lean_object* v_recordedDeps_2074_; lean_object* v_messages_2075_; lean_object* v_infoState_2076_; lean_object* v_snapshotTasks_2077_; lean_object* v_asyncMode_2078_; uint8_t v_logWrites_2079_; lean_object* v___x_2080_; 
v___x_2067_ = lean_st_ref_take(v___y_2066_);
v_toEnvExtension_2068_ = lean_ctor_get(v___x_2054_, 0);
v_env_2069_ = lean_ctor_get(v___x_2067_, 0);
lean_inc_ref(v_env_2069_);
v_nextMacroScope_2070_ = lean_ctor_get(v___x_2067_, 1);
lean_inc(v_nextMacroScope_2070_);
v_ngen_2071_ = lean_ctor_get(v___x_2067_, 2);
lean_inc_ref(v_ngen_2071_);
v_auxDeclNGen_2072_ = lean_ctor_get(v___x_2067_, 3);
lean_inc_ref(v_auxDeclNGen_2072_);
v_traceState_2073_ = lean_ctor_get(v___x_2067_, 4);
lean_inc_ref(v_traceState_2073_);
v_recordedDeps_2074_ = lean_ctor_get(v___x_2067_, 6);
lean_inc_ref(v_recordedDeps_2074_);
v_messages_2075_ = lean_ctor_get(v___x_2067_, 7);
lean_inc_ref(v_messages_2075_);
v_infoState_2076_ = lean_ctor_get(v___x_2067_, 8);
lean_inc_ref(v_infoState_2076_);
v_snapshotTasks_2077_ = lean_ctor_get(v___x_2067_, 9);
lean_inc_ref(v_snapshotTasks_2077_);
lean_dec(v___x_2067_);
v_asyncMode_2078_ = lean_ctor_get(v_toEnvExtension_2068_, 2);
v_logWrites_2079_ = lean_ctor_get_uint8(v_toEnvExtension_2068_, sizeof(void*)*6);
v___x_2080_ = lean_box(0);
if (v_logWrites_2079_ == 0)
{
lean_object* v___x_2081_; 
lean_inc_ref(v_toEnvExtension_2068_);
v___x_2081_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2068_, v_env_2069_, v___f_2063_, v_asyncMode_2078_, v___x_2056_, v___x_2064_);
v___y_2032_ = v_snapshotTasks_2077_;
v___y_2033_ = v_infoState_2076_;
v___y_2034_ = v___x_2080_;
v___y_2035_ = v___y_2066_;
v___y_2036_ = v_ngen_2071_;
v___y_2037_ = v_nextMacroScope_2070_;
v___y_2038_ = v_traceState_2073_;
v___y_2039_ = v_messages_2075_;
v___y_2040_ = v_recordedDeps_2074_;
v___y_2041_ = v_auxDeclNGen_2072_;
v___y_2042_ = v___x_2081_;
goto v___jp_2031_;
}
else
{
lean_object* v___x_2082_; lean_object* v___x_2083_; 
lean_inc_ref_n(v_toEnvExtension_2068_, 2);
v___x_2082_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2068_, v_env_2069_);
lean_dec_ref(v_env_2069_);
v___x_2083_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2068_, v___x_2082_, v___f_2063_, v_asyncMode_2078_, v___x_2056_, v___x_2064_);
v___y_2032_ = v_snapshotTasks_2077_;
v___y_2033_ = v_infoState_2076_;
v___y_2034_ = v___x_2080_;
v___y_2035_ = v___y_2066_;
v___y_2036_ = v_ngen_2071_;
v___y_2037_ = v_nextMacroScope_2070_;
v___y_2038_ = v_traceState_2073_;
v___y_2039_ = v_messages_2075_;
v___y_2040_ = v_recordedDeps_2074_;
v___y_2041_ = v_auxDeclNGen_2072_;
v___y_2042_ = v___x_2083_;
goto v___jp_2031_;
}
}
}
else
{
lean_object* v___x_2117_; lean_object* v___x_2118_; 
lean_dec_ref_known(v_entry_2051_, 1);
lean_dec(v_hint_2027_);
lean_dec(v_mod_2025_);
v___x_2117_ = lean_box(0);
v___x_2118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
return v___x_2118_;
}
v___jp_2031_:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2043_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__1);
v___x_2044_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2044_, 0, v___y_2042_);
lean_ctor_set(v___x_2044_, 1, v___y_2037_);
lean_ctor_set(v___x_2044_, 2, v___y_2036_);
lean_ctor_set(v___x_2044_, 3, v___y_2041_);
lean_ctor_set(v___x_2044_, 4, v___y_2038_);
lean_ctor_set(v___x_2044_, 5, v___x_2043_);
lean_ctor_set(v___x_2044_, 6, v___y_2040_);
lean_ctor_set(v___x_2044_, 7, v___y_2039_);
lean_ctor_set(v___x_2044_, 8, v___y_2033_);
lean_ctor_set(v___x_2044_, 9, v___y_2032_);
v___x_2045_ = lean_st_ref_put(v___y_2035_, v___x_2044_);
v___x_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2046_, 0, v___y_2034_);
return v___x_2046_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___boxed(lean_object* v_mod_2119_, lean_object* v_isMeta_2120_, lean_object* v_hint_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
uint8_t v_isMeta_boxed_2125_; lean_object* v_res_2126_; 
v_isMeta_boxed_2125_ = lean_unbox(v_isMeta_2120_);
v_res_2126_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4(v_mod_2119_, v_isMeta_boxed_2125_, v_hint_2121_, v___y_2122_, v___y_2123_);
lean_dec(v___y_2123_);
lean_dec_ref(v___y_2122_);
return v_res_2126_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg(lean_object* v_a_2127_, lean_object* v_x_2128_){
_start:
{
if (lean_obj_tag(v_x_2128_) == 0)
{
lean_object* v___x_2129_; 
v___x_2129_ = lean_box(0);
return v___x_2129_;
}
else
{
lean_object* v_key_2130_; lean_object* v_value_2131_; lean_object* v_tail_2132_; uint8_t v___x_2133_; 
v_key_2130_ = lean_ctor_get(v_x_2128_, 0);
v_value_2131_ = lean_ctor_get(v_x_2128_, 1);
v_tail_2132_ = lean_ctor_get(v_x_2128_, 2);
v___x_2133_ = lean_name_eq(v_key_2130_, v_a_2127_);
if (v___x_2133_ == 0)
{
v_x_2128_ = v_tail_2132_;
goto _start;
}
else
{
lean_object* v___x_2135_; 
lean_inc(v_value_2131_);
v___x_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2135_, 0, v_value_2131_);
return v___x_2135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg___boxed(lean_object* v_a_2136_, lean_object* v_x_2137_){
_start:
{
lean_object* v_res_2138_; 
v_res_2138_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg(v_a_2136_, v_x_2137_);
lean_dec(v_x_2137_);
lean_dec(v_a_2136_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6___redArg(lean_object* v_m_2139_, lean_object* v_a_2140_){
_start:
{
lean_object* v_buckets_2141_; lean_object* v___x_2142_; uint64_t v___y_2144_; 
v_buckets_2141_ = lean_ctor_get(v_m_2139_, 1);
v___x_2142_ = lean_array_get_size(v_buckets_2141_);
if (lean_obj_tag(v_a_2140_) == 0)
{
uint64_t v___x_2158_; 
v___x_2158_ = 1723ULL;
v___y_2144_ = v___x_2158_;
goto v___jp_2143_;
}
else
{
uint64_t v_hash_2159_; 
v_hash_2159_ = lean_ctor_get_uint64(v_a_2140_, sizeof(void*)*2);
v___y_2144_ = v_hash_2159_;
goto v___jp_2143_;
}
v___jp_2143_:
{
uint64_t v___x_2145_; uint64_t v___x_2146_; uint64_t v_fold_2147_; uint64_t v___x_2148_; uint64_t v___x_2149_; uint64_t v___x_2150_; size_t v___x_2151_; size_t v___x_2152_; size_t v___x_2153_; size_t v___x_2154_; size_t v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2145_ = 32ULL;
v___x_2146_ = lean_uint64_shift_right(v___y_2144_, v___x_2145_);
v_fold_2147_ = lean_uint64_xor(v___y_2144_, v___x_2146_);
v___x_2148_ = 16ULL;
v___x_2149_ = lean_uint64_shift_right(v_fold_2147_, v___x_2148_);
v___x_2150_ = lean_uint64_xor(v_fold_2147_, v___x_2149_);
v___x_2151_ = lean_uint64_to_usize(v___x_2150_);
v___x_2152_ = lean_usize_of_nat(v___x_2142_);
v___x_2153_ = ((size_t)1ULL);
v___x_2154_ = lean_usize_sub(v___x_2152_, v___x_2153_);
v___x_2155_ = lean_usize_land(v___x_2151_, v___x_2154_);
v___x_2156_ = lean_array_uget_borrowed(v_buckets_2141_, v___x_2155_);
v___x_2157_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg(v_a_2140_, v___x_2156_);
return v___x_2157_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6___redArg___boxed(lean_object* v_m_2160_, lean_object* v_a_2161_){
_start:
{
lean_object* v_res_2162_; 
v_res_2162_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6___redArg(v_m_2160_, v_a_2161_);
lean_dec(v_a_2161_);
lean_dec_ref(v_m_2160_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__5(lean_object* v___x_2163_, lean_object* v_declName_2164_, lean_object* v_as_2165_, size_t v_sz_2166_, size_t v_i_2167_, lean_object* v_b_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_){
_start:
{
uint8_t v___x_2172_; 
v___x_2172_ = lean_usize_dec_lt(v_i_2167_, v_sz_2166_);
if (v___x_2172_ == 0)
{
lean_object* v___x_2173_; 
lean_dec(v_declName_2164_);
v___x_2173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2173_, 0, v_b_2168_);
return v___x_2173_;
}
else
{
lean_object* v___x_2174_; lean_object* v_modules_2175_; lean_object* v___x_2176_; lean_object* v_a_2177_; lean_object* v___x_2178_; lean_object* v_toImport_2179_; lean_object* v_module_2180_; lean_object* v___x_2181_; uint8_t v___x_2182_; lean_object* v___x_2183_; 
v___x_2174_ = l_Lean_Environment_header(v___x_2163_);
v_modules_2175_ = lean_ctor_get(v___x_2174_, 3);
lean_inc_ref(v_modules_2175_);
lean_dec_ref(v___x_2174_);
v___x_2176_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2177_ = lean_array_uget_borrowed(v_as_2165_, v_i_2167_);
v___x_2178_ = lean_array_get(v___x_2176_, v_modules_2175_, v_a_2177_);
lean_dec_ref(v_modules_2175_);
v_toImport_2179_ = lean_ctor_get(v___x_2178_, 0);
lean_inc_ref(v_toImport_2179_);
lean_dec(v___x_2178_);
v_module_2180_ = lean_ctor_get(v_toImport_2179_, 0);
lean_inc(v_module_2180_);
lean_dec_ref(v_toImport_2179_);
v___x_2181_ = lean_box(0);
v___x_2182_ = 0;
lean_inc(v_declName_2164_);
v___x_2183_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4(v_module_2180_, v___x_2182_, v_declName_2164_, v___y_2169_, v___y_2170_);
if (lean_obj_tag(v___x_2183_) == 0)
{
size_t v___x_2184_; size_t v___x_2185_; 
lean_dec_ref_known(v___x_2183_, 1);
v___x_2184_ = ((size_t)1ULL);
v___x_2185_ = lean_usize_add(v_i_2167_, v___x_2184_);
v_i_2167_ = v___x_2185_;
v_b_2168_ = v___x_2181_;
goto _start;
}
else
{
lean_dec(v_declName_2164_);
return v___x_2183_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__5___boxed(lean_object* v___x_2187_, lean_object* v_declName_2188_, lean_object* v_as_2189_, lean_object* v_sz_2190_, lean_object* v_i_2191_, lean_object* v_b_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_){
_start:
{
size_t v_sz_boxed_2196_; size_t v_i_boxed_2197_; lean_object* v_res_2198_; 
v_sz_boxed_2196_ = lean_unbox_usize(v_sz_2190_);
lean_dec(v_sz_2190_);
v_i_boxed_2197_ = lean_unbox_usize(v_i_2191_);
lean_dec(v_i_2191_);
v_res_2198_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__5(v___x_2187_, v_declName_2188_, v_as_2189_, v_sz_boxed_2196_, v_i_boxed_2197_, v_b_2192_, v___y_2193_, v___y_2194_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
lean_dec_ref(v_as_2189_);
lean_dec_ref(v___x_2187_);
return v_res_2198_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2___closed__0(void){
_start:
{
lean_object* v___x_2199_; 
v___x_2199_ = l_Std_HashMap_instInhabited___redArg();
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2(lean_object* v_declName_2202_, uint8_t v_isMeta_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v_env_2212_; lean_object* v___y_2214_; lean_object* v___x_2227_; 
v___x_2207_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2___closed__0);
v___x_2208_ = lean_st_ref_get(v___y_2205_);
v_env_2212_ = lean_ctor_get(v___x_2208_, 0);
lean_inc_ref(v_env_2212_);
lean_dec(v___x_2208_);
v___x_2227_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2212_, v_declName_2202_);
if (lean_obj_tag(v___x_2227_) == 0)
{
lean_dec_ref(v_env_2212_);
lean_dec(v_declName_2202_);
goto v___jp_2209_;
}
else
{
lean_object* v_val_2228_; lean_object* v___x_2229_; lean_object* v_modules_2230_; lean_object* v___x_2231_; uint8_t v___x_2232_; 
v_val_2228_ = lean_ctor_get(v___x_2227_, 0);
lean_inc(v_val_2228_);
lean_dec_ref_known(v___x_2227_, 1);
v___x_2229_ = l_Lean_Environment_header(v_env_2212_);
v_modules_2230_ = lean_ctor_get(v___x_2229_, 3);
lean_inc_ref(v_modules_2230_);
lean_dec_ref(v___x_2229_);
v___x_2231_ = lean_array_get_size(v_modules_2230_);
v___x_2232_ = lean_nat_dec_lt(v_val_2228_, v___x_2231_);
if (v___x_2232_ == 0)
{
lean_dec_ref(v_modules_2230_);
lean_dec(v_val_2228_);
lean_dec_ref(v_env_2212_);
lean_dec(v_declName_2202_);
goto v___jp_2209_;
}
else
{
lean_object* v___x_2233_; lean_object* v___x_2234_; uint8_t v___y_2236_; 
v___x_2233_ = lean_array_fget(v_modules_2230_, v_val_2228_);
lean_dec(v_val_2228_);
lean_dec_ref(v_modules_2230_);
v___x_2234_ = lean_st_ref_get(v___y_2205_);
if (v_isMeta_2203_ == 0)
{
lean_dec(v___x_2234_);
v___y_2236_ = v_isMeta_2203_;
goto v___jp_2235_;
}
else
{
lean_object* v_env_2247_; uint8_t v___x_2248_; 
v_env_2247_ = lean_ctor_get(v___x_2234_, 0);
lean_inc_ref(v_env_2247_);
lean_dec(v___x_2234_);
lean_inc(v_declName_2202_);
v___x_2248_ = l_Lean_isMarkedMeta(v_env_2247_, v_declName_2202_);
if (v___x_2248_ == 0)
{
v___y_2236_ = v_isMeta_2203_;
goto v___jp_2235_;
}
else
{
uint8_t v___x_2249_; 
v___x_2249_ = 0;
v___y_2236_ = v___x_2249_;
goto v___jp_2235_;
}
}
v___jp_2235_:
{
lean_object* v_toImport_2237_; lean_object* v_module_2238_; lean_object* v___x_2239_; 
v_toImport_2237_ = lean_ctor_get(v___x_2233_, 0);
lean_inc_ref(v_toImport_2237_);
lean_dec(v___x_2233_);
v_module_2238_ = lean_ctor_get(v_toImport_2237_, 0);
lean_inc(v_module_2238_);
lean_dec_ref(v_toImport_2237_);
lean_inc(v_declName_2202_);
v___x_2239_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4(v_module_2238_, v___y_2236_, v_declName_2202_, v___y_2204_, v___y_2205_);
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
lean_dec_ref_known(v___x_2239_, 1);
v___x_2240_ = l_Lean_indirectModUseExt;
v___x_2241_ = lean_box(1);
v___x_2242_ = lean_box(0);
lean_inc_ref(v_env_2212_);
v___x_2243_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2207_, v___x_2240_, v_env_2212_, v___x_2241_, v___x_2242_);
v___x_2244_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6___redArg(v___x_2243_, v_declName_2202_);
lean_dec(v___x_2243_);
if (lean_obj_tag(v___x_2244_) == 0)
{
lean_object* v___x_2245_; 
v___x_2245_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2___closed__1));
v___y_2214_ = v___x_2245_;
goto v___jp_2213_;
}
else
{
lean_object* v_val_2246_; 
v_val_2246_ = lean_ctor_get(v___x_2244_, 0);
lean_inc(v_val_2246_);
lean_dec_ref_known(v___x_2244_, 1);
v___y_2214_ = v_val_2246_;
goto v___jp_2213_;
}
}
else
{
lean_dec_ref(v_env_2212_);
lean_dec(v_declName_2202_);
return v___x_2239_;
}
}
}
}
v___jp_2209_:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2210_ = lean_box(0);
v___x_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2210_);
return v___x_2211_;
}
v___jp_2213_:
{
lean_object* v___x_2215_; size_t v_sz_2216_; size_t v___x_2217_; lean_object* v___x_2218_; 
v___x_2215_ = lean_box(0);
v_sz_2216_ = lean_array_size(v___y_2214_);
v___x_2217_ = ((size_t)0ULL);
v___x_2218_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__5(v_env_2212_, v_declName_2202_, v___y_2214_, v_sz_2216_, v___x_2217_, v___x_2215_, v___y_2204_, v___y_2205_);
lean_dec_ref(v___y_2214_);
lean_dec_ref(v_env_2212_);
if (lean_obj_tag(v___x_2218_) == 0)
{
lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2218_);
if (v_isSharedCheck_2225_ == 0)
{
lean_object* v_unused_2226_; 
v_unused_2226_ = lean_ctor_get(v___x_2218_, 0);
lean_dec(v_unused_2226_);
v___x_2220_ = v___x_2218_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_dec(v___x_2218_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2223_; 
if (v_isShared_2221_ == 0)
{
lean_ctor_set(v___x_2220_, 0, v___x_2215_);
v___x_2223_ = v___x_2220_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v___x_2215_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
else
{
return v___x_2218_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2___boxed(lean_object* v_declName_2250_, lean_object* v_isMeta_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_){
_start:
{
uint8_t v_isMeta_boxed_2255_; lean_object* v_res_2256_; 
v_isMeta_boxed_2255_ = lean_unbox(v_isMeta_2251_);
v_res_2256_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2(v_declName_2250_, v_isMeta_boxed_2255_, v___y_2252_, v___y_2253_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5(lean_object* v_ref_2257_, lean_object* v_msgData_2258_, uint8_t v_severity_2259_, uint8_t v_isSilent_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_){
_start:
{
uint8_t v___y_2265_; lean_object* v___y_2266_; uint8_t v___y_2267_; lean_object* v___y_2268_; lean_object* v___y_2269_; lean_object* v___y_2270_; lean_object* v___y_2271_; lean_object* v_toCold_2272_; lean_object* v___y_2273_; lean_object* v___y_2302_; lean_object* v___y_2303_; uint8_t v___y_2304_; lean_object* v___y_2305_; uint8_t v___y_2306_; uint8_t v___y_2307_; lean_object* v___y_2308_; lean_object* v___y_2309_; lean_object* v___y_2329_; uint8_t v___y_2330_; lean_object* v___y_2331_; uint8_t v___y_2332_; uint8_t v___y_2333_; lean_object* v___y_2334_; lean_object* v___y_2335_; uint8_t v___y_2339_; uint8_t v___y_2340_; uint8_t v___y_2341_; uint8_t v___x_2352_; uint8_t v___y_2354_; uint8_t v___y_2355_; uint8_t v___y_2356_; uint8_t v___y_2358_; uint8_t v___x_2366_; 
v___x_2352_ = 2;
v___x_2366_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2259_, v___x_2352_);
if (v___x_2366_ == 0)
{
v___y_2358_ = v___x_2366_;
goto v___jp_2357_;
}
else
{
uint8_t v___x_2367_; 
lean_inc_ref(v_msgData_2258_);
v___x_2367_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2258_);
v___y_2358_ = v___x_2367_;
goto v___jp_2357_;
}
v___jp_2264_:
{
lean_object* v_currNamespace_2274_; lean_object* v_openDecls_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v_env_2280_; lean_object* v_nextMacroScope_2281_; lean_object* v_ngen_2282_; lean_object* v_auxDeclNGen_2283_; lean_object* v_traceState_2284_; lean_object* v_cache_2285_; lean_object* v_recordedDeps_2286_; lean_object* v_messages_2287_; lean_object* v_infoState_2288_; lean_object* v_snapshotTasks_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2300_; 
v_currNamespace_2274_ = lean_ctor_get(v_toCold_2272_, 4);
v_openDecls_2275_ = lean_ctor_get(v_toCold_2272_, 5);
lean_inc(v_openDecls_2275_);
lean_inc(v_currNamespace_2274_);
v___x_2276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2276_, 0, v_currNamespace_2274_);
lean_ctor_set(v___x_2276_, 1, v_openDecls_2275_);
v___x_2277_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2276_);
lean_ctor_set(v___x_2277_, 1, v___y_2270_);
lean_inc_ref(v___y_2268_);
lean_inc_ref(v___y_2271_);
v___x_2278_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2278_, 0, v___y_2271_);
lean_ctor_set(v___x_2278_, 1, v___y_2266_);
lean_ctor_set(v___x_2278_, 2, v___y_2269_);
lean_ctor_set(v___x_2278_, 3, v___y_2268_);
lean_ctor_set(v___x_2278_, 4, v___x_2277_);
lean_ctor_set_uint8(v___x_2278_, sizeof(void*)*5, v___y_2267_);
lean_ctor_set_uint8(v___x_2278_, sizeof(void*)*5 + 1, v___y_2265_);
lean_ctor_set_uint8(v___x_2278_, sizeof(void*)*5 + 2, v_isSilent_2260_);
v___x_2279_ = lean_st_ref_take(v___y_2273_);
v_env_2280_ = lean_ctor_get(v___x_2279_, 0);
v_nextMacroScope_2281_ = lean_ctor_get(v___x_2279_, 1);
v_ngen_2282_ = lean_ctor_get(v___x_2279_, 2);
v_auxDeclNGen_2283_ = lean_ctor_get(v___x_2279_, 3);
v_traceState_2284_ = lean_ctor_get(v___x_2279_, 4);
v_cache_2285_ = lean_ctor_get(v___x_2279_, 5);
v_recordedDeps_2286_ = lean_ctor_get(v___x_2279_, 6);
v_messages_2287_ = lean_ctor_get(v___x_2279_, 7);
v_infoState_2288_ = lean_ctor_get(v___x_2279_, 8);
v_snapshotTasks_2289_ = lean_ctor_get(v___x_2279_, 9);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2291_ = v___x_2279_;
v_isShared_2292_ = v_isSharedCheck_2300_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_snapshotTasks_2289_);
lean_inc(v_infoState_2288_);
lean_inc(v_messages_2287_);
lean_inc(v_recordedDeps_2286_);
lean_inc(v_cache_2285_);
lean_inc(v_traceState_2284_);
lean_inc(v_auxDeclNGen_2283_);
lean_inc(v_ngen_2282_);
lean_inc(v_nextMacroScope_2281_);
lean_inc(v_env_2280_);
lean_dec(v___x_2279_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2300_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2296_; 
v___x_2293_ = lean_box(0);
v___x_2294_ = l_Lean_MessageLog_add(v___x_2278_, v_messages_2287_);
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 7, v___x_2294_);
v___x_2296_ = v___x_2291_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_env_2280_);
lean_ctor_set(v_reuseFailAlloc_2299_, 1, v_nextMacroScope_2281_);
lean_ctor_set(v_reuseFailAlloc_2299_, 2, v_ngen_2282_);
lean_ctor_set(v_reuseFailAlloc_2299_, 3, v_auxDeclNGen_2283_);
lean_ctor_set(v_reuseFailAlloc_2299_, 4, v_traceState_2284_);
lean_ctor_set(v_reuseFailAlloc_2299_, 5, v_cache_2285_);
lean_ctor_set(v_reuseFailAlloc_2299_, 6, v_recordedDeps_2286_);
lean_ctor_set(v_reuseFailAlloc_2299_, 7, v___x_2294_);
lean_ctor_set(v_reuseFailAlloc_2299_, 8, v_infoState_2288_);
lean_ctor_set(v_reuseFailAlloc_2299_, 9, v_snapshotTasks_2289_);
v___x_2296_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___x_2297_ = lean_st_ref_put(v___y_2273_, v___x_2296_);
v___x_2298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2293_);
return v___x_2298_;
}
}
}
v___jp_2301_:
{
lean_object* v_fileName_2310_; lean_object* v_fileMap_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2327_; 
v_fileName_2310_ = lean_ctor_get(v___y_2305_, 0);
v_fileMap_2311_ = lean_ctor_get(v___y_2305_, 1);
v___x_2312_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2258_);
v___x_2313_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0(v___x_2312_, v___y_2261_, v___y_2262_);
v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2316_ = v___x_2313_;
v_isShared_2317_ = v_isSharedCheck_2327_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2313_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2327_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
lean_inc_ref_n(v_fileMap_2311_, 2);
v___x_2318_ = l_Lean_FileMap_toPosition(v_fileMap_2311_, v___y_2308_);
lean_dec(v___y_2308_);
v___x_2319_ = l_Lean_FileMap_toPosition(v_fileMap_2311_, v___y_2309_);
lean_dec(v___y_2309_);
v___x_2320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2319_);
v___x_2321_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48___closed__0));
if (v___y_2307_ == 0)
{
lean_del_object(v___x_2316_);
lean_dec_ref(v___y_2303_);
v___y_2265_ = v___y_2304_;
v___y_2266_ = v___x_2318_;
v___y_2267_ = v___y_2306_;
v___y_2268_ = v___x_2321_;
v___y_2269_ = v___x_2320_;
v___y_2270_ = v_a_2314_;
v___y_2271_ = v_fileName_2310_;
v_toCold_2272_ = v___y_2302_;
v___y_2273_ = v___y_2262_;
goto v___jp_2264_;
}
else
{
uint8_t v___x_2322_; 
lean_inc(v_a_2314_);
v___x_2322_ = l_Lean_MessageData_hasTag(v___y_2303_, v_a_2314_);
if (v___x_2322_ == 0)
{
lean_object* v___x_2323_; lean_object* v___x_2325_; 
lean_dec_ref_known(v___x_2320_, 1);
lean_dec_ref(v___x_2318_);
lean_dec(v_a_2314_);
v___x_2323_ = lean_box(0);
if (v_isShared_2317_ == 0)
{
lean_ctor_set(v___x_2316_, 0, v___x_2323_);
v___x_2325_ = v___x_2316_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v___x_2323_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
}
}
else
{
lean_del_object(v___x_2316_);
v___y_2265_ = v___y_2304_;
v___y_2266_ = v___x_2318_;
v___y_2267_ = v___y_2306_;
v___y_2268_ = v___x_2321_;
v___y_2269_ = v___x_2320_;
v___y_2270_ = v_a_2314_;
v___y_2271_ = v_fileName_2310_;
v_toCold_2272_ = v___y_2302_;
v___y_2273_ = v___y_2262_;
goto v___jp_2264_;
}
}
}
}
v___jp_2328_:
{
lean_object* v___x_2336_; 
v___x_2336_ = l_Lean_Syntax_getTailPos_x3f(v___y_2334_, v___y_2333_);
lean_dec(v___y_2334_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_inc(v___y_2335_);
v___y_2302_ = v___y_2329_;
v___y_2303_ = v___y_2331_;
v___y_2304_ = v___y_2332_;
v___y_2305_ = v___y_2329_;
v___y_2306_ = v___y_2333_;
v___y_2307_ = v___y_2330_;
v___y_2308_ = v___y_2335_;
v___y_2309_ = v___y_2335_;
goto v___jp_2301_;
}
else
{
lean_object* v_val_2337_; 
v_val_2337_ = lean_ctor_get(v___x_2336_, 0);
lean_inc(v_val_2337_);
lean_dec_ref_known(v___x_2336_, 1);
v___y_2302_ = v___y_2329_;
v___y_2303_ = v___y_2331_;
v___y_2304_ = v___y_2332_;
v___y_2305_ = v___y_2329_;
v___y_2306_ = v___y_2333_;
v___y_2307_ = v___y_2330_;
v___y_2308_ = v___y_2335_;
v___y_2309_ = v_val_2337_;
goto v___jp_2301_;
}
}
v___jp_2338_:
{
lean_object* v_toCold_2342_; lean_object* v_ref_2343_; uint8_t v_suppressElabErrors_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___f_2347_; lean_object* v_ref_2348_; lean_object* v___x_2349_; 
v_toCold_2342_ = lean_ctor_get(v___y_2261_, 0);
v_ref_2343_ = lean_ctor_get(v___y_2261_, 2);
v_suppressElabErrors_2344_ = lean_ctor_get_uint8(v___y_2261_, sizeof(void*)*3 + 2);
v___x_2345_ = lean_box(v_suppressElabErrors_2344_);
v___x_2346_ = lean_box(v___y_2339_);
v___f_2347_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2347_, 0, v___x_2345_);
lean_closure_set(v___f_2347_, 1, v___x_2346_);
v_ref_2348_ = l_Lean_replaceRef(v_ref_2257_, v_ref_2343_);
v___x_2349_ = l_Lean_Syntax_getPos_x3f(v_ref_2348_, v___y_2340_);
if (lean_obj_tag(v___x_2349_) == 0)
{
lean_object* v___x_2350_; 
v___x_2350_ = lean_unsigned_to_nat(0u);
v___y_2329_ = v_toCold_2342_;
v___y_2330_ = v_suppressElabErrors_2344_;
v___y_2331_ = v___f_2347_;
v___y_2332_ = v___y_2341_;
v___y_2333_ = v___y_2340_;
v___y_2334_ = v_ref_2348_;
v___y_2335_ = v___x_2350_;
goto v___jp_2328_;
}
else
{
lean_object* v_val_2351_; 
v_val_2351_ = lean_ctor_get(v___x_2349_, 0);
lean_inc(v_val_2351_);
lean_dec_ref_known(v___x_2349_, 1);
v___y_2329_ = v_toCold_2342_;
v___y_2330_ = v_suppressElabErrors_2344_;
v___y_2331_ = v___f_2347_;
v___y_2332_ = v___y_2341_;
v___y_2333_ = v___y_2340_;
v___y_2334_ = v_ref_2348_;
v___y_2335_ = v_val_2351_;
goto v___jp_2328_;
}
}
v___jp_2353_:
{
if (v___y_2356_ == 0)
{
v___y_2339_ = v___y_2354_;
v___y_2340_ = v___y_2355_;
v___y_2341_ = v_severity_2259_;
goto v___jp_2338_;
}
else
{
v___y_2339_ = v___y_2354_;
v___y_2340_ = v___y_2355_;
v___y_2341_ = v___x_2352_;
goto v___jp_2338_;
}
}
v___jp_2357_:
{
if (v___y_2358_ == 0)
{
uint8_t v___x_2359_; uint8_t v___x_2360_; 
v___x_2359_ = 1;
v___x_2360_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2259_, v___x_2359_);
if (v___x_2360_ == 0)
{
v___y_2354_ = v___y_2358_;
v___y_2355_ = v___y_2358_;
v___y_2356_ = v___x_2360_;
goto v___jp_2353_;
}
else
{
lean_object* v___x_2361_; lean_object* v___x_2362_; uint8_t v___x_2363_; 
v___x_2361_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2261_);
v___x_2362_ = l_Lean_warningAsError;
v___x_2363_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4(v___x_2361_, v___x_2362_);
lean_dec_ref(v___x_2361_);
v___y_2354_ = v___y_2358_;
v___y_2355_ = v___y_2358_;
v___y_2356_ = v___x_2363_;
goto v___jp_2353_;
}
}
else
{
lean_object* v___x_2364_; lean_object* v___x_2365_; 
lean_dec_ref(v_msgData_2258_);
v___x_2364_ = lean_box(0);
v___x_2365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2364_);
return v___x_2365_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___boxed(lean_object* v_ref_2368_, lean_object* v_msgData_2369_, lean_object* v_severity_2370_, lean_object* v_isSilent_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_){
_start:
{
uint8_t v_severity_boxed_2375_; uint8_t v_isSilent_boxed_2376_; lean_object* v_res_2377_; 
v_severity_boxed_2375_ = lean_unbox(v_severity_2370_);
v_isSilent_boxed_2376_ = lean_unbox(v_isSilent_2371_);
v_res_2377_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5(v_ref_2368_, v_msgData_2369_, v_severity_boxed_2375_, v_isSilent_boxed_2376_, v___y_2372_, v___y_2373_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
lean_dec(v_ref_2368_);
return v_res_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_msgData_2378_, uint8_t v_severity_2379_, uint8_t v_isSilent_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_){
_start:
{
lean_object* v_ref_2384_; lean_object* v___x_2385_; 
v_ref_2384_ = lean_ctor_get(v___y_2381_, 2);
v___x_2385_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5(v_ref_2384_, v_msgData_2378_, v_severity_2379_, v_isSilent_2380_, v___y_2381_, v___y_2382_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_msgData_2386_, lean_object* v_severity_2387_, lean_object* v_isSilent_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_){
_start:
{
uint8_t v_severity_boxed_2392_; uint8_t v_isSilent_boxed_2393_; lean_object* v_res_2394_; 
v_severity_boxed_2392_ = lean_unbox(v_severity_2387_);
v_isSilent_boxed_2393_ = lean_unbox(v_isSilent_2388_);
v_res_2394_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2(v_msgData_2386_, v_severity_boxed_2392_, v_isSilent_boxed_2393_, v___y_2389_, v___y_2390_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
return v_res_2394_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1(lean_object* v_msgData_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_){
_start:
{
uint8_t v___x_2399_; uint8_t v___x_2400_; lean_object* v___x_2401_; 
v___x_2399_ = 1;
v___x_2400_ = 0;
v___x_2401_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2(v_msgData_2395_, v___x_2399_, v___x_2400_, v___y_2396_, v___y_2397_);
return v___x_2401_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1___boxed(lean_object* v_msgData_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_){
_start:
{
lean_object* v_res_2406_; 
v_res_2406_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1(v_msgData_2402_, v___y_2403_, v___y_2404_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_){
_start:
{
lean_object* v_ref_2411_; lean_object* v___x_2412_; lean_object* v_a_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2421_; 
v_ref_2411_ = lean_ctor_get(v___y_2408_, 2);
v___x_2412_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0(v_msg_2407_, v___y_2408_, v___y_2409_);
v_a_2413_ = lean_ctor_get(v___x_2412_, 0);
v_isSharedCheck_2421_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2415_ = v___x_2412_;
v_isShared_2416_ = v_isSharedCheck_2421_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_a_2413_);
lean_dec(v___x_2412_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2421_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v___x_2417_; lean_object* v___x_2419_; 
lean_inc(v_ref_2411_);
v___x_2417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2417_, 0, v_ref_2411_);
lean_ctor_set(v___x_2417_, 1, v_a_2413_);
if (v_isShared_2416_ == 0)
{
lean_ctor_set_tag(v___x_2415_, 1);
lean_ctor_set(v___x_2415_, 0, v___x_2417_);
v___x_2419_ = v___x_2415_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v___x_2417_);
v___x_2419_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
return v___x_2419_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0___redArg(v_msg_2422_, v___y_2423_, v___y_2424_);
lean_dec(v___y_2424_);
lean_dec_ref(v___y_2423_);
return v_res_2426_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__1_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2428_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__0_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2429_ = l_Lean_stringToMessageData(v___x_2428_);
return v___x_2429_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__4_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2433_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__3_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2434_ = l_Lean_MessageData_ofFormat(v___x_2433_);
return v___x_2434_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2436_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__5_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2437_ = l_Lean_stringToMessageData(v___x_2436_);
return v___x_2437_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2439_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2440_ = l_Lean_stringToMessageData(v___x_2439_);
return v___x_2440_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__10_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___x_2442_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2443_ = l_Lean_stringToMessageData(v___x_2442_);
return v___x_2443_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__13_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___x_2447_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__12_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2448_ = l_Lean_MessageData_ofFormat(v___x_2447_);
return v___x_2448_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__14_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2449_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__13_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__13_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__13_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2450_ = l_Lean_MessageData_hint_x27(v___x_2449_);
return v___x_2450_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2452_; lean_object* v___x_2453_; 
v___x_2452_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__15_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2453_ = l_Lean_stringToMessageData(v___x_2452_);
return v___x_2453_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__19_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2457_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__18_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2458_ = l_Lean_MessageData_ofFormat(v___x_2457_);
return v___x_2458_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__24_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; 
v___x_2465_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__23_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2466_ = l_Lean_MessageData_ofFormat(v___x_2465_);
return v___x_2466_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__25_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2467_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__24_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__24_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__24_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2468_, 0, v___x_2467_);
return v___x_2468_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__28_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2472_; lean_object* v___x_2473_; 
v___x_2472_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__27_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2473_ = l_Lean_MessageData_ofFormat(v___x_2472_);
return v___x_2473_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2474_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_2475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2475_, 0, v___x_2474_);
return v___x_2475_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2476_ = lean_box(1);
v___x_2477_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_2478_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2479_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2478_);
lean_ctor_set(v___x_2479_, 1, v___x_2477_);
lean_ctor_set(v___x_2479_, 2, v___x_2476_);
return v___x_2479_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; 
v___x_2482_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_2483_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2484_ = lean_unsigned_to_nat(0u);
v___x_2485_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2485_, 0, v___x_2484_);
lean_ctor_set(v___x_2485_, 1, v___x_2484_);
lean_ctor_set(v___x_2485_, 2, v___x_2484_);
lean_ctor_set(v___x_2485_, 3, v___x_2484_);
lean_ctor_set(v___x_2485_, 4, v___x_2483_);
lean_ctor_set(v___x_2485_, 5, v___x_2483_);
lean_ctor_set(v___x_2485_, 6, v___x_2483_);
lean_ctor_set(v___x_2485_, 7, v___x_2483_);
lean_ctor_set(v___x_2485_, 8, v___x_2483_);
lean_ctor_set(v___x_2485_, 9, v___x_2483_);
lean_ctor_set(v___x_2485_, 10, v___x_2483_);
lean_ctor_set(v___x_2485_, 11, v___x_2482_);
return v___x_2485_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2486_; lean_object* v___x_2487_; 
v___x_2486_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2487_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2487_, 0, v___x_2486_);
lean_ctor_set(v___x_2487_, 1, v___x_2486_);
lean_ctor_set(v___x_2487_, 2, v___x_2486_);
lean_ctor_set(v___x_2487_, 3, v___x_2486_);
lean_ctor_set(v___x_2487_, 4, v___x_2486_);
lean_ctor_set(v___x_2487_, 5, v___x_2486_);
return v___x_2487_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2488_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2489_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2489_, 0, v___x_2488_);
lean_ctor_set(v___x_2489_, 1, v___x_2488_);
lean_ctor_set(v___x_2489_, 2, v___x_2488_);
lean_ctor_set(v___x_2489_, 3, v___x_2488_);
lean_ctor_set(v___x_2489_, 4, v___x_2488_);
return v___x_2489_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__36_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2491_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2492_ = l_Lean_stringToMessageData(v___x_2491_);
return v___x_2492_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__38_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2494_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__37_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2495_ = l_Lean_stringToMessageData(v___x_2494_);
return v___x_2495_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__40_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2497_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__39_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2498_ = l_Lean_stringToMessageData(v___x_2497_);
return v___x_2498_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2500_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2501_ = l_Lean_stringToMessageData(v___x_2500_);
return v___x_2501_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2503_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2504_ = l_Lean_stringToMessageData(v___x_2503_);
return v___x_2504_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2506_; lean_object* v___x_2507_; 
v___x_2506_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2507_ = l_Lean_stringToMessageData(v___x_2506_);
return v___x_2507_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__48_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2509_; lean_object* v___x_2510_; 
v___x_2509_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__47_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2510_ = l_Lean_stringToMessageData(v___x_2509_);
return v___x_2510_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__50_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2512_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__49_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2513_ = l_Lean_stringToMessageData(v___x_2512_);
return v___x_2513_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__52_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2515_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__51_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2516_ = l_Lean_stringToMessageData(v___x_2515_);
return v___x_2516_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__54_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___x_2518_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__53_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2519_ = l_Lean_stringToMessageData(v___x_2518_);
return v___x_2519_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__56_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2521_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__55_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2522_ = l_Lean_stringToMessageData(v___x_2521_);
return v___x_2522_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__58_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2524_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__57_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2525_ = l_Lean_stringToMessageData(v___x_2524_);
return v___x_2525_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__60_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2527_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__59_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2528_ = l_Lean_stringToMessageData(v___x_2527_);
return v___x_2528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(lean_object* v___x_2529_, lean_object* v___x_2530_, lean_object* v___f_2531_, uint8_t v___x_2532_, lean_object* v___x_2533_, lean_object* v___x_2534_, lean_object* v_a_2535_, lean_object* v_declName_2536_, lean_object* v_stx_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_){
_start:
{
lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___x_2547_; uint8_t v___x_2548_; lean_object* v___y_2550_; lean_object* v___y_2551_; lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2594_; lean_object* v___y_2595_; lean_object* v___y_2596_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2611_; lean_object* v___y_2612_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2615_; lean_object* v___y_2616_; lean_object* v___y_2628_; lean_object* v___y_2629_; lean_object* v___y_2630_; lean_object* v___y_2631_; lean_object* v___y_2632_; lean_object* v___y_2633_; lean_object* v_hint_2634_; lean_object* v___y_2635_; lean_object* v___y_2636_; lean_object* v___y_2659_; lean_object* v___y_2660_; lean_object* v___y_2661_; lean_object* v___y_2662_; lean_object* v___y_2663_; lean_object* v___y_2664_; lean_object* v___y_2665_; lean_object* v___y_2666_; 
v___x_2547_ = l_Lean_Name_mkStr2(v___x_2529_, v___x_2530_);
lean_inc(v_stx_2537_);
v___x_2548_ = l_Lean_Syntax_isOfKind(v_stx_2537_, v___x_2547_);
lean_dec(v___x_2547_);
if (v___x_2548_ == 0)
{
lean_object* v___x_2668_; lean_object* v___x_2669_; 
lean_dec(v_stx_2537_);
lean_dec(v_declName_2536_);
lean_dec_ref(v___x_2534_);
lean_dec(v___x_2533_);
lean_dec_ref(v___f_2531_);
v___x_2668_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2669_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0___redArg(v___x_2668_, v___y_2538_, v___y_2539_);
return v___x_2669_;
}
else
{
lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___y_2673_; lean_object* v___y_2674_; lean_object* v___y_2675_; lean_object* v___y_2676_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v_val_2681_; lean_object* v___y_2706_; lean_object* v___y_2707_; lean_object* v___y_2708_; lean_object* v___y_2709_; lean_object* v___y_2710_; lean_object* v___y_2711_; lean_object* v___y_2712_; lean_object* v___y_2713_; lean_object* v___y_2718_; lean_object* v___y_2719_; lean_object* v___y_2720_; lean_object* v___y_2721_; lean_object* v___y_2722_; lean_object* v___y_2723_; lean_object* v___y_2724_; lean_object* v___y_2725_; uint8_t v___y_2726_; lean_object* v___y_2727_; uint8_t v_a_2728_; lean_object* v___y_2743_; lean_object* v___y_2744_; lean_object* v___y_2745_; lean_object* v___y_2746_; lean_object* v___y_2747_; lean_object* v___y_2748_; uint8_t v___y_2749_; lean_object* v___y_2750_; lean_object* v___y_2751_; lean_object* v___y_2752_; lean_object* v___y_2788_; lean_object* v___y_2789_; lean_object* v___y_2790_; lean_object* v___y_2791_; lean_object* v___y_2792_; lean_object* v___y_2793_; uint8_t v___y_2794_; lean_object* v___y_2795_; lean_object* v_msg_2796_; lean_object* v___y_2797_; lean_object* v___y_2798_; lean_object* v___y_2809_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v___y_2815_; lean_object* v___y_2816_; lean_object* v___y_2817_; lean_object* v___y_2818_; lean_object* v___y_2819_; uint8_t v___y_2820_; lean_object* v___y_2821_; lean_object* v_a_2822_; lean_object* v___y_2855_; lean_object* v___y_2856_; lean_object* v___y_2857_; lean_object* v___y_2858_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v___y_2861_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_2962_; lean_object* v___y_2963_; lean_object* v___y_2964_; lean_object* v___y_2965_; lean_object* v_a_2966_; lean_object* v___y_2984_; lean_object* v___y_2985_; lean_object* v___y_2986_; lean_object* v_since_x3f_2987_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v_typeChanged_x3f_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3022_; lean_object* v_text_x3f_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v_id_x3f_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___x_3048_; uint8_t v___x_3049_; 
v___x_2670_ = lean_unsigned_to_nat(0u);
v___x_2671_ = lean_unsigned_to_nat(1u);
v___x_3048_ = l_Lean_Syntax_getArg(v_stx_2537_, v___x_2671_);
v___x_3049_ = l_Lean_Syntax_isNone(v___x_3048_);
if (v___x_3049_ == 0)
{
uint8_t v___x_3050_; 
lean_inc(v___x_3048_);
v___x_3050_ = l_Lean_Syntax_matchesNull(v___x_3048_, v___x_2671_);
if (v___x_3050_ == 0)
{
lean_object* v___x_3051_; lean_object* v___x_3052_; 
lean_dec(v___x_3048_);
lean_dec(v_stx_2537_);
lean_dec(v_declName_2536_);
lean_dec_ref(v___x_2534_);
lean_dec(v___x_2533_);
lean_dec_ref(v___f_2531_);
v___x_3051_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_3052_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0___redArg(v___x_3051_, v___y_2538_, v___y_2539_);
return v___x_3052_;
}
else
{
lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3053_ = l_Lean_Syntax_getArg(v___x_3048_, v___x_2670_);
lean_dec(v___x_3048_);
v___x_3054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3053_);
v_id_x3f_3036_ = v___x_3054_;
v___y_3037_ = v___y_2538_;
v___y_3038_ = v___y_2539_;
goto v___jp_3035_;
}
}
else
{
lean_object* v___x_3055_; 
lean_dec(v___x_3048_);
v___x_3055_ = lean_box(0);
v_id_x3f_3036_ = v___x_3055_;
v___y_3037_ = v___y_2538_;
v___y_3038_ = v___y_2539_;
goto v___jp_3035_;
}
v___jp_2672_:
{
lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; uint8_t v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; 
v___x_2682_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__19_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__19_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__19_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2683_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__21_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2684_ = lean_box(0);
v___x_2685_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__25_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__25_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__25_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2686_, 0, v___f_2531_);
v___x_2687_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2687_, 0, v___x_2683_);
lean_ctor_set(v___x_2687_, 1, v___x_2684_);
lean_ctor_set(v___x_2687_, 2, v___x_2684_);
lean_ctor_set(v___x_2687_, 3, v___x_2684_);
lean_ctor_set(v___x_2687_, 4, v___x_2685_);
lean_ctor_set(v___x_2687_, 5, v___x_2686_);
lean_inc(v_val_2681_);
v___x_2688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2688_, 0, v_val_2681_);
lean_ctor_set(v___x_2688_, 1, v_val_2681_);
v___x_2689_ = l_Lean_Syntax_ofRange(v___x_2688_, v___x_2548_);
v___x_2690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2689_);
v___x_2691_ = 4;
v___x_2692_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2692_, 0, v___x_2687_);
lean_ctor_set(v___x_2692_, 1, v___x_2690_);
lean_ctor_set(v___x_2692_, 2, v___x_2684_);
lean_ctor_set_uint8(v___x_2692_, sizeof(void*)*3, v___x_2691_);
v___x_2693_ = lean_mk_empty_array_with_capacity(v___x_2671_);
v___x_2694_ = lean_array_push(v___x_2693_, v___x_2692_);
v___x_2695_ = l_Lean_MessageData_hint(v___x_2682_, v___x_2694_, v___x_2684_, v___x_2684_, v___x_2532_, v___y_2676_, v___y_2674_);
lean_dec_ref(v___x_2694_);
if (lean_obj_tag(v___x_2695_) == 0)
{
lean_object* v_a_2696_; 
v_a_2696_ = lean_ctor_get(v___x_2695_, 0);
lean_inc(v_a_2696_);
lean_dec_ref_known(v___x_2695_, 1);
v___y_2628_ = v___y_2673_;
v___y_2629_ = v___y_2675_;
v___y_2630_ = v___y_2677_;
v___y_2631_ = v___y_2678_;
v___y_2632_ = v___y_2679_;
v___y_2633_ = v___y_2680_;
v_hint_2634_ = v_a_2696_;
v___y_2635_ = v___y_2676_;
v___y_2636_ = v___y_2674_;
goto v___jp_2627_;
}
else
{
lean_object* v_a_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2704_; 
lean_dec_ref(v___y_2680_);
lean_dec_ref(v___y_2679_);
lean_dec(v___y_2678_);
lean_dec(v___y_2677_);
lean_dec(v___y_2675_);
lean_dec(v___y_2673_);
lean_dec(v_stx_2537_);
v_a_2697_ = lean_ctor_get(v___x_2695_, 0);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2695_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2699_ = v___x_2695_;
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_a_2697_);
lean_dec(v___x_2695_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v___x_2702_; 
if (v_isShared_2700_ == 0)
{
v___x_2702_ = v___x_2699_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_a_2697_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
return v___x_2702_;
}
}
}
}
v___jp_2705_:
{
if (lean_obj_tag(v___y_2711_) == 0)
{
lean_dec_ref(v___f_2531_);
v___y_2659_ = v___y_2707_;
v___y_2660_ = v___y_2706_;
v___y_2661_ = v___y_2708_;
v___y_2662_ = v___y_2709_;
v___y_2663_ = v___y_2710_;
v___y_2664_ = v___y_2711_;
v___y_2665_ = v___y_2712_;
v___y_2666_ = v___y_2713_;
goto v___jp_2658_;
}
else
{
lean_object* v_val_2714_; lean_object* v___x_2715_; 
v_val_2714_ = lean_ctor_get(v___y_2711_, 0);
v___x_2715_ = l_Lean_Syntax_getTailPos_x3f(v_val_2714_, v___x_2548_);
if (lean_obj_tag(v___x_2715_) == 1)
{
lean_object* v_val_2716_; 
v_val_2716_ = lean_ctor_get(v___x_2715_, 0);
lean_inc(v_val_2716_);
lean_dec_ref_known(v___x_2715_, 1);
v___y_2673_ = v___y_2707_;
v___y_2674_ = v___y_2706_;
v___y_2675_ = v___y_2708_;
v___y_2676_ = v___y_2709_;
v___y_2677_ = v___y_2710_;
v___y_2678_ = v___y_2711_;
v___y_2679_ = v___y_2712_;
v___y_2680_ = v___y_2713_;
v_val_2681_ = v_val_2716_;
goto v___jp_2672_;
}
else
{
lean_dec(v___x_2715_);
lean_dec_ref(v___f_2531_);
v___y_2659_ = v___y_2707_;
v___y_2660_ = v___y_2706_;
v___y_2661_ = v___y_2708_;
v___y_2662_ = v___y_2709_;
v___y_2663_ = v___y_2710_;
v___y_2664_ = v___y_2711_;
v___y_2665_ = v___y_2712_;
v___y_2666_ = v___y_2713_;
goto v___jp_2658_;
}
}
}
v___jp_2717_:
{
if (v_a_2728_ == 0)
{
if (lean_obj_tag(v___y_2724_) == 0)
{
if (v___y_2726_ == 0)
{
lean_dec_ref(v___y_2727_);
lean_dec_ref(v___y_2725_);
lean_dec_ref(v___f_2531_);
v___y_2611_ = v___y_2719_;
v___y_2612_ = v___y_2720_;
v___y_2613_ = v___y_2722_;
v___y_2614_ = v___y_2723_;
v___y_2615_ = v___y_2721_;
v___y_2616_ = v___y_2718_;
goto v___jp_2610_;
}
else
{
if (lean_obj_tag(v___y_2722_) == 0)
{
v___y_2706_ = v___y_2718_;
v___y_2707_ = v___y_2719_;
v___y_2708_ = v___y_2720_;
v___y_2709_ = v___y_2721_;
v___y_2710_ = v___y_2722_;
v___y_2711_ = v___y_2723_;
v___y_2712_ = v___y_2725_;
v___y_2713_ = v___y_2727_;
goto v___jp_2705_;
}
else
{
lean_object* v_val_2729_; lean_object* v___x_2730_; 
v_val_2729_ = lean_ctor_get(v___y_2722_, 0);
v___x_2730_ = l_Lean_Syntax_getTailPos_x3f(v_val_2729_, v___x_2548_);
if (lean_obj_tag(v___x_2730_) == 0)
{
v___y_2706_ = v___y_2718_;
v___y_2707_ = v___y_2719_;
v___y_2708_ = v___y_2720_;
v___y_2709_ = v___y_2721_;
v___y_2710_ = v___y_2722_;
v___y_2711_ = v___y_2723_;
v___y_2712_ = v___y_2725_;
v___y_2713_ = v___y_2727_;
goto v___jp_2705_;
}
else
{
lean_object* v_val_2731_; 
v_val_2731_ = lean_ctor_get(v___x_2730_, 0);
lean_inc(v_val_2731_);
lean_dec_ref_known(v___x_2730_, 1);
v___y_2673_ = v___y_2719_;
v___y_2674_ = v___y_2718_;
v___y_2675_ = v___y_2720_;
v___y_2676_ = v___y_2721_;
v___y_2677_ = v___y_2722_;
v___y_2678_ = v___y_2723_;
v___y_2679_ = v___y_2725_;
v___y_2680_ = v___y_2727_;
v_val_2681_ = v_val_2731_;
goto v___jp_2672_;
}
}
}
}
else
{
lean_dec_ref_known(v___y_2724_, 1);
lean_dec_ref(v___y_2727_);
lean_dec_ref(v___y_2725_);
lean_dec_ref(v___f_2531_);
v___y_2611_ = v___y_2719_;
v___y_2612_ = v___y_2720_;
v___y_2613_ = v___y_2722_;
v___y_2614_ = v___y_2723_;
v___y_2615_ = v___y_2721_;
v___y_2616_ = v___y_2718_;
goto v___jp_2610_;
}
}
else
{
lean_dec_ref(v___y_2727_);
lean_dec_ref(v___y_2725_);
lean_dec_ref(v___f_2531_);
if (lean_obj_tag(v___y_2724_) == 0)
{
v___y_2611_ = v___y_2719_;
v___y_2612_ = v___y_2720_;
v___y_2613_ = v___y_2722_;
v___y_2614_ = v___y_2723_;
v___y_2615_ = v___y_2721_;
v___y_2616_ = v___y_2718_;
goto v___jp_2610_;
}
else
{
lean_object* v___x_2732_; lean_object* v___x_2733_; 
lean_dec_ref_known(v___y_2724_, 1);
v___x_2732_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__28_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__28_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__28_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2733_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1(v___x_2732_, v___y_2721_, v___y_2718_);
if (lean_obj_tag(v___x_2733_) == 0)
{
lean_dec_ref_known(v___x_2733_, 1);
v___y_2611_ = v___y_2719_;
v___y_2612_ = v___y_2720_;
v___y_2613_ = v___y_2722_;
v___y_2614_ = v___y_2723_;
v___y_2615_ = v___y_2721_;
v___y_2616_ = v___y_2718_;
goto v___jp_2610_;
}
else
{
lean_object* v_a_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2741_; 
lean_dec(v___y_2723_);
lean_dec(v___y_2722_);
lean_dec(v___y_2720_);
lean_dec(v___y_2719_);
lean_dec(v_stx_2537_);
v_a_2734_ = lean_ctor_get(v___x_2733_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2736_ = v___x_2733_;
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_a_2734_);
lean_dec(v___x_2733_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___x_2739_; 
if (v_isShared_2737_ == 0)
{
v___x_2739_ = v___x_2736_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v_a_2734_);
v___x_2739_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
return v___x_2739_;
}
}
}
}
}
}
v___jp_2742_:
{
lean_object* v___x_2753_; 
lean_inc_ref(v___y_2743_);
v___x_2753_ = l_Lean_Environment_find_x3f(v___y_2743_, v_declName_2536_, v___x_2532_);
if (lean_obj_tag(v___x_2753_) == 1)
{
lean_object* v_val_2754_; lean_object* v___x_2755_; 
v_val_2754_ = lean_ctor_get(v___x_2753_, 0);
lean_inc(v_val_2754_);
lean_dec_ref_known(v___x_2753_, 1);
v___x_2755_ = l_Lean_Environment_find_x3f(v___y_2743_, v___y_2750_, v___x_2532_);
if (lean_obj_tag(v___x_2755_) == 1)
{
lean_object* v_val_2756_; uint8_t v___x_2757_; uint8_t v___x_2758_; uint8_t v___x_2759_; lean_object* v___x_2760_; uint64_t v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
v_val_2756_ = lean_ctor_get(v___x_2755_, 0);
lean_inc(v_val_2756_);
lean_dec_ref_known(v___x_2755_, 1);
v___x_2757_ = 1;
v___x_2758_ = 0;
v___x_2759_ = 2;
v___x_2760_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_2760_, 0, v___x_2532_);
lean_ctor_set_uint8(v___x_2760_, 1, v___x_2532_);
lean_ctor_set_uint8(v___x_2760_, 2, v___x_2532_);
lean_ctor_set_uint8(v___x_2760_, 3, v___x_2532_);
lean_ctor_set_uint8(v___x_2760_, 4, v___x_2532_);
lean_ctor_set_uint8(v___x_2760_, 5, v___y_2749_);
lean_ctor_set_uint8(v___x_2760_, 6, v___y_2749_);
lean_ctor_set_uint8(v___x_2760_, 7, v___x_2532_);
lean_ctor_set_uint8(v___x_2760_, 8, v___y_2749_);
lean_ctor_set_uint8(v___x_2760_, 9, v___x_2757_);
lean_ctor_set_uint8(v___x_2760_, 10, v___x_2758_);
lean_ctor_set_uint8(v___x_2760_, 11, v___y_2749_);
lean_ctor_set_uint8(v___x_2760_, 12, v___y_2749_);
lean_ctor_set_uint8(v___x_2760_, 13, v___y_2749_);
lean_ctor_set_uint8(v___x_2760_, 14, v___x_2759_);
lean_ctor_set_uint8(v___x_2760_, 15, v___y_2749_);
lean_ctor_set_uint8(v___x_2760_, 16, v___y_2749_);
lean_ctor_set_uint8(v___x_2760_, 17, v___y_2749_);
lean_ctor_set_uint8(v___x_2760_, 18, v___y_2749_);
lean_ctor_set_uint8(v___x_2760_, 19, v___x_2532_);
v___x_2761_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2760_);
v___x_2762_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2762_, 0, v___x_2760_);
lean_ctor_set_uint64(v___x_2762_, sizeof(void*)*1, v___x_2761_);
v___x_2763_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_2764_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2765_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2766_ = lean_box(0);
lean_inc(v___x_2533_);
v___x_2767_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2767_, 0, v___x_2762_);
lean_ctor_set(v___x_2767_, 1, v___x_2533_);
lean_ctor_set(v___x_2767_, 2, v___x_2764_);
lean_ctor_set(v___x_2767_, 3, v___x_2765_);
lean_ctor_set(v___x_2767_, 4, v___x_2766_);
lean_ctor_set(v___x_2767_, 5, v___x_2670_);
lean_ctor_set(v___x_2767_, 6, v___x_2766_);
lean_ctor_set_uint8(v___x_2767_, sizeof(void*)*7, v___x_2532_);
lean_ctor_set_uint8(v___x_2767_, sizeof(void*)*7 + 1, v___x_2532_);
lean_ctor_set_uint8(v___x_2767_, sizeof(void*)*7 + 2, v___x_2532_);
lean_ctor_set_uint8(v___x_2767_, sizeof(void*)*7 + 3, v___x_2548_);
v___x_2768_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2769_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2770_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2771_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2771_, 0, v___x_2768_);
lean_ctor_set(v___x_2771_, 1, v___x_2769_);
lean_ctor_set(v___x_2771_, 2, v___x_2533_);
lean_ctor_set(v___x_2771_, 3, v___x_2763_);
lean_ctor_set(v___x_2771_, 4, v___x_2770_);
v___x_2772_ = lean_st_mk_ref(v___x_2771_);
v___x_2773_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq(v_val_2754_, v_val_2756_, v___x_2767_, v___x_2772_, v___y_2751_, v___y_2752_);
lean_dec_ref_known(v___x_2767_, 7);
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_object* v_a_2774_; lean_object* v___x_2775_; uint8_t v___x_2776_; 
v_a_2774_ = lean_ctor_get(v___x_2773_, 0);
lean_inc(v_a_2774_);
lean_dec_ref_known(v___x_2773_, 1);
v___x_2775_ = lean_st_ref_get(v___x_2772_);
lean_dec(v___x_2772_);
lean_dec(v___x_2775_);
v___x_2776_ = lean_unbox(v_a_2774_);
lean_dec(v_a_2774_);
v___y_2718_ = v___y_2752_;
v___y_2719_ = v___y_2744_;
v___y_2720_ = v___y_2745_;
v___y_2721_ = v___y_2751_;
v___y_2722_ = v___y_2746_;
v___y_2723_ = v___y_2747_;
v___y_2724_ = v___y_2748_;
v___y_2725_ = v_val_2756_;
v___y_2726_ = v___y_2749_;
v___y_2727_ = v_val_2754_;
v_a_2728_ = v___x_2776_;
goto v___jp_2717_;
}
else
{
lean_dec(v___x_2772_);
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_object* v_a_2777_; uint8_t v___x_2778_; 
v_a_2777_ = lean_ctor_get(v___x_2773_, 0);
lean_inc(v_a_2777_);
lean_dec_ref_known(v___x_2773_, 1);
v___x_2778_ = lean_unbox(v_a_2777_);
lean_dec(v_a_2777_);
v___y_2718_ = v___y_2752_;
v___y_2719_ = v___y_2744_;
v___y_2720_ = v___y_2745_;
v___y_2721_ = v___y_2751_;
v___y_2722_ = v___y_2746_;
v___y_2723_ = v___y_2747_;
v___y_2724_ = v___y_2748_;
v___y_2725_ = v_val_2756_;
v___y_2726_ = v___y_2749_;
v___y_2727_ = v_val_2754_;
v_a_2728_ = v___x_2778_;
goto v___jp_2717_;
}
else
{
lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2786_; 
lean_dec(v_val_2756_);
lean_dec(v_val_2754_);
lean_dec(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec(v___y_2744_);
lean_dec(v_stx_2537_);
lean_dec_ref(v___f_2531_);
v_a_2779_ = lean_ctor_get(v___x_2773_, 0);
v_isSharedCheck_2786_ = !lean_is_exclusive(v___x_2773_);
if (v_isSharedCheck_2786_ == 0)
{
v___x_2781_ = v___x_2773_;
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v___x_2773_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v___x_2784_; 
if (v_isShared_2782_ == 0)
{
v___x_2784_ = v___x_2781_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_a_2779_);
v___x_2784_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
return v___x_2784_;
}
}
}
}
}
else
{
lean_dec(v___x_2755_);
lean_dec(v_val_2754_);
lean_dec(v___y_2748_);
lean_dec(v___x_2533_);
lean_dec_ref(v___f_2531_);
v___y_2611_ = v___y_2744_;
v___y_2612_ = v___y_2745_;
v___y_2613_ = v___y_2746_;
v___y_2614_ = v___y_2747_;
v___y_2615_ = v___y_2751_;
v___y_2616_ = v___y_2752_;
goto v___jp_2610_;
}
}
else
{
lean_dec(v___x_2753_);
lean_dec(v___y_2750_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2743_);
lean_dec(v___x_2533_);
lean_dec_ref(v___f_2531_);
v___y_2611_ = v___y_2744_;
v___y_2612_ = v___y_2745_;
v___y_2613_ = v___y_2746_;
v___y_2614_ = v___y_2747_;
v___y_2615_ = v___y_2751_;
v___y_2616_ = v___y_2752_;
goto v___jp_2610_;
}
}
v___jp_2787_:
{
lean_object* v___x_2799_; 
v___x_2799_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1(v_msg_2796_, v___y_2797_, v___y_2798_);
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_dec_ref_known(v___x_2799_, 1);
v___y_2743_ = v___y_2788_;
v___y_2744_ = v___y_2789_;
v___y_2745_ = v___y_2790_;
v___y_2746_ = v___y_2791_;
v___y_2747_ = v___y_2792_;
v___y_2748_ = v___y_2793_;
v___y_2749_ = v___y_2794_;
v___y_2750_ = v___y_2795_;
v___y_2751_ = v___y_2797_;
v___y_2752_ = v___y_2798_;
goto v___jp_2742_;
}
else
{
lean_object* v_a_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2807_; 
lean_dec(v___y_2795_);
lean_dec(v___y_2793_);
lean_dec(v___y_2792_);
lean_dec(v___y_2791_);
lean_dec(v___y_2790_);
lean_dec(v___y_2789_);
lean_dec_ref(v___y_2788_);
lean_dec(v_stx_2537_);
lean_dec(v_declName_2536_);
lean_dec(v___x_2533_);
lean_dec_ref(v___f_2531_);
v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2802_ = v___x_2799_;
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_a_2800_);
lean_dec(v___x_2799_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2805_; 
if (v_isShared_2803_ == 0)
{
v___x_2805_ = v___x_2802_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2800_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
}
v___jp_2808_:
{
if (lean_obj_tag(v_a_2822_) == 1)
{
lean_object* v_val_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2853_; 
v_val_2823_ = lean_ctor_get(v_a_2822_, 0);
v_isSharedCheck_2853_ = !lean_is_exclusive(v_a_2822_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2825_ = v_a_2822_;
v_isShared_2826_ = v_isSharedCheck_2853_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_val_2823_);
lean_dec(v_a_2822_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2853_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; uint8_t v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2840_; 
v___x_2827_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__36_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__36_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__36_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2827_);
lean_ctor_set(v___x_2828_, 1, v___y_2819_);
v___x_2829_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__38_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__38_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__38_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2830_, 0, v___x_2828_);
lean_ctor_set(v___x_2830_, 1, v___x_2829_);
v___x_2831_ = l_Lean_Name_toString(v_val_2823_, v___x_2548_);
v___x_2832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2832_, 0, v___x_2831_);
v___x_2833_ = lean_box(0);
v___x_2834_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2834_, 0, v___x_2832_);
lean_ctor_set(v___x_2834_, 1, v___x_2833_);
lean_ctor_set(v___x_2834_, 2, v___x_2833_);
lean_ctor_set(v___x_2834_, 3, v___x_2833_);
lean_ctor_set(v___x_2834_, 4, v___x_2833_);
lean_ctor_set(v___x_2834_, 5, v___x_2833_);
v___x_2835_ = 0;
v___x_2836_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2836_, 0, v___x_2834_);
lean_ctor_set(v___x_2836_, 1, v___x_2833_);
lean_ctor_set(v___x_2836_, 2, v___x_2833_);
lean_ctor_set_uint8(v___x_2836_, sizeof(void*)*3, v___x_2835_);
v___x_2837_ = lean_mk_empty_array_with_capacity(v___x_2671_);
v___x_2838_ = lean_array_push(v___x_2837_, v___x_2836_);
if (v_isShared_2826_ == 0)
{
lean_ctor_set(v___x_2825_, 0, v___y_2812_);
v___x_2840_ = v___x_2825_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v___y_2812_);
v___x_2840_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
lean_object* v___x_2841_; 
v___x_2841_ = l_Lean_MessageData_hint(v___x_2830_, v___x_2838_, v___x_2840_, v___x_2833_, v___x_2532_, v___y_2817_, v___y_2814_);
lean_dec_ref(v___x_2838_);
if (lean_obj_tag(v___x_2841_) == 0)
{
lean_object* v_a_2842_; lean_object* v___x_2843_; 
v_a_2842_ = lean_ctor_get(v___x_2841_, 0);
lean_inc(v_a_2842_);
lean_dec_ref_known(v___x_2841_, 1);
v___x_2843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2843_, 0, v___y_2813_);
lean_ctor_set(v___x_2843_, 1, v_a_2842_);
v___y_2788_ = v___y_2815_;
v___y_2789_ = v___y_2809_;
v___y_2790_ = v___y_2816_;
v___y_2791_ = v___y_2810_;
v___y_2792_ = v___y_2818_;
v___y_2793_ = v___y_2811_;
v___y_2794_ = v___y_2820_;
v___y_2795_ = v___y_2821_;
v_msg_2796_ = v___x_2843_;
v___y_2797_ = v___y_2817_;
v___y_2798_ = v___y_2814_;
goto v___jp_2787_;
}
else
{
lean_object* v_a_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2851_; 
lean_dec(v___y_2821_);
lean_dec(v___y_2818_);
lean_dec(v___y_2816_);
lean_dec_ref(v___y_2815_);
lean_dec_ref(v___y_2813_);
lean_dec(v___y_2811_);
lean_dec(v___y_2810_);
lean_dec(v___y_2809_);
lean_dec(v_stx_2537_);
lean_dec(v_declName_2536_);
lean_dec(v___x_2533_);
lean_dec_ref(v___f_2531_);
v_a_2844_ = lean_ctor_get(v___x_2841_, 0);
v_isSharedCheck_2851_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2851_ == 0)
{
v___x_2846_ = v___x_2841_;
v_isShared_2847_ = v_isSharedCheck_2851_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_a_2844_);
lean_dec(v___x_2841_);
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
}
}
else
{
lean_dec(v_a_2822_);
lean_dec_ref(v___y_2819_);
lean_dec(v___y_2812_);
v___y_2788_ = v___y_2815_;
v___y_2789_ = v___y_2809_;
v___y_2790_ = v___y_2816_;
v___y_2791_ = v___y_2810_;
v___y_2792_ = v___y_2818_;
v___y_2793_ = v___y_2811_;
v___y_2794_ = v___y_2820_;
v___y_2795_ = v___y_2821_;
v_msg_2796_ = v___y_2813_;
v___y_2797_ = v___y_2817_;
v___y_2798_ = v___y_2814_;
goto v___jp_2787_;
}
}
v___jp_2854_:
{
if (lean_obj_tag(v___y_2855_) == 1)
{
lean_object* v_val_2862_; lean_object* v___x_2863_; 
v_val_2862_ = lean_ctor_get(v___y_2855_, 0);
lean_inc(v_val_2862_);
v___x_2863_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2(v_val_2862_, v___x_2532_, v___y_2860_, v___y_2861_);
if (lean_obj_tag(v___x_2863_) == 0)
{
lean_object* v___x_2864_; lean_object* v_a_2865_; lean_object* v___x_2866_; uint8_t v___x_2867_; 
lean_dec_ref_known(v___x_2863_, 1);
v___x_2864_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3(v___y_2860_, v___y_2861_);
v_a_2865_ = lean_ctor_get(v___x_2864_, 0);
lean_inc(v_a_2865_);
lean_dec_ref(v___x_2864_);
v___x_2866_ = l_Lean_Linter_linter_deprecated;
v___x_2867_ = l_Lean_Linter_getLinterValue(v___x_2866_, v_a_2865_);
lean_dec(v_a_2865_);
if (v___x_2867_ == 0)
{
lean_dec(v___y_2859_);
lean_dec(v_declName_2536_);
lean_dec_ref(v___x_2534_);
lean_dec(v___x_2533_);
lean_dec_ref(v___f_2531_);
v___y_2611_ = v___y_2855_;
v___y_2612_ = v___y_2856_;
v___y_2613_ = v___y_2857_;
v___y_2614_ = v___y_2858_;
v___y_2615_ = v___y_2860_;
v___y_2616_ = v___y_2861_;
goto v___jp_2610_;
}
else
{
lean_object* v___x_2868_; lean_object* v_env_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; uint8_t v___x_2872_; 
lean_inc(v_val_2862_);
v___x_2868_ = lean_st_ref_get(v___y_2861_);
v_env_2869_ = lean_ctor_get(v___x_2868_, 0);
lean_inc_ref(v_env_2869_);
lean_dec(v___x_2868_);
v___x_2870_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2860_);
v___x_2871_ = l_Lean_Linter_linter_deprecated_deprecatedTarget;
v___x_2872_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4(v___x_2870_, v___x_2871_);
lean_dec_ref(v___x_2870_);
if (v___x_2872_ == 0)
{
lean_dec_ref(v___x_2534_);
v___y_2743_ = v_env_2869_;
v___y_2744_ = v___y_2855_;
v___y_2745_ = v___y_2856_;
v___y_2746_ = v___y_2857_;
v___y_2747_ = v___y_2858_;
v___y_2748_ = v___y_2859_;
v___y_2749_ = v___x_2867_;
v___y_2750_ = v_val_2862_;
v___y_2751_ = v___y_2860_;
v___y_2752_ = v___y_2861_;
goto v___jp_2742_;
}
else
{
lean_object* v___x_2873_; 
lean_inc(v_val_2862_);
lean_inc_ref(v_env_2869_);
v___x_2873_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v___x_2534_, v_a_2535_, v___x_2532_, v_env_2869_, v_val_2862_);
if (lean_obj_tag(v___x_2873_) == 1)
{
lean_object* v_val_2874_; lean_object* v_name_2875_; lean_object* v_newName_x3f_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; 
v_val_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc(v_val_2874_);
lean_dec_ref_known(v___x_2873_, 1);
v_name_2875_ = lean_ctor_get(v___x_2871_, 0);
v_newName_x3f_2876_ = lean_ctor_get(v_val_2874_, 0);
lean_inc(v_newName_x3f_2876_);
lean_dec(v_val_2874_);
v___x_2877_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__40_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__40_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__40_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
lean_inc(v_name_2875_);
v___x_2878_ = l_Lean_MessageData_ofName(v_name_2875_);
v___x_2879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2877_);
lean_ctor_set(v___x_2879_, 1, v___x_2878_);
v___x_2880_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2881_, 0, v___x_2879_);
lean_ctor_set(v___x_2881_, 1, v___x_2880_);
v___x_2882_ = l_Lean_MessageData_note(v___x_2881_);
if (lean_obj_tag(v_newName_x3f_2876_) == 0)
{
lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2883_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
lean_inc(v_val_2862_);
v___x_2884_ = l_Lean_MessageData_ofConstName(v_val_2862_, v___x_2548_);
v___x_2885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2885_, 0, v___x_2883_);
lean_ctor_set(v___x_2885_, 1, v___x_2884_);
v___x_2886_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2885_);
lean_ctor_set(v___x_2887_, 1, v___x_2886_);
lean_inc(v_declName_2536_);
v___x_2888_ = l_Lean_MessageData_ofConstName(v_declName_2536_, v___x_2548_);
v___x_2889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2889_, 0, v___x_2887_);
lean_ctor_set(v___x_2889_, 1, v___x_2888_);
v___x_2890_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__48_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__48_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__48_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2891_, 0, v___x_2889_);
lean_ctor_set(v___x_2891_, 1, v___x_2890_);
v___x_2892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2891_);
lean_ctor_set(v___x_2892_, 1, v___x_2882_);
v___x_2893_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1(v___x_2892_, v___y_2860_, v___y_2861_);
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_dec_ref_known(v___x_2893_, 1);
v___y_2743_ = v_env_2869_;
v___y_2744_ = v___y_2855_;
v___y_2745_ = v___y_2856_;
v___y_2746_ = v___y_2857_;
v___y_2747_ = v___y_2858_;
v___y_2748_ = v___y_2859_;
v___y_2749_ = v___x_2867_;
v___y_2750_ = v_val_2862_;
v___y_2751_ = v___y_2860_;
v___y_2752_ = v___y_2861_;
goto v___jp_2742_;
}
else
{
lean_object* v_a_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2901_; 
lean_dec_ref(v_env_2869_);
lean_dec_ref_known(v___y_2855_, 1);
lean_dec(v_val_2862_);
lean_dec(v___y_2859_);
lean_dec(v___y_2858_);
lean_dec(v___y_2857_);
lean_dec(v___y_2856_);
lean_dec(v_stx_2537_);
lean_dec(v_declName_2536_);
lean_dec(v___x_2533_);
lean_dec_ref(v___f_2531_);
v_a_2894_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2901_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2896_ = v___x_2893_;
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_a_2894_);
lean_dec(v___x_2893_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2899_; 
if (v_isShared_2897_ == 0)
{
v___x_2899_ = v___x_2896_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_a_2894_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
return v___x_2899_;
}
}
}
}
else
{
lean_object* v_val_2902_; uint8_t v___x_2903_; 
v_val_2902_ = lean_ctor_get(v_newName_x3f_2876_, 0);
lean_inc(v_val_2902_);
lean_dec_ref_known(v_newName_x3f_2876_, 1);
v___x_2903_ = lean_name_eq(v_val_2902_, v_val_2862_);
if (v___x_2903_ == 0)
{
if (v___x_2872_ == 0)
{
lean_dec(v_val_2902_);
lean_dec_ref(v___x_2882_);
v___y_2743_ = v_env_2869_;
v___y_2744_ = v___y_2855_;
v___y_2745_ = v___y_2856_;
v___y_2746_ = v___y_2857_;
v___y_2747_ = v___y_2858_;
v___y_2748_ = v___y_2859_;
v___y_2749_ = v___x_2867_;
v___y_2750_ = v_val_2862_;
v___y_2751_ = v___y_2860_;
v___y_2752_ = v___y_2861_;
goto v___jp_2742_;
}
else
{
lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; 
v___x_2904_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
lean_inc(v_val_2862_);
v___x_2905_ = l_Lean_MessageData_ofConstName(v_val_2862_, v___x_2548_);
v___x_2906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2906_, 0, v___x_2904_);
lean_ctor_set(v___x_2906_, 1, v___x_2905_);
v___x_2907_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__50_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__50_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__50_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2908_, 0, v___x_2906_);
lean_ctor_set(v___x_2908_, 1, v___x_2907_);
lean_inc(v_val_2902_);
v___x_2909_ = l_Lean_MessageData_ofConstName(v_val_2902_, v___x_2548_);
lean_inc_ref_n(v___x_2909_, 2);
v___x_2910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2910_, 0, v___x_2908_);
lean_ctor_set(v___x_2910_, 1, v___x_2909_);
v___x_2911_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__52_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__52_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__52_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2910_);
lean_ctor_set(v___x_2912_, 1, v___x_2911_);
lean_inc(v_declName_2536_);
v___x_2913_ = l_Lean_MessageData_ofConstName(v_declName_2536_, v___x_2548_);
v___x_2914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2914_, 0, v___x_2912_);
lean_ctor_set(v___x_2914_, 1, v___x_2913_);
v___x_2915_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__54_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__54_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__54_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2916_, 0, v___x_2914_);
lean_ctor_set(v___x_2916_, 1, v___x_2915_);
v___x_2917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2917_, 0, v___x_2916_);
lean_ctor_set(v___x_2917_, 1, v___x_2909_);
v___x_2918_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__56_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__56_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__56_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2919_, 0, v___x_2917_);
lean_ctor_set(v___x_2919_, 1, v___x_2918_);
v___x_2920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2920_, 0, v___x_2919_);
lean_ctor_set(v___x_2920_, 1, v___x_2882_);
if (lean_obj_tag(v___y_2858_) == 1)
{
lean_object* v_val_2921_; lean_object* v___x_2922_; 
v_val_2921_ = lean_ctor_get(v___y_2858_, 0);
v___x_2922_ = l_Lean_Syntax_getRange_x3f(v_val_2921_, v___x_2548_);
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_dec_ref(v___x_2909_);
lean_dec(v_val_2902_);
v___y_2788_ = v_env_2869_;
v___y_2789_ = v___y_2855_;
v___y_2790_ = v___y_2856_;
v___y_2791_ = v___y_2857_;
v___y_2792_ = v___y_2858_;
v___y_2793_ = v___y_2859_;
v___y_2794_ = v___x_2867_;
v___y_2795_ = v_val_2862_;
v_msg_2796_ = v___x_2920_;
v___y_2797_ = v___y_2860_;
v___y_2798_ = v___y_2861_;
goto v___jp_2787_;
}
else
{
uint8_t v___x_2923_; uint8_t v___x_2924_; uint8_t v___x_2925_; lean_object* v___x_2926_; uint64_t v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; 
lean_inc(v_val_2921_);
lean_dec_ref_known(v___x_2922_, 1);
v___x_2923_ = 1;
v___x_2924_ = 0;
v___x_2925_ = 2;
v___x_2926_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_2926_, 0, v___x_2903_);
lean_ctor_set_uint8(v___x_2926_, 1, v___x_2903_);
lean_ctor_set_uint8(v___x_2926_, 2, v___x_2903_);
lean_ctor_set_uint8(v___x_2926_, 3, v___x_2903_);
lean_ctor_set_uint8(v___x_2926_, 4, v___x_2903_);
lean_ctor_set_uint8(v___x_2926_, 5, v___x_2872_);
lean_ctor_set_uint8(v___x_2926_, 6, v___x_2872_);
lean_ctor_set_uint8(v___x_2926_, 7, v___x_2903_);
lean_ctor_set_uint8(v___x_2926_, 8, v___x_2872_);
lean_ctor_set_uint8(v___x_2926_, 9, v___x_2923_);
lean_ctor_set_uint8(v___x_2926_, 10, v___x_2924_);
lean_ctor_set_uint8(v___x_2926_, 11, v___x_2872_);
lean_ctor_set_uint8(v___x_2926_, 12, v___x_2872_);
lean_ctor_set_uint8(v___x_2926_, 13, v___x_2872_);
lean_ctor_set_uint8(v___x_2926_, 14, v___x_2925_);
lean_ctor_set_uint8(v___x_2926_, 15, v___x_2872_);
lean_ctor_set_uint8(v___x_2926_, 16, v___x_2872_);
lean_ctor_set_uint8(v___x_2926_, 17, v___x_2872_);
lean_ctor_set_uint8(v___x_2926_, 18, v___x_2872_);
lean_ctor_set_uint8(v___x_2926_, 19, v___x_2903_);
v___x_2927_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2926_);
v___x_2928_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2928_, 0, v___x_2926_);
lean_ctor_set_uint64(v___x_2928_, sizeof(void*)*1, v___x_2927_);
v___x_2929_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_2930_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2931_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2932_ = lean_box(0);
lean_inc_n(v___x_2533_, 2);
v___x_2933_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2933_, 0, v___x_2928_);
lean_ctor_set(v___x_2933_, 1, v___x_2533_);
lean_ctor_set(v___x_2933_, 2, v___x_2930_);
lean_ctor_set(v___x_2933_, 3, v___x_2931_);
lean_ctor_set(v___x_2933_, 4, v___x_2932_);
lean_ctor_set(v___x_2933_, 5, v___x_2670_);
lean_ctor_set(v___x_2933_, 6, v___x_2932_);
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*7, v___x_2532_);
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*7 + 1, v___x_2532_);
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*7 + 2, v___x_2532_);
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*7 + 3, v___x_2548_);
v___x_2934_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2935_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2936_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2937_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2937_, 0, v___x_2934_);
lean_ctor_set(v___x_2937_, 1, v___x_2935_);
lean_ctor_set(v___x_2937_, 2, v___x_2533_);
lean_ctor_set(v___x_2937_, 3, v___x_2929_);
lean_ctor_set(v___x_2937_, 4, v___x_2936_);
v___x_2938_ = lean_st_mk_ref(v___x_2937_);
v___x_2939_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5(v_val_2902_, v___x_2532_, v___x_2933_, v___x_2938_, v___y_2860_, v___y_2861_);
lean_dec_ref_known(v___x_2933_, 7);
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_object* v_a_2940_; lean_object* v___x_2941_; 
v_a_2940_ = lean_ctor_get(v___x_2939_, 0);
lean_inc(v_a_2940_);
lean_dec_ref_known(v___x_2939_, 1);
v___x_2941_ = lean_st_ref_get(v___x_2938_);
lean_dec(v___x_2938_);
lean_dec(v___x_2941_);
v___y_2809_ = v___y_2855_;
v___y_2810_ = v___y_2857_;
v___y_2811_ = v___y_2859_;
v___y_2812_ = v_val_2921_;
v___y_2813_ = v___x_2920_;
v___y_2814_ = v___y_2861_;
v___y_2815_ = v_env_2869_;
v___y_2816_ = v___y_2856_;
v___y_2817_ = v___y_2860_;
v___y_2818_ = v___y_2858_;
v___y_2819_ = v___x_2909_;
v___y_2820_ = v___x_2867_;
v___y_2821_ = v_val_2862_;
v_a_2822_ = v_a_2940_;
goto v___jp_2808_;
}
else
{
lean_dec(v___x_2938_);
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_object* v_a_2942_; 
v_a_2942_ = lean_ctor_get(v___x_2939_, 0);
lean_inc(v_a_2942_);
lean_dec_ref_known(v___x_2939_, 1);
v___y_2809_ = v___y_2855_;
v___y_2810_ = v___y_2857_;
v___y_2811_ = v___y_2859_;
v___y_2812_ = v_val_2921_;
v___y_2813_ = v___x_2920_;
v___y_2814_ = v___y_2861_;
v___y_2815_ = v_env_2869_;
v___y_2816_ = v___y_2856_;
v___y_2817_ = v___y_2860_;
v___y_2818_ = v___y_2858_;
v___y_2819_ = v___x_2909_;
v___y_2820_ = v___x_2867_;
v___y_2821_ = v_val_2862_;
v_a_2822_ = v_a_2942_;
goto v___jp_2808_;
}
else
{
lean_object* v_a_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2950_; 
lean_dec_ref_known(v___y_2858_, 1);
lean_dec(v_val_2921_);
lean_dec_ref_known(v___x_2920_, 2);
lean_dec_ref(v___x_2909_);
lean_dec_ref(v_env_2869_);
lean_dec_ref_known(v___y_2855_, 1);
lean_dec(v_val_2862_);
lean_dec(v___y_2859_);
lean_dec(v___y_2857_);
lean_dec(v___y_2856_);
lean_dec(v_stx_2537_);
lean_dec(v_declName_2536_);
lean_dec(v___x_2533_);
lean_dec_ref(v___f_2531_);
v_a_2943_ = lean_ctor_get(v___x_2939_, 0);
v_isSharedCheck_2950_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_2950_ == 0)
{
v___x_2945_ = v___x_2939_;
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_a_2943_);
lean_dec(v___x_2939_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2948_; 
if (v_isShared_2946_ == 0)
{
v___x_2948_ = v___x_2945_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v_a_2943_);
v___x_2948_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
return v___x_2948_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_2909_);
lean_dec(v_val_2902_);
v___y_2788_ = v_env_2869_;
v___y_2789_ = v___y_2855_;
v___y_2790_ = v___y_2856_;
v___y_2791_ = v___y_2857_;
v___y_2792_ = v___y_2858_;
v___y_2793_ = v___y_2859_;
v___y_2794_ = v___x_2867_;
v___y_2795_ = v_val_2862_;
v_msg_2796_ = v___x_2920_;
v___y_2797_ = v___y_2860_;
v___y_2798_ = v___y_2861_;
goto v___jp_2787_;
}
}
}
else
{
lean_dec(v_val_2902_);
lean_dec_ref(v___x_2882_);
v___y_2743_ = v_env_2869_;
v___y_2744_ = v___y_2855_;
v___y_2745_ = v___y_2856_;
v___y_2746_ = v___y_2857_;
v___y_2747_ = v___y_2858_;
v___y_2748_ = v___y_2859_;
v___y_2749_ = v___x_2867_;
v___y_2750_ = v_val_2862_;
v___y_2751_ = v___y_2860_;
v___y_2752_ = v___y_2861_;
goto v___jp_2742_;
}
}
}
else
{
lean_dec(v___x_2873_);
v___y_2743_ = v_env_2869_;
v___y_2744_ = v___y_2855_;
v___y_2745_ = v___y_2856_;
v___y_2746_ = v___y_2857_;
v___y_2747_ = v___y_2858_;
v___y_2748_ = v___y_2859_;
v___y_2749_ = v___x_2867_;
v___y_2750_ = v_val_2862_;
v___y_2751_ = v___y_2860_;
v___y_2752_ = v___y_2861_;
goto v___jp_2742_;
}
}
}
}
else
{
lean_object* v_a_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_2958_; 
lean_dec_ref_known(v___y_2855_, 1);
lean_dec(v___y_2859_);
lean_dec(v___y_2858_);
lean_dec(v___y_2857_);
lean_dec(v___y_2856_);
lean_dec(v_stx_2537_);
lean_dec(v_declName_2536_);
lean_dec_ref(v___x_2534_);
lean_dec(v___x_2533_);
lean_dec_ref(v___f_2531_);
v_a_2951_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_2958_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2958_ == 0)
{
v___x_2953_ = v___x_2863_;
v_isShared_2954_ = v_isSharedCheck_2958_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_a_2951_);
lean_dec(v___x_2863_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_2958_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v___x_2956_; 
if (v_isShared_2954_ == 0)
{
v___x_2956_ = v___x_2953_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v_a_2951_);
v___x_2956_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
return v___x_2956_;
}
}
}
}
else
{
lean_dec(v___y_2859_);
lean_dec(v_declName_2536_);
lean_dec_ref(v___x_2534_);
lean_dec(v___x_2533_);
lean_dec_ref(v___f_2531_);
v___y_2611_ = v___y_2855_;
v___y_2612_ = v___y_2856_;
v___y_2613_ = v___y_2857_;
v___y_2614_ = v___y_2858_;
v___y_2615_ = v___y_2860_;
v___y_2616_ = v___y_2861_;
goto v___jp_2610_;
}
}
v___jp_2959_:
{
lean_object* v___x_2967_; uint8_t v___x_2968_; 
lean_inc(v_declName_2536_);
v___x_2967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2967_, 0, v_declName_2536_);
v___x_2968_ = l_instBEqOption_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6(v_a_2966_, v___x_2967_);
lean_dec_ref_known(v___x_2967_, 1);
if (v___x_2968_ == 0)
{
v___y_2855_ = v_a_2966_;
v___y_2856_ = v___y_2961_;
v___y_2857_ = v___y_2962_;
v___y_2858_ = v___y_2963_;
v___y_2859_ = v___y_2965_;
v___y_2860_ = v___y_2960_;
v___y_2861_ = v___y_2964_;
goto v___jp_2854_;
}
else
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v_a_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2982_; 
lean_dec(v_a_2966_);
lean_dec(v___y_2965_);
lean_dec(v___y_2963_);
lean_dec(v___y_2962_);
lean_dec(v___y_2961_);
lean_dec(v_stx_2537_);
lean_dec_ref(v___x_2534_);
lean_dec(v___x_2533_);
lean_dec_ref(v___f_2531_);
v___x_2969_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__58_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__58_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__58_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2970_ = l_Lean_MessageData_ofConstName(v_declName_2536_, v___x_2548_);
v___x_2971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2971_, 0, v___x_2969_);
lean_ctor_set(v___x_2971_, 1, v___x_2970_);
v___x_2972_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__60_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__60_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__60_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2971_);
lean_ctor_set(v___x_2973_, 1, v___x_2972_);
v___x_2974_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0___redArg(v___x_2973_, v___y_2960_, v___y_2964_);
v_a_2975_ = lean_ctor_get(v___x_2974_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2974_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2977_ = v___x_2974_;
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_a_2975_);
lean_dec(v___x_2974_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2980_; 
if (v_isShared_2978_ == 0)
{
v___x_2980_ = v___x_2977_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_a_2975_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
}
}
v___jp_2983_:
{
if (lean_obj_tag(v___y_2985_) == 0)
{
lean_object* v___x_2990_; 
v___x_2990_ = lean_box(0);
v___y_2960_ = v___y_2988_;
v___y_2961_ = v_since_x3f_2987_;
v___y_2962_ = v___y_2984_;
v___y_2963_ = v___y_2985_;
v___y_2964_ = v___y_2989_;
v___y_2965_ = v___y_2986_;
v_a_2966_ = v___x_2990_;
goto v___jp_2959_;
}
else
{
lean_object* v_val_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; 
v_val_2991_ = lean_ctor_get(v___y_2985_, 0);
v___x_2992_ = lean_box(0);
lean_inc(v_val_2991_);
v___x_2993_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_val_2991_, v___x_2992_, v___y_2988_, v___y_2989_);
if (lean_obj_tag(v___x_2993_) == 0)
{
lean_object* v_a_2994_; lean_object* v___x_2995_; 
v_a_2994_ = lean_ctor_get(v___x_2993_, 0);
lean_inc(v_a_2994_);
lean_dec_ref_known(v___x_2993_, 1);
v___x_2995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2995_, 0, v_a_2994_);
v___y_2960_ = v___y_2988_;
v___y_2961_ = v_since_x3f_2987_;
v___y_2962_ = v___y_2984_;
v___y_2963_ = v___y_2985_;
v___y_2964_ = v___y_2989_;
v___y_2965_ = v___y_2986_;
v_a_2966_ = v___x_2995_;
goto v___jp_2959_;
}
else
{
lean_object* v_a_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3003_; 
lean_dec_ref_known(v___y_2985_, 1);
lean_dec(v_since_x3f_2987_);
lean_dec(v___y_2986_);
lean_dec(v___y_2984_);
lean_dec(v_stx_2537_);
lean_dec(v_declName_2536_);
lean_dec_ref(v___x_2534_);
lean_dec(v___x_2533_);
lean_dec_ref(v___f_2531_);
v_a_2996_ = lean_ctor_get(v___x_2993_, 0);
v_isSharedCheck_3003_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3003_ == 0)
{
v___x_2998_ = v___x_2993_;
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_a_2996_);
lean_dec(v___x_2993_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
lean_object* v___x_3001_; 
if (v_isShared_2999_ == 0)
{
v___x_3001_ = v___x_2998_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_a_2996_);
v___x_3001_ = v_reuseFailAlloc_3002_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
return v___x_3001_;
}
}
}
}
}
v___jp_3004_:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; uint8_t v___x_3013_; 
v___x_3011_ = lean_unsigned_to_nat(4u);
v___x_3012_ = l_Lean_Syntax_getArg(v_stx_2537_, v___x_3011_);
v___x_3013_ = l_Lean_Syntax_isNone(v___x_3012_);
if (v___x_3013_ == 0)
{
lean_object* v___x_3014_; uint8_t v___x_3015_; 
v___x_3014_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_3012_);
v___x_3015_ = l_Lean_Syntax_matchesNull(v___x_3012_, v___x_3014_);
if (v___x_3015_ == 0)
{
lean_object* v___x_3016_; lean_object* v___x_3017_; 
lean_dec(v___x_3012_);
lean_dec(v_typeChanged_x3f_3008_);
lean_dec(v___y_3007_);
lean_dec(v___y_3006_);
lean_dec(v_stx_2537_);
lean_dec(v_declName_2536_);
lean_dec_ref(v___x_2534_);
lean_dec(v___x_2533_);
lean_dec_ref(v___f_2531_);
v___x_3016_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_3017_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0___redArg(v___x_3016_, v___y_3009_, v___y_3010_);
return v___x_3017_;
}
else
{
lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3018_ = l_Lean_Syntax_getArg(v___x_3012_, v___y_3005_);
lean_dec(v___x_3012_);
v___x_3019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3019_, 0, v___x_3018_);
v___y_2984_ = v___y_3006_;
v___y_2985_ = v___y_3007_;
v___y_2986_ = v_typeChanged_x3f_3008_;
v_since_x3f_2987_ = v___x_3019_;
v___y_2988_ = v___y_3009_;
v___y_2989_ = v___y_3010_;
goto v___jp_2983_;
}
}
else
{
lean_object* v___x_3020_; 
lean_dec(v___x_3012_);
v___x_3020_ = lean_box(0);
v___y_2984_ = v___y_3006_;
v___y_2985_ = v___y_3007_;
v___y_2986_ = v_typeChanged_x3f_3008_;
v_since_x3f_2987_ = v___x_3020_;
v___y_2988_ = v___y_3009_;
v___y_2989_ = v___y_3010_;
goto v___jp_2983_;
}
}
v___jp_3021_:
{
lean_object* v___x_3026_; lean_object* v___x_3027_; uint8_t v___x_3028_; 
v___x_3026_ = lean_unsigned_to_nat(3u);
v___x_3027_ = l_Lean_Syntax_getArg(v_stx_2537_, v___x_3026_);
v___x_3028_ = l_Lean_Syntax_isNone(v___x_3027_);
if (v___x_3028_ == 0)
{
uint8_t v___x_3029_; 
lean_inc(v___x_3027_);
v___x_3029_ = l_Lean_Syntax_matchesNull(v___x_3027_, v___x_2671_);
if (v___x_3029_ == 0)
{
lean_object* v___x_3030_; lean_object* v___x_3031_; 
lean_dec(v___x_3027_);
lean_dec(v_text_x3f_3023_);
lean_dec(v___y_3022_);
lean_dec(v_stx_2537_);
lean_dec(v_declName_2536_);
lean_dec_ref(v___x_2534_);
lean_dec(v___x_2533_);
lean_dec_ref(v___f_2531_);
v___x_3030_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_3031_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0___redArg(v___x_3030_, v___y_3024_, v___y_3025_);
return v___x_3031_;
}
else
{
lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___x_3032_ = l_Lean_Syntax_getArg(v___x_3027_, v___x_2670_);
lean_dec(v___x_3027_);
v___x_3033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3033_, 0, v___x_3032_);
v___y_3005_ = v___x_3026_;
v___y_3006_ = v_text_x3f_3023_;
v___y_3007_ = v___y_3022_;
v_typeChanged_x3f_3008_ = v___x_3033_;
v___y_3009_ = v___y_3024_;
v___y_3010_ = v___y_3025_;
goto v___jp_3004_;
}
}
else
{
lean_object* v___x_3034_; 
lean_dec(v___x_3027_);
v___x_3034_ = lean_box(0);
v___y_3005_ = v___x_3026_;
v___y_3006_ = v_text_x3f_3023_;
v___y_3007_ = v___y_3022_;
v_typeChanged_x3f_3008_ = v___x_3034_;
v___y_3009_ = v___y_3024_;
v___y_3010_ = v___y_3025_;
goto v___jp_3004_;
}
}
v___jp_3035_:
{
lean_object* v___x_3039_; lean_object* v___x_3040_; uint8_t v___x_3041_; 
v___x_3039_ = lean_unsigned_to_nat(2u);
v___x_3040_ = l_Lean_Syntax_getArg(v_stx_2537_, v___x_3039_);
v___x_3041_ = l_Lean_Syntax_isNone(v___x_3040_);
if (v___x_3041_ == 0)
{
uint8_t v___x_3042_; 
lean_inc(v___x_3040_);
v___x_3042_ = l_Lean_Syntax_matchesNull(v___x_3040_, v___x_2671_);
if (v___x_3042_ == 0)
{
lean_object* v___x_3043_; lean_object* v___x_3044_; 
lean_dec(v___x_3040_);
lean_dec(v_id_x3f_3036_);
lean_dec(v_stx_2537_);
lean_dec(v_declName_2536_);
lean_dec_ref(v___x_2534_);
lean_dec(v___x_2533_);
lean_dec_ref(v___f_2531_);
v___x_3043_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_3044_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0___redArg(v___x_3043_, v___y_3037_, v___y_3038_);
return v___x_3044_;
}
else
{
lean_object* v___x_3045_; lean_object* v___x_3046_; 
v___x_3045_ = l_Lean_Syntax_getArg(v___x_3040_, v___x_2670_);
lean_dec(v___x_3040_);
v___x_3046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3046_, 0, v___x_3045_);
v___y_3022_ = v_id_x3f_3036_;
v_text_x3f_3023_ = v___x_3046_;
v___y_3024_ = v___y_3037_;
v___y_3025_ = v___y_3038_;
goto v___jp_3021_;
}
}
else
{
lean_object* v___x_3047_; 
lean_dec(v___x_3040_);
v___x_3047_ = lean_box(0);
v___y_3022_ = v_id_x3f_3036_;
v_text_x3f_3023_ = v___x_3047_;
v___y_3024_ = v___y_3037_;
v___y_3025_ = v___y_3038_;
goto v___jp_3021_;
}
}
}
v___jp_2541_:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2545_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2545_, 0, v___y_2542_);
lean_ctor_set(v___x_2545_, 1, v___y_2544_);
lean_ctor_set(v___x_2545_, 2, v___y_2543_);
v___x_2546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2545_);
return v___x_2546_;
}
v___jp_2549_:
{
if (lean_obj_tag(v___y_2551_) == 0)
{
if (v___x_2548_ == 0)
{
lean_dec(v_stx_2537_);
v___y_2542_ = v___y_2550_;
v___y_2543_ = v___y_2551_;
v___y_2544_ = v___y_2552_;
goto v___jp_2541_;
}
else
{
lean_object* v___x_2555_; 
v___x_2555_ = l_Lean_Linter_mkSinceHint(v_stx_2537_, v___y_2553_, v___y_2554_);
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_object* v_a_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
v_a_2556_ = lean_ctor_get(v___x_2555_, 0);
lean_inc(v_a_2556_);
lean_dec_ref_known(v___x_2555_, 1);
v___x_2557_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__1_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__1_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__1_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2557_);
lean_ctor_set(v___x_2558_, 1, v_a_2556_);
v___x_2559_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1(v___x_2558_, v___y_2553_, v___y_2554_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_dec_ref_known(v___x_2559_, 1);
v___y_2542_ = v___y_2550_;
v___y_2543_ = v___y_2551_;
v___y_2544_ = v___y_2552_;
goto v___jp_2541_;
}
else
{
lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2567_; 
lean_dec(v___y_2552_);
lean_dec(v___y_2550_);
v_a_2560_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2562_ = v___x_2559_;
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___x_2559_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2565_; 
if (v_isShared_2563_ == 0)
{
v___x_2565_ = v___x_2562_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_a_2560_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
return v___x_2565_;
}
}
}
}
else
{
lean_object* v_a_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2575_; 
lean_dec(v___y_2552_);
lean_dec(v___y_2550_);
v_a_2568_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2570_ = v___x_2555_;
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_a_2568_);
lean_dec(v___x_2555_);
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
}
else
{
lean_dec(v_stx_2537_);
v___y_2542_ = v___y_2550_;
v___y_2543_ = v___y_2551_;
v___y_2544_ = v___y_2552_;
goto v___jp_2541_;
}
}
v___jp_2576_:
{
if (lean_obj_tag(v___y_2578_) == 0)
{
if (v___x_2548_ == 0)
{
v___y_2550_ = v___y_2577_;
v___y_2551_ = v___y_2582_;
v___y_2552_ = v___y_2581_;
v___y_2553_ = v___y_2580_;
v___y_2554_ = v___y_2579_;
goto v___jp_2549_;
}
else
{
if (lean_obj_tag(v___y_2581_) == 0)
{
if (v___x_2548_ == 0)
{
v___y_2550_ = v___y_2577_;
v___y_2551_ = v___y_2582_;
v___y_2552_ = v___y_2581_;
v___y_2553_ = v___y_2580_;
v___y_2554_ = v___y_2579_;
goto v___jp_2549_;
}
else
{
lean_object* v___x_2583_; lean_object* v___x_2584_; 
v___x_2583_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__4_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__4_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__4_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2584_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1(v___x_2583_, v___y_2580_, v___y_2579_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_dec_ref_known(v___x_2584_, 1);
v___y_2550_ = v___y_2577_;
v___y_2551_ = v___y_2582_;
v___y_2552_ = v___y_2581_;
v___y_2553_ = v___y_2580_;
v___y_2554_ = v___y_2579_;
goto v___jp_2549_;
}
else
{
lean_object* v_a_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2592_; 
lean_dec(v___y_2582_);
lean_dec(v___y_2577_);
lean_dec(v_stx_2537_);
v_a_2585_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2587_ = v___x_2584_;
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_a_2585_);
lean_dec(v___x_2584_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___x_2590_; 
if (v_isShared_2588_ == 0)
{
v___x_2590_ = v___x_2587_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_a_2585_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
}
}
}
else
{
v___y_2550_ = v___y_2577_;
v___y_2551_ = v___y_2582_;
v___y_2552_ = v___y_2581_;
v___y_2553_ = v___y_2580_;
v___y_2554_ = v___y_2579_;
goto v___jp_2549_;
}
}
}
else
{
lean_dec_ref_known(v___y_2578_, 1);
v___y_2550_ = v___y_2577_;
v___y_2551_ = v___y_2582_;
v___y_2552_ = v___y_2581_;
v___y_2553_ = v___y_2580_;
v___y_2554_ = v___y_2579_;
goto v___jp_2549_;
}
}
v___jp_2593_:
{
if (lean_obj_tag(v___y_2595_) == 0)
{
lean_object* v___x_2600_; 
v___x_2600_ = lean_box(0);
v___y_2577_ = v___y_2594_;
v___y_2578_ = v___y_2596_;
v___y_2579_ = v___y_2597_;
v___y_2580_ = v___y_2598_;
v___y_2581_ = v___y_2599_;
v___y_2582_ = v___x_2600_;
goto v___jp_2576_;
}
else
{
lean_object* v_val_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2609_; 
v_val_2601_ = lean_ctor_get(v___y_2595_, 0);
v_isSharedCheck_2609_ = !lean_is_exclusive(v___y_2595_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2603_ = v___y_2595_;
v_isShared_2604_ = v_isSharedCheck_2609_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_val_2601_);
lean_dec(v___y_2595_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2609_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2605_; lean_object* v___x_2607_; 
v___x_2605_ = l_Lean_TSyntax_getString(v_val_2601_);
lean_dec(v_val_2601_);
if (v_isShared_2604_ == 0)
{
lean_ctor_set(v___x_2603_, 0, v___x_2605_);
v___x_2607_ = v___x_2603_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v___x_2605_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
v___y_2577_ = v___y_2594_;
v___y_2578_ = v___y_2596_;
v___y_2579_ = v___y_2597_;
v___y_2580_ = v___y_2598_;
v___y_2581_ = v___y_2599_;
v___y_2582_ = v___x_2607_;
goto v___jp_2576_;
}
}
}
}
v___jp_2610_:
{
if (lean_obj_tag(v___y_2613_) == 0)
{
lean_object* v___x_2617_; 
v___x_2617_ = lean_box(0);
v___y_2594_ = v___y_2611_;
v___y_2595_ = v___y_2612_;
v___y_2596_ = v___y_2614_;
v___y_2597_ = v___y_2616_;
v___y_2598_ = v___y_2615_;
v___y_2599_ = v___x_2617_;
goto v___jp_2593_;
}
else
{
lean_object* v_val_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2626_; 
v_val_2618_ = lean_ctor_get(v___y_2613_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___y_2613_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2620_ = v___y_2613_;
v_isShared_2621_ = v_isSharedCheck_2626_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_val_2618_);
lean_dec(v___y_2613_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2626_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2622_; lean_object* v___x_2624_; 
v___x_2622_ = l_Lean_TSyntax_getString(v_val_2618_);
lean_dec(v_val_2618_);
if (v_isShared_2621_ == 0)
{
lean_ctor_set(v___x_2620_, 0, v___x_2622_);
v___x_2624_ = v___x_2620_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v___x_2622_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
v___y_2594_ = v___y_2611_;
v___y_2595_ = v___y_2612_;
v___y_2596_ = v___y_2614_;
v___y_2597_ = v___y_2616_;
v___y_2598_ = v___y_2615_;
v___y_2599_ = v___x_2624_;
goto v___jp_2593_;
}
}
}
}
v___jp_2627_:
{
lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; 
v___x_2637_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2638_ = l_Lean_ConstantInfo_type(v___y_2632_);
lean_dec_ref(v___y_2632_);
v___x_2639_ = l_Lean_indentExpr(v___x_2638_);
v___x_2640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2640_, 0, v___x_2637_);
lean_ctor_set(v___x_2640_, 1, v___x_2639_);
v___x_2641_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2642_, 0, v___x_2640_);
lean_ctor_set(v___x_2642_, 1, v___x_2641_);
v___x_2643_ = l_Lean_ConstantInfo_type(v___y_2633_);
lean_dec_ref(v___y_2633_);
v___x_2644_ = l_Lean_indentExpr(v___x_2643_);
v___x_2645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2645_, 0, v___x_2642_);
lean_ctor_set(v___x_2645_, 1, v___x_2644_);
v___x_2646_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__10_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__10_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__10_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2647_, 0, v___x_2645_);
lean_ctor_set(v___x_2647_, 1, v___x_2646_);
v___x_2648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2648_, 0, v___x_2647_);
lean_ctor_set(v___x_2648_, 1, v_hint_2634_);
v___x_2649_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1(v___x_2648_, v___y_2635_, v___y_2636_);
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_dec_ref_known(v___x_2649_, 1);
v___y_2611_ = v___y_2628_;
v___y_2612_ = v___y_2629_;
v___y_2613_ = v___y_2630_;
v___y_2614_ = v___y_2631_;
v___y_2615_ = v___y_2635_;
v___y_2616_ = v___y_2636_;
goto v___jp_2610_;
}
else
{
lean_object* v_a_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2657_; 
lean_dec(v___y_2631_);
lean_dec(v___y_2630_);
lean_dec(v___y_2629_);
lean_dec(v___y_2628_);
lean_dec(v_stx_2537_);
v_a_2650_ = lean_ctor_get(v___x_2649_, 0);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2652_ = v___x_2649_;
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_a_2650_);
lean_dec(v___x_2649_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v___x_2655_; 
if (v_isShared_2653_ == 0)
{
v___x_2655_ = v___x_2652_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_a_2650_);
v___x_2655_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
return v___x_2655_;
}
}
}
}
v___jp_2658_:
{
lean_object* v___x_2667_; 
v___x_2667_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__14_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__14_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__14_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___y_2628_ = v___y_2659_;
v___y_2629_ = v___y_2661_;
v___y_2630_ = v___y_2663_;
v___y_2631_ = v___y_2664_;
v___y_2632_ = v___y_2665_;
v___y_2633_ = v___y_2666_;
v_hint_2634_ = v___x_2667_;
v___y_2635_ = v___y_2662_;
v___y_2636_ = v___y_2660_;
goto v___jp_2627_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2____boxed(lean_object* v___x_3056_, lean_object* v___x_3057_, lean_object* v___f_3058_, lean_object* v___x_3059_, lean_object* v___x_3060_, lean_object* v___x_3061_, lean_object* v_a_3062_, lean_object* v_declName_3063_, lean_object* v_stx_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_){
_start:
{
uint8_t v___x_46883__boxed_3068_; lean_object* v_res_3069_; 
v___x_46883__boxed_3068_ = lean_unbox(v___x_3059_);
v_res_3069_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(v___x_3056_, v___x_3057_, v___f_3058_, v___x_46883__boxed_3068_, v___x_3060_, v___x_3061_, v_a_3062_, v_declName_3063_, v_stx_3064_, v___y_3065_, v___y_3066_);
lean_dec(v___y_3066_);
lean_dec_ref(v___y_3065_);
lean_dec_ref(v_a_3062_);
return v_res_3069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3087_; lean_object* v___f_3088_; lean_object* v___f_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; uint8_t v___x_3094_; lean_object* v___x_3095_; 
v___f_3087_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___f_3088_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___f_3089_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_3090_ = lean_box(1);
v___x_3091_ = ((lean_object*)(l_Lean_Linter_instInhabitedDeprecationEntry_default));
v___x_3092_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_));
v___x_3093_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_3094_ = 0;
v___x_3095_ = l_Lean_registerParametricAttributeExt___redArg(v___x_3093_, v___x_3094_, v___f_3087_, v___x_3094_);
if (lean_obj_tag(v___x_3095_) == 0)
{
lean_object* v_a_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___f_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; 
v_a_3096_ = lean_ctor_get(v___x_3095_, 0);
lean_inc_n(v_a_3096_, 2);
lean_dec_ref_known(v___x_3095_, 1);
v___x_3097_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_));
v___x_3098_ = lean_box(v___x_3094_);
v___f_3099_ = lean_alloc_closure((void*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2____boxed), 12, 7);
lean_closure_set(v___f_3099_, 0, v___x_3092_);
lean_closure_set(v___f_3099_, 1, v___x_3097_);
lean_closure_set(v___f_3099_, 2, v___f_3088_);
lean_closure_set(v___f_3099_, 3, v___x_3098_);
lean_closure_set(v___f_3099_, 4, v___x_3090_);
lean_closure_set(v___f_3099_, 5, v___x_3091_);
lean_closure_set(v___f_3099_, 6, v_a_3096_);
v___x_3100_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_3101_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3101_, 0, v___x_3100_);
lean_ctor_set(v___x_3101_, 1, v___f_3099_);
lean_ctor_set(v___x_3101_, 2, v___f_3089_);
lean_ctor_set(v___x_3101_, 3, v___f_3087_);
lean_ctor_set_uint8(v___x_3101_, sizeof(void*)*4, v___x_3094_);
v___x_3102_ = l_Lean_registerParametricAttributeForExt___redArg(v___x_3101_, v_a_3096_);
return v___x_3102_;
}
else
{
lean_object* v_a_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3110_; 
v_a_3103_ = lean_ctor_get(v___x_3095_, 0);
v_isSharedCheck_3110_ = !lean_is_exclusive(v___x_3095_);
if (v_isSharedCheck_3110_ == 0)
{
v___x_3105_ = v___x_3095_;
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_a_3103_);
lean_dec(v___x_3095_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3108_; 
if (v_isShared_3106_ == 0)
{
v___x_3108_ = v___x_3105_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_a_3103_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
return v___x_3108_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2____boxed(lean_object* v_a_3111_){
_start:
{
lean_object* v_res_3112_; 
v_res_3112_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_();
return v_res_3112_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_3113_, lean_object* v_msg_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_){
_start:
{
lean_object* v___x_3118_; 
v___x_3118_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0___redArg(v_msg_3114_, v___y_3115_, v___y_3116_);
return v___x_3118_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_3119_, lean_object* v_msg_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_){
_start:
{
lean_object* v_res_3124_; 
v_res_3124_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0(v_00_u03b1_3119_, v_msg_3120_, v___y_3121_, v___y_3122_);
lean_dec(v___y_3122_);
lean_dec_ref(v___y_3121_);
return v_res_3124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3_spec__8(lean_object* v_o_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_){
_start:
{
lean_object* v___x_3129_; 
v___x_3129_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3_spec__8___redArg(v_o_3125_, v___y_3127_);
return v___x_3129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3_spec__8___boxed(lean_object* v_o_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_){
_start:
{
lean_object* v_res_3134_; 
v_res_3134_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3_spec__8(v_o_3130_, v___y_3131_, v___y_3132_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
return v_res_3134_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6(lean_object* v_00_u03b2_3135_, lean_object* v_m_3136_, lean_object* v_a_3137_){
_start:
{
lean_object* v___x_3138_; 
v___x_3138_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6___redArg(v_m_3136_, v_a_3137_);
return v___x_3138_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6___boxed(lean_object* v_00_u03b2_3139_, lean_object* v_m_3140_, lean_object* v_a_3141_){
_start:
{
lean_object* v_res_3142_; 
v_res_3142_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6(v_00_u03b2_3139_, v_m_3140_, v_a_3141_);
lean_dec(v_a_3141_);
lean_dec_ref(v_m_3140_);
return v_res_3142_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8(lean_object* v_00_u03b2_3143_, lean_object* v_x_3144_, lean_object* v_x_3145_){
_start:
{
uint8_t v___x_3146_; 
v___x_3146_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg(v_x_3144_, v_x_3145_);
return v___x_3146_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_3147_, lean_object* v_x_3148_, lean_object* v_x_3149_){
_start:
{
uint8_t v_res_3150_; lean_object* v_r_3151_; 
v_res_3150_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8(v_00_u03b2_3147_, v_x_3148_, v_x_3149_);
lean_dec_ref(v_x_3149_);
lean_dec_ref(v_x_3148_);
v_r_3151_ = lean_box(v_res_3150_);
return v_r_3151_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6_spec__12(lean_object* v_00_u03b2_3152_, lean_object* v_a_3153_, lean_object* v_x_3154_){
_start:
{
lean_object* v___x_3155_; 
v___x_3155_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg(v_a_3153_, v_x_3154_);
return v___x_3155_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6_spec__12___boxed(lean_object* v_00_u03b2_3156_, lean_object* v_a_3157_, lean_object* v_x_3158_){
_start:
{
lean_object* v_res_3159_; 
v_res_3159_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6_spec__12(v_00_u03b2_3156_, v_a_3157_, v_x_3158_);
lean_dec(v_x_3158_);
lean_dec(v_a_3157_);
return v_res_3159_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__17(lean_object* v_00_u03b4_3160_, lean_object* v_t_3161_, lean_object* v_k_3162_){
_start:
{
lean_object* v___x_3163_; 
v___x_3163_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__17___redArg(v_t_3161_, v_k_3162_);
return v___x_3163_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__17___boxed(lean_object* v_00_u03b4_3164_, lean_object* v_t_3165_, lean_object* v_k_3166_){
_start:
{
lean_object* v_res_3167_; 
v_res_3167_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__17(v_00_u03b4_3164_, v_t_3165_, v_k_3166_);
lean_dec(v_k_3166_);
lean_dec(v_t_3165_);
return v_res_3167_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12(lean_object* v_00_u03b2_3168_, lean_object* v_x_3169_, size_t v_x_3170_, lean_object* v_x_3171_){
_start:
{
uint8_t v___x_3172_; 
v___x_3172_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12___redArg(v_x_3169_, v_x_3170_, v_x_3171_);
return v___x_3172_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12___boxed(lean_object* v_00_u03b2_3173_, lean_object* v_x_3174_, lean_object* v_x_3175_, lean_object* v_x_3176_){
_start:
{
size_t v_x_48181__boxed_3177_; uint8_t v_res_3178_; lean_object* v_r_3179_; 
v_x_48181__boxed_3177_ = lean_unbox_usize(v_x_3175_);
lean_dec(v_x_3175_);
v_res_3178_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12(v_00_u03b2_3173_, v_x_3174_, v_x_48181__boxed_3177_, v_x_3176_);
lean_dec_ref(v_x_3176_);
lean_dec_ref(v_x_3174_);
v_r_3179_ = lean_box(v_res_3178_);
return v_r_3179_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20(lean_object* v_givenName_3180_, uint8_t v_skipAuxDecl_3181_, lean_object* v_auxDeclToFullName_3182_, lean_object* v___x_3183_, lean_object* v_givenNameView_3184_, lean_object* v_as_3185_, lean_object* v_i_3186_, lean_object* v_a_3187_){
_start:
{
lean_object* v___x_3188_; 
v___x_3188_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg(v_givenName_3180_, v_skipAuxDecl_3181_, v_auxDeclToFullName_3182_, v___x_3183_, v_givenNameView_3184_, v_as_3185_, v_i_3186_);
return v___x_3188_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___boxed(lean_object* v_givenName_3189_, lean_object* v_skipAuxDecl_3190_, lean_object* v_auxDeclToFullName_3191_, lean_object* v___x_3192_, lean_object* v_givenNameView_3193_, lean_object* v_as_3194_, lean_object* v_i_3195_, lean_object* v_a_3196_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3197_; lean_object* v_res_3198_; 
v_skipAuxDecl_boxed_3197_ = lean_unbox(v_skipAuxDecl_3190_);
v_res_3198_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20(v_givenName_3189_, v_skipAuxDecl_boxed_3197_, v_auxDeclToFullName_3191_, v___x_3192_, v_givenNameView_3193_, v_as_3194_, v_i_3195_, v_a_3196_);
lean_dec_ref(v_as_3194_);
lean_dec(v_auxDeclToFullName_3191_);
lean_dec(v_givenName_3189_);
return v_res_3198_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23(lean_object* v_localDecl_x3f_3199_, lean_object* v_givenName_3200_, lean_object* v_as_3201_, lean_object* v_i_3202_, lean_object* v_a_3203_){
_start:
{
lean_object* v___x_3204_; 
v___x_3204_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___redArg(v_localDecl_x3f_3199_, v_givenName_3200_, v_as_3201_, v_i_3202_);
return v___x_3204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___boxed(lean_object* v_localDecl_x3f_3205_, lean_object* v_givenName_3206_, lean_object* v_as_3207_, lean_object* v_i_3208_, lean_object* v_a_3209_){
_start:
{
lean_object* v_res_3210_; 
v_res_3210_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23(v_localDecl_x3f_3205_, v_givenName_3206_, v_as_3207_, v_i_3208_, v_a_3209_);
lean_dec_ref(v_as_3207_);
lean_dec(v_givenName_3206_);
lean_dec(v_localDecl_x3f_3205_);
return v_res_3210_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30(lean_object* v_n_u2080_3211_, lean_object* v_filter_3212_, lean_object* v_view_x3f_3213_, lean_object* v_as_3214_, lean_object* v_as_x27_3215_, lean_object* v_b_3216_, lean_object* v_a_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_){
_start:
{
lean_object* v___x_3223_; 
v___x_3223_ = l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30___redArg(v_n_u2080_3211_, v_filter_3212_, v_view_x3f_3213_, v_as_x27_3215_, v_b_3216_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_);
return v___x_3223_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30___boxed(lean_object* v_n_u2080_3224_, lean_object* v_filter_3225_, lean_object* v_view_x3f_3226_, lean_object* v_as_3227_, lean_object* v_as_x27_3228_, lean_object* v_b_3229_, lean_object* v_a_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_){
_start:
{
lean_object* v_res_3236_; 
v_res_3236_ = l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30(v_n_u2080_3224_, v_filter_3225_, v_view_x3f_3226_, v_as_3227_, v_as_x27_3228_, v_b_3229_, v_a_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_);
lean_dec(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
lean_dec(v_as_x27_3228_);
lean_dec(v_as_3227_);
lean_dec(v_n_u2080_3224_);
return v_res_3236_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17(lean_object* v_00_u03b2_3237_, lean_object* v_keys_3238_, lean_object* v_vals_3239_, lean_object* v_heq_3240_, lean_object* v_i_3241_, lean_object* v_k_3242_){
_start:
{
uint8_t v___x_3243_; 
v___x_3243_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17___redArg(v_keys_3238_, v_i_3241_, v_k_3242_);
return v___x_3243_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17___boxed(lean_object* v_00_u03b2_3244_, lean_object* v_keys_3245_, lean_object* v_vals_3246_, lean_object* v_heq_3247_, lean_object* v_i_3248_, lean_object* v_k_3249_){
_start:
{
uint8_t v_res_3250_; lean_object* v_r_3251_; 
v_res_3250_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17(v_00_u03b2_3244_, v_keys_3245_, v_vals_3246_, v_heq_3247_, v_i_3248_, v_k_3249_);
lean_dec_ref(v_k_3249_);
lean_dec_ref(v_vals_3246_);
lean_dec_ref(v_keys_3245_);
v_r_3251_ = lean_box(v_res_3250_);
return v_r_3251_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24(lean_object* v_givenName_3252_, uint8_t v_skipAuxDecl_3253_, lean_object* v_auxDeclToFullName_3254_, lean_object* v___x_3255_, lean_object* v_givenNameView_3256_, lean_object* v_as_3257_, lean_object* v_i_3258_, lean_object* v_a_3259_){
_start:
{
lean_object* v___x_3260_; 
v___x_3260_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24___redArg(v_givenName_3252_, v_skipAuxDecl_3253_, v_auxDeclToFullName_3254_, v___x_3255_, v_givenNameView_3256_, v_as_3257_, v_i_3258_);
return v___x_3260_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24___boxed(lean_object* v_givenName_3261_, lean_object* v_skipAuxDecl_3262_, lean_object* v_auxDeclToFullName_3263_, lean_object* v___x_3264_, lean_object* v_givenNameView_3265_, lean_object* v_as_3266_, lean_object* v_i_3267_, lean_object* v_a_3268_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3269_; lean_object* v_res_3270_; 
v_skipAuxDecl_boxed_3269_ = lean_unbox(v_skipAuxDecl_3262_);
v_res_3270_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24(v_givenName_3261_, v_skipAuxDecl_boxed_3269_, v_auxDeclToFullName_3263_, v___x_3264_, v_givenNameView_3265_, v_as_3266_, v_i_3267_, v_a_3268_);
lean_dec_ref(v_as_3266_);
lean_dec(v_auxDeclToFullName_3263_);
lean_dec(v_givenName_3261_);
return v_res_3270_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28(lean_object* v_localDecl_x3f_3271_, lean_object* v_givenName_3272_, lean_object* v_as_3273_, lean_object* v_i_3274_, lean_object* v_a_3275_){
_start:
{
lean_object* v___x_3276_; 
v___x_3276_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28___redArg(v_localDecl_x3f_3271_, v_givenName_3272_, v_as_3273_, v_i_3274_);
return v___x_3276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28___boxed(lean_object* v_localDecl_x3f_3277_, lean_object* v_givenName_3278_, lean_object* v_as_3279_, lean_object* v_i_3280_, lean_object* v_a_3281_){
_start:
{
lean_object* v_res_3282_; 
v_res_3282_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28(v_localDecl_x3f_3277_, v_givenName_3278_, v_as_3279_, v_i_3280_, v_a_3281_);
lean_dec_ref(v_as_3279_);
lean_dec(v_givenName_3278_);
lean_dec(v_localDecl_x3f_3277_);
return v_res_3282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37(lean_object* v_opt_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_){
_start:
{
lean_object* v___x_3289_; 
v___x_3289_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37___redArg(v_opt_3283_, v___y_3286_);
return v___x_3289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37___boxed(lean_object* v_opt_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_){
_start:
{
lean_object* v_res_3296_; 
v_res_3296_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37(v_opt_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_);
lean_dec(v___y_3294_);
lean_dec_ref(v___y_3293_);
lean_dec(v___y_3292_);
lean_dec_ref(v___y_3291_);
lean_dec_ref(v_opt_3290_);
return v_res_3296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43(lean_object* v_opt_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_){
_start:
{
lean_object* v___x_3303_; 
v___x_3303_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43___redArg(v_opt_3297_, v___y_3300_);
return v___x_3303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43___boxed(lean_object* v_opt_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_){
_start:
{
lean_object* v_res_3310_; 
v_res_3310_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43(v_opt_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_);
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
v___x_3359_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
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
LEAN_EXPORT uint8_t l_List_beq___at___00List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0(lean_object* v_x_3379_, lean_object* v_x_3380_){
_start:
{
if (lean_obj_tag(v_x_3379_) == 0)
{
if (lean_obj_tag(v_x_3380_) == 0)
{
uint8_t v___x_3381_; 
v___x_3381_ = 1;
return v___x_3381_;
}
else
{
uint8_t v___x_3382_; 
v___x_3382_ = 0;
return v___x_3382_;
}
}
else
{
if (lean_obj_tag(v_x_3380_) == 0)
{
uint8_t v___x_3383_; 
v___x_3383_ = 0;
return v___x_3383_;
}
else
{
lean_object* v_head_3384_; lean_object* v_tail_3385_; lean_object* v_head_3386_; lean_object* v_tail_3387_; uint8_t v___x_3388_; 
v_head_3384_ = lean_ctor_get(v_x_3379_, 0);
v_tail_3385_ = lean_ctor_get(v_x_3379_, 1);
v_head_3386_ = lean_ctor_get(v_x_3380_, 0);
v_tail_3387_ = lean_ctor_get(v_x_3380_, 1);
v___x_3388_ = lean_string_dec_eq(v_head_3384_, v_head_3386_);
if (v___x_3388_ == 0)
{
return v___x_3388_;
}
else
{
v_x_3379_ = v_tail_3385_;
v_x_3380_ = v_tail_3387_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0___boxed(lean_object* v_x_3390_, lean_object* v_x_3391_){
_start:
{
uint8_t v_res_3392_; lean_object* v_r_3393_; 
v_res_3392_ = l_List_beq___at___00List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0(v_x_3390_, v_x_3391_);
lean_dec(v_x_3391_);
lean_dec(v_x_3390_);
v_r_3393_ = lean_box(v_res_3392_);
return v_r_3393_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0(lean_object* v_x_3394_, lean_object* v_x_3395_){
_start:
{
if (lean_obj_tag(v_x_3394_) == 0)
{
if (lean_obj_tag(v_x_3395_) == 0)
{
uint8_t v___x_3396_; 
v___x_3396_ = 1;
return v___x_3396_;
}
else
{
uint8_t v___x_3397_; 
v___x_3397_ = 0;
return v___x_3397_;
}
}
else
{
if (lean_obj_tag(v_x_3395_) == 0)
{
uint8_t v___x_3398_; 
v___x_3398_ = 0;
return v___x_3398_;
}
else
{
lean_object* v_head_3399_; lean_object* v_tail_3400_; lean_object* v_head_3401_; lean_object* v_tail_3402_; uint8_t v___y_3404_; lean_object* v_fst_3406_; lean_object* v_snd_3407_; lean_object* v_fst_3408_; lean_object* v_snd_3409_; uint8_t v___x_3410_; 
v_head_3399_ = lean_ctor_get(v_x_3394_, 0);
v_tail_3400_ = lean_ctor_get(v_x_3394_, 1);
v_head_3401_ = lean_ctor_get(v_x_3395_, 0);
v_tail_3402_ = lean_ctor_get(v_x_3395_, 1);
v_fst_3406_ = lean_ctor_get(v_head_3399_, 0);
v_snd_3407_ = lean_ctor_get(v_head_3399_, 1);
v_fst_3408_ = lean_ctor_get(v_head_3401_, 0);
v_snd_3409_ = lean_ctor_get(v_head_3401_, 1);
v___x_3410_ = lean_name_eq(v_fst_3406_, v_fst_3408_);
if (v___x_3410_ == 0)
{
v___y_3404_ = v___x_3410_;
goto v___jp_3403_;
}
else
{
uint8_t v___x_3411_; 
v___x_3411_ = l_List_beq___at___00List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0(v_snd_3407_, v_snd_3409_);
v___y_3404_ = v___x_3411_;
goto v___jp_3403_;
}
v___jp_3403_:
{
if (v___y_3404_ == 0)
{
return v___y_3404_;
}
else
{
v_x_3394_ = v_tail_3400_;
v_x_3395_ = v_tail_3402_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0___boxed(lean_object* v_x_3412_, lean_object* v_x_3413_){
_start:
{
uint8_t v_res_3414_; lean_object* v_r_3415_; 
v_res_3414_ = l_List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0(v_x_3412_, v_x_3413_);
lean_dec(v_x_3413_);
lean_dec(v_x_3412_);
v_r_3415_ = lean_box(v_res_3414_);
return v_r_3415_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__1(void){
_start:
{
lean_object* v___x_3417_; lean_object* v___x_3418_; 
v___x_3417_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__0));
v___x_3418_ = l_Lean_stringToMessageData(v___x_3417_);
return v___x_3418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f(lean_object* v_declName_3419_, lean_object* v_newName_3420_, lean_object* v_a_3421_, lean_object* v_a_3422_, lean_object* v_a_3423_, lean_object* v_a_3424_){
_start:
{
lean_object* v_ref_3426_; 
v_ref_3426_ = lean_ctor_get(v_a_3423_, 2);
if (lean_obj_tag(v_ref_3426_) == 3)
{
lean_object* v_val_3427_; uint8_t v___x_3428_; 
v_val_3427_ = lean_ctor_get(v_ref_3426_, 2);
v___x_3428_ = l_Lean_Name_hasMacroScopes(v_val_3427_);
if (v___x_3428_ == 0)
{
uint8_t v___x_3429_; lean_object* v___x_3507_; 
v___x_3429_ = 1;
v___x_3507_ = l_Lean_Syntax_getRange_x3f(v_ref_3426_, v___x_3429_);
if (lean_obj_tag(v___x_3507_) == 0)
{
if (v___x_3428_ == 0)
{
lean_object* v___x_3508_; lean_object* v___x_3509_; 
lean_dec(v_newName_3420_);
lean_dec(v_declName_3419_);
v___x_3508_ = lean_box(0);
v___x_3509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3509_, 0, v___x_3508_);
return v___x_3509_;
}
else
{
goto v___jp_3430_;
}
}
else
{
lean_dec_ref_known(v___x_3507_, 1);
goto v___jp_3430_;
}
v___jp_3430_:
{
lean_object* v___x_3431_; 
lean_inc(v_val_3427_);
v___x_3431_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26(v_val_3427_, v___x_3429_, v_a_3421_, v_a_3422_, v_a_3423_, v_a_3424_);
if (lean_obj_tag(v___x_3431_) == 0)
{
lean_object* v_a_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3498_; 
v_a_3432_ = lean_ctor_get(v___x_3431_, 0);
v_isSharedCheck_3498_ = !lean_is_exclusive(v___x_3431_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3434_ = v___x_3431_;
v_isShared_3435_ = v_isSharedCheck_3498_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_a_3432_);
lean_dec(v___x_3431_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3498_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; uint8_t v___x_3439_; 
v___x_3436_ = lean_box(0);
v___x_3437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3437_, 0, v_declName_3419_);
lean_ctor_set(v___x_3437_, 1, v___x_3436_);
v___x_3438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3438_, 0, v___x_3437_);
lean_ctor_set(v___x_3438_, 1, v___x_3436_);
v___x_3439_ = l_List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0(v_a_3432_, v___x_3438_);
lean_dec_ref_known(v___x_3438_, 2);
lean_dec(v_a_3432_);
if (v___x_3439_ == 0)
{
lean_object* v___x_3440_; lean_object* v___x_3442_; 
lean_dec(v_newName_3420_);
v___x_3440_ = lean_box(0);
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 0, v___x_3440_);
v___x_3442_ = v___x_3434_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v___x_3440_);
v___x_3442_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
return v___x_3442_;
}
}
else
{
lean_object* v___x_3444_; 
lean_del_object(v___x_3434_);
v___x_3444_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5(v_newName_3420_, v___x_3428_, v_a_3421_, v_a_3422_, v_a_3423_, v_a_3424_);
if (lean_obj_tag(v___x_3444_) == 0)
{
lean_object* v_a_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3489_; 
v_a_3445_ = lean_ctor_get(v___x_3444_, 0);
v_isSharedCheck_3489_ = !lean_is_exclusive(v___x_3444_);
if (v_isSharedCheck_3489_ == 0)
{
v___x_3447_ = v___x_3444_;
v_isShared_3448_ = v_isSharedCheck_3489_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_a_3445_);
lean_dec(v___x_3444_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3489_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
if (lean_obj_tag(v_a_3445_) == 1)
{
lean_object* v_val_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3484_; 
lean_del_object(v___x_3447_);
v_val_3449_ = lean_ctor_get(v_a_3445_, 0);
v_isSharedCheck_3484_ = !lean_is_exclusive(v_a_3445_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3451_ = v_a_3445_;
v_isShared_3452_ = v_isSharedCheck_3484_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_val_3449_);
lean_dec(v_a_3445_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3484_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; uint8_t v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3464_; 
v___x_3453_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__1, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__1_once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__1);
v___x_3454_ = l_Lean_Name_toString(v_val_3449_, v___x_3429_);
v___x_3455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3455_, 0, v___x_3454_);
v___x_3456_ = lean_box(0);
v___x_3457_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3455_);
lean_ctor_set(v___x_3457_, 1, v___x_3456_);
lean_ctor_set(v___x_3457_, 2, v___x_3456_);
lean_ctor_set(v___x_3457_, 3, v___x_3456_);
lean_ctor_set(v___x_3457_, 4, v___x_3456_);
lean_ctor_set(v___x_3457_, 5, v___x_3456_);
v___x_3458_ = 0;
v___x_3459_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3459_, 0, v___x_3457_);
lean_ctor_set(v___x_3459_, 1, v___x_3456_);
lean_ctor_set(v___x_3459_, 2, v___x_3456_);
lean_ctor_set_uint8(v___x_3459_, sizeof(void*)*3, v___x_3458_);
v___x_3460_ = lean_unsigned_to_nat(1u);
v___x_3461_ = lean_mk_empty_array_with_capacity(v___x_3460_);
v___x_3462_ = lean_array_push(v___x_3461_, v___x_3459_);
lean_inc_ref(v_ref_3426_);
if (v_isShared_3452_ == 0)
{
lean_ctor_set(v___x_3451_, 0, v_ref_3426_);
v___x_3464_ = v___x_3451_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v_ref_3426_);
v___x_3464_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
lean_object* v___x_3465_; 
v___x_3465_ = l_Lean_MessageData_hint(v___x_3453_, v___x_3462_, v___x_3464_, v___x_3456_, v___x_3428_, v_a_3423_, v_a_3424_);
lean_dec_ref(v___x_3462_);
if (lean_obj_tag(v___x_3465_) == 0)
{
lean_object* v_a_3466_; lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3474_; 
v_a_3466_ = lean_ctor_get(v___x_3465_, 0);
v_isSharedCheck_3474_ = !lean_is_exclusive(v___x_3465_);
if (v_isSharedCheck_3474_ == 0)
{
v___x_3468_ = v___x_3465_;
v_isShared_3469_ = v_isSharedCheck_3474_;
goto v_resetjp_3467_;
}
else
{
lean_inc(v_a_3466_);
lean_dec(v___x_3465_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3474_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
lean_object* v___x_3470_; lean_object* v___x_3472_; 
v___x_3470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3470_, 0, v_a_3466_);
if (v_isShared_3469_ == 0)
{
lean_ctor_set(v___x_3468_, 0, v___x_3470_);
v___x_3472_ = v___x_3468_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v___x_3470_);
v___x_3472_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
return v___x_3472_;
}
}
}
else
{
lean_object* v_a_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3482_; 
v_a_3475_ = lean_ctor_get(v___x_3465_, 0);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3465_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3477_ = v___x_3465_;
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_a_3475_);
lean_dec(v___x_3465_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
lean_object* v___x_3480_; 
if (v_isShared_3478_ == 0)
{
v___x_3480_ = v___x_3477_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v_a_3475_);
v___x_3480_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
return v___x_3480_;
}
}
}
}
}
}
else
{
lean_object* v___x_3485_; lean_object* v___x_3487_; 
lean_dec(v_a_3445_);
v___x_3485_ = lean_box(0);
if (v_isShared_3448_ == 0)
{
lean_ctor_set(v___x_3447_, 0, v___x_3485_);
v___x_3487_ = v___x_3447_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v___x_3485_);
v___x_3487_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3486_;
}
v_reusejp_3486_:
{
return v___x_3487_;
}
}
}
}
else
{
lean_object* v_a_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3497_; 
v_a_3490_ = lean_ctor_get(v___x_3444_, 0);
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3444_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_3492_ = v___x_3444_;
v_isShared_3493_ = v_isSharedCheck_3497_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_a_3490_);
lean_dec(v___x_3444_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3497_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
lean_object* v___x_3495_; 
if (v_isShared_3493_ == 0)
{
v___x_3495_ = v___x_3492_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v_a_3490_);
v___x_3495_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
return v___x_3495_;
}
}
}
}
}
}
else
{
lean_object* v_a_3499_; lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3506_; 
lean_dec(v_newName_3420_);
lean_dec(v_declName_3419_);
v_a_3499_ = lean_ctor_get(v___x_3431_, 0);
v_isSharedCheck_3506_ = !lean_is_exclusive(v___x_3431_);
if (v_isSharedCheck_3506_ == 0)
{
v___x_3501_ = v___x_3431_;
v_isShared_3502_ = v_isSharedCheck_3506_;
goto v_resetjp_3500_;
}
else
{
lean_inc(v_a_3499_);
lean_dec(v___x_3431_);
v___x_3501_ = lean_box(0);
v_isShared_3502_ = v_isSharedCheck_3506_;
goto v_resetjp_3500_;
}
v_resetjp_3500_:
{
lean_object* v___x_3504_; 
if (v_isShared_3502_ == 0)
{
v___x_3504_ = v___x_3501_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v_a_3499_);
v___x_3504_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
return v___x_3504_;
}
}
}
}
}
else
{
lean_object* v___x_3510_; lean_object* v___x_3511_; 
lean_dec(v_newName_3420_);
lean_dec(v_declName_3419_);
v___x_3510_ = lean_box(0);
v___x_3511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3511_, 0, v___x_3510_);
return v___x_3511_;
}
}
else
{
lean_object* v___x_3512_; lean_object* v___x_3513_; 
lean_dec(v_newName_3420_);
lean_dec(v_declName_3419_);
v___x_3512_ = lean_box(0);
v___x_3513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3513_, 0, v___x_3512_);
return v___x_3513_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___boxed(lean_object* v_declName_3514_, lean_object* v_newName_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_){
_start:
{
lean_object* v_res_3521_; 
v_res_3521_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f(v_declName_3514_, v_newName_3515_, v_a_3516_, v_a_3517_, v_a_3518_, v_a_3519_);
lean_dec(v_a_3519_);
lean_dec_ref(v_a_3518_);
lean_dec(v_a_3517_);
lean_dec_ref(v_a_3516_);
return v_res_3521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(lean_object* v_o_3522_, lean_object* v___y_3523_){
_start:
{
lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v_env_3527_; lean_object* v___x_3528_; lean_object* v_toEnvExtension_3529_; lean_object* v_asyncMode_3530_; lean_object* v___x_3531_; uint8_t v___x_3532_; lean_object* v___x_3533_; lean_object* v_merged_3534_; lean_object* v___x_3536_; uint8_t v_isShared_3537_; uint8_t v_isSharedCheck_3542_; 
v___x_3525_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_3526_ = lean_st_ref_get(v___y_3523_);
v_env_3527_ = lean_ctor_get(v___x_3526_, 0);
lean_inc_ref(v_env_3527_);
lean_dec(v___x_3526_);
v___x_3528_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_3529_ = lean_ctor_get(v___x_3528_, 0);
v_asyncMode_3530_ = lean_ctor_get(v_toEnvExtension_3529_, 2);
v___x_3531_ = lean_box(0);
v___x_3532_ = 0;
v___x_3533_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3525_, v___x_3528_, v_env_3527_, v_asyncMode_3530_, v___x_3531_, v___x_3532_);
v_merged_3534_ = lean_ctor_get(v___x_3533_, 0);
v_isSharedCheck_3542_ = !lean_is_exclusive(v___x_3533_);
if (v_isSharedCheck_3542_ == 0)
{
lean_object* v_unused_3543_; 
v_unused_3543_ = lean_ctor_get(v___x_3533_, 1);
lean_dec(v_unused_3543_);
v___x_3536_ = v___x_3533_;
v_isShared_3537_ = v_isSharedCheck_3542_;
goto v_resetjp_3535_;
}
else
{
lean_inc(v_merged_3534_);
lean_dec(v___x_3533_);
v___x_3536_ = lean_box(0);
v_isShared_3537_ = v_isSharedCheck_3542_;
goto v_resetjp_3535_;
}
v_resetjp_3535_:
{
lean_object* v___x_3539_; 
if (v_isShared_3537_ == 0)
{
lean_ctor_set(v___x_3536_, 1, v_merged_3534_);
lean_ctor_set(v___x_3536_, 0, v_o_3522_);
v___x_3539_ = v___x_3536_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v_o_3522_);
lean_ctor_set(v_reuseFailAlloc_3541_, 1, v_merged_3534_);
v___x_3539_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
lean_object* v___x_3540_; 
v___x_3540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3540_, 0, v___x_3539_);
return v___x_3540_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg___boxed(lean_object* v_o_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_){
_start:
{
lean_object* v_res_3547_; 
v_res_3547_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(v_o_3544_, v___y_3545_);
lean_dec(v___y_3545_);
return v_res_3547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0(lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_){
_start:
{
lean_object* v___x_3553_; lean_object* v___x_3554_; 
v___x_3553_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3550_);
v___x_3554_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(v___x_3553_, v___y_3551_);
return v___x_3554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0___boxed(lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_){
_start:
{
lean_object* v_res_3560_; 
v_res_3560_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0(v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_);
lean_dec(v___y_3558_);
lean_dec_ref(v___y_3557_);
lean_dec(v___y_3556_);
lean_dec_ref(v___y_3555_);
return v_res_3560_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__1(void){
_start:
{
lean_object* v___x_3562_; lean_object* v___x_3563_; 
v___x_3562_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__0));
v___x_3563_ = l_Lean_stringToMessageData(v___x_3562_);
return v___x_3563_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__3(void){
_start:
{
lean_object* v___x_3565_; lean_object* v___x_3566_; 
v___x_3565_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__2));
v___x_3566_ = l_Lean_stringToMessageData(v___x_3565_);
return v___x_3566_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__5(void){
_start:
{
lean_object* v___x_3568_; lean_object* v___x_3569_; 
v___x_3568_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__4));
v___x_3569_ = l_Lean_stringToMessageData(v___x_3568_);
return v___x_3569_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__7(void){
_start:
{
lean_object* v___x_3571_; lean_object* v___x_3572_; 
v___x_3571_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__6));
v___x_3572_ = l_Lean_stringToMessageData(v___x_3571_);
return v___x_3572_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__9(void){
_start:
{
lean_object* v___x_3574_; lean_object* v___x_3575_; 
v___x_3574_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__8));
v___x_3575_ = l_Lean_stringToMessageData(v___x_3574_);
return v___x_3575_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__11(void){
_start:
{
lean_object* v___x_3577_; lean_object* v___x_3578_; 
v___x_3577_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__10));
v___x_3578_ = l_Lean_stringToMessageData(v___x_3577_);
return v___x_3578_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__13(void){
_start:
{
lean_object* v___x_3580_; lean_object* v___x_3581_; 
v___x_3580_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__12));
v___x_3581_ = l_Lean_stringToMessageData(v___x_3580_);
return v___x_3581_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__15(void){
_start:
{
lean_object* v___x_3584_; lean_object* v___x_3585_; 
v___x_3584_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__14));
v___x_3585_ = l_Lean_MessageData_ofFormat(v___x_3584_);
return v___x_3585_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__17(void){
_start:
{
lean_object* v___x_3587_; lean_object* v___x_3588_; 
v___x_3587_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__16));
v___x_3588_ = l_Lean_stringToMessageData(v___x_3587_);
return v___x_3588_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__19(void){
_start:
{
lean_object* v___x_3590_; lean_object* v___x_3591_; 
v___x_3590_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__18));
v___x_3591_ = l_Lean_stringToMessageData(v___x_3590_);
return v___x_3591_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__21(void){
_start:
{
lean_object* v___x_3593_; lean_object* v___x_3594_; 
v___x_3593_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__20));
v___x_3594_ = l_Lean_stringToMessageData(v___x_3593_);
return v___x_3594_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__23(void){
_start:
{
lean_object* v___x_3596_; lean_object* v___x_3597_; 
v___x_3596_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__22));
v___x_3597_ = l_Lean_stringToMessageData(v___x_3596_);
return v___x_3597_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__25(void){
_start:
{
lean_object* v___x_3599_; lean_object* v___x_3600_; 
v___x_3599_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__24));
v___x_3600_ = l_Lean_stringToMessageData(v___x_3599_);
return v___x_3600_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__27(void){
_start:
{
lean_object* v___x_3602_; lean_object* v___x_3603_; 
v___x_3602_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__26));
v___x_3603_ = l_Lean_stringToMessageData(v___x_3602_);
return v___x_3603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkDeprecated(lean_object* v_declName_3604_, uint8_t v_allowSuggestion_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_){
_start:
{
lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v_a_3613_; lean_object* v___x_3615_; uint8_t v_isShared_3616_; uint8_t v_isSharedCheck_3784_; 
v___x_3611_ = ((lean_object*)(l_Lean_Linter_instInhabitedDeprecationEntry_default));
v___x_3612_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0(v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_);
v_a_3613_ = lean_ctor_get(v___x_3612_, 0);
v_isSharedCheck_3784_ = !lean_is_exclusive(v___x_3612_);
if (v_isSharedCheck_3784_ == 0)
{
v___x_3615_ = v___x_3612_;
v_isShared_3616_ = v_isSharedCheck_3784_;
goto v_resetjp_3614_;
}
else
{
lean_inc(v_a_3613_);
lean_dec(v___x_3612_);
v___x_3615_ = lean_box(0);
v_isShared_3616_ = v_isSharedCheck_3784_;
goto v_resetjp_3614_;
}
v_resetjp_3614_:
{
lean_object* v___x_3617_; uint8_t v___x_3618_; lean_object* v_extraMsg_3620_; lean_object* v___y_3621_; lean_object* v___y_3622_; lean_object* v___y_3623_; lean_object* v___y_3624_; 
v___x_3617_ = l_Lean_Linter_linter_deprecated;
v___x_3618_ = l_Lean_Linter_getLinterValue(v___x_3617_, v_a_3613_);
lean_dec(v_a_3613_);
if (v___x_3618_ == 0)
{
lean_object* v___x_3634_; lean_object* v___x_3636_; 
lean_dec(v_declName_3604_);
v___x_3634_ = lean_box(0);
if (v_isShared_3616_ == 0)
{
lean_ctor_set(v___x_3615_, 0, v___x_3634_);
v___x_3636_ = v___x_3615_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v___x_3634_);
v___x_3636_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
return v___x_3636_;
}
}
else
{
lean_object* v___x_3638_; lean_object* v_env_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; 
v___x_3638_ = lean_st_ref_get(v_a_3609_);
v_env_3639_ = lean_ctor_get(v___x_3638_, 0);
lean_inc_ref(v_env_3639_);
lean_dec(v___x_3638_);
v___x_3640_ = l_Lean_Linter_deprecatedAttr;
lean_inc(v_declName_3604_);
v___x_3641_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_3611_, v___x_3640_, v_env_3639_, v_declName_3604_);
if (lean_obj_tag(v___x_3641_) == 1)
{
lean_object* v_val_3642_; lean_object* v_text_x3f_3643_; 
lean_del_object(v___x_3615_);
v_val_3642_ = lean_ctor_get(v___x_3641_, 0);
lean_inc(v_val_3642_);
lean_dec_ref_known(v___x_3641_, 1);
v_text_x3f_3643_ = lean_ctor_get(v_val_3642_, 1);
if (lean_obj_tag(v_text_x3f_3643_) == 0)
{
lean_object* v_newName_x3f_3644_; 
v_newName_x3f_3644_ = lean_ctor_get(v_val_3642_, 0);
lean_inc(v_newName_x3f_3644_);
lean_dec(v_val_3642_);
if (lean_obj_tag(v_newName_x3f_3644_) == 0)
{
lean_object* v___x_3645_; 
v___x_3645_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__9);
v_extraMsg_3620_ = v___x_3645_;
v___y_3621_ = v_a_3606_;
v___y_3622_ = v_a_3607_;
v___y_3623_ = v_a_3608_;
v___y_3624_ = v_a_3609_;
goto v___jp_3619_;
}
else
{
lean_object* v_val_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v_env_3653_; lean_object* v___x_3654_; uint8_t v___x_3655_; lean_object* v___x_3656_; 
v_val_3646_ = lean_ctor_get(v_newName_x3f_3644_, 0);
lean_inc_n(v_val_3646_, 2);
lean_dec_ref_known(v_newName_x3f_3644_, 1);
v___x_3647_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__3, &l_Lean_Linter_checkDeprecated___closed__3_once, _init_l_Lean_Linter_checkDeprecated___closed__3);
v___x_3648_ = l_Lean_MessageData_ofConstName(v_val_3646_, v___x_3618_);
lean_inc_ref(v___x_3648_);
v___x_3649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3649_, 0, v___x_3647_);
lean_ctor_set(v___x_3649_, 1, v___x_3648_);
v___x_3650_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__56_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__56_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__56_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_3651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3651_, 0, v___x_3649_);
lean_ctor_set(v___x_3651_, 1, v___x_3650_);
v___x_3652_ = lean_st_ref_get(v_a_3609_);
v_env_3653_ = lean_ctor_get(v___x_3652_, 0);
lean_inc_ref_n(v_env_3653_, 2);
lean_dec(v___x_3652_);
v___x_3654_ = l_Lean_Name_getPrefix(v_declName_3604_);
v___x_3655_ = 0;
lean_inc(v_declName_3604_);
v___x_3656_ = l_Lean_Environment_find_x3f(v_env_3653_, v_declName_3604_, v___x_3655_);
if (lean_obj_tag(v___x_3656_) == 1)
{
lean_object* v_val_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; 
v_val_3657_ = lean_ctor_get(v___x_3656_, 0);
lean_inc(v_val_3657_);
lean_dec_ref_known(v___x_3656_, 1);
v___x_3658_ = l_Lean_Name_getPrefix(v_val_3646_);
lean_inc(v_val_3646_);
lean_inc_ref(v_env_3653_);
v___x_3659_ = l_Lean_Environment_find_x3f(v_env_3653_, v_val_3646_, v___x_3655_);
if (lean_obj_tag(v___x_3659_) == 1)
{
lean_object* v_val_3660_; lean_object* v___x_3661_; 
v_val_3660_ = lean_ctor_get(v___x_3659_, 0);
lean_inc(v_val_3660_);
lean_dec_ref_known(v___x_3659_, 1);
v___x_3661_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq(v_val_3657_, v_val_3660_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_);
if (lean_obj_tag(v___x_3661_) == 0)
{
lean_object* v_a_3662_; lean_object* v_msg_3664_; lean_object* v___y_3665_; lean_object* v___y_3666_; lean_object* v___y_3667_; lean_object* v___y_3668_; lean_object* v___y_3683_; lean_object* v___y_3684_; lean_object* v___y_3685_; lean_object* v___y_3686_; lean_object* v___y_3687_; lean_object* v___y_3688_; lean_object* v___y_3703_; lean_object* v___y_3704_; lean_object* v___y_3705_; lean_object* v___y_3706_; lean_object* v___y_3707_; lean_object* v___y_3708_; uint8_t v___y_3716_; lean_object* v___y_3717_; lean_object* v___y_3718_; lean_object* v___y_3719_; lean_object* v___y_3720_; lean_object* v___y_3721_; uint8_t v___y_3722_; lean_object* v_msg_3749_; lean_object* v___y_3750_; lean_object* v___y_3751_; lean_object* v___y_3752_; lean_object* v___y_3753_; uint8_t v___x_3756_; 
v_a_3662_ = lean_ctor_get(v___x_3661_, 0);
lean_inc(v_a_3662_);
lean_dec_ref_known(v___x_3661_, 1);
v___x_3756_ = lean_unbox(v_a_3662_);
if (v___x_3756_ == 0)
{
if (v___x_3618_ == 0)
{
lean_dec(v_val_3660_);
lean_dec(v_val_3657_);
v_msg_3749_ = v___x_3651_;
v___y_3750_ = v_a_3606_;
v___y_3751_ = v_a_3607_;
v___y_3752_ = v_a_3608_;
v___y_3753_ = v_a_3609_;
goto v___jp_3748_;
}
else
{
lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; 
v___x_3757_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_3758_ = l_Lean_ConstantInfo_type(v_val_3660_);
lean_dec(v_val_3660_);
v___x_3759_ = l_Lean_indentExpr(v___x_3758_);
v___x_3760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3760_, 0, v___x_3757_);
lean_ctor_set(v___x_3760_, 1, v___x_3759_);
v___x_3761_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_3762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3762_, 0, v___x_3760_);
lean_ctor_set(v___x_3762_, 1, v___x_3761_);
v___x_3763_ = l_Lean_ConstantInfo_type(v_val_3657_);
lean_dec(v_val_3657_);
v___x_3764_ = l_Lean_indentExpr(v___x_3763_);
v___x_3765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3765_, 0, v___x_3762_);
lean_ctor_set(v___x_3765_, 1, v___x_3764_);
v___x_3766_ = l_Lean_MessageData_note(v___x_3765_);
v___x_3767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3767_, 0, v___x_3651_);
lean_ctor_set(v___x_3767_, 1, v___x_3766_);
v_msg_3749_ = v___x_3767_;
v___y_3750_ = v_a_3606_;
v___y_3751_ = v_a_3607_;
v___y_3752_ = v_a_3608_;
v___y_3753_ = v_a_3609_;
goto v___jp_3748_;
}
}
else
{
lean_dec(v_val_3660_);
lean_dec(v_val_3657_);
v_msg_3749_ = v___x_3651_;
v___y_3750_ = v_a_3606_;
v___y_3751_ = v_a_3607_;
v___y_3752_ = v_a_3608_;
v___y_3753_ = v_a_3609_;
goto v___jp_3748_;
}
v___jp_3663_:
{
if (v_allowSuggestion_3605_ == 0)
{
lean_dec(v_a_3662_);
lean_dec(v_val_3646_);
v_extraMsg_3620_ = v_msg_3664_;
v___y_3621_ = v___y_3665_;
v___y_3622_ = v___y_3666_;
v___y_3623_ = v___y_3667_;
v___y_3624_ = v___y_3668_;
goto v___jp_3619_;
}
else
{
uint8_t v___x_3669_; 
v___x_3669_ = lean_unbox(v_a_3662_);
lean_dec(v_a_3662_);
if (v___x_3669_ == 0)
{
lean_dec(v_val_3646_);
v_extraMsg_3620_ = v_msg_3664_;
v___y_3621_ = v___y_3665_;
v___y_3622_ = v___y_3666_;
v___y_3623_ = v___y_3667_;
v___y_3624_ = v___y_3668_;
goto v___jp_3619_;
}
else
{
lean_object* v___x_3670_; 
lean_inc(v_declName_3604_);
v___x_3670_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f(v_declName_3604_, v_val_3646_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
if (lean_obj_tag(v___x_3670_) == 0)
{
lean_object* v_a_3671_; 
v_a_3671_ = lean_ctor_get(v___x_3670_, 0);
lean_inc(v_a_3671_);
lean_dec_ref_known(v___x_3670_, 1);
if (lean_obj_tag(v_a_3671_) == 1)
{
lean_object* v_val_3672_; lean_object* v___x_3673_; 
v_val_3672_ = lean_ctor_get(v_a_3671_, 0);
lean_inc(v_val_3672_);
lean_dec_ref_known(v_a_3671_, 1);
v___x_3673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3673_, 0, v_msg_3664_);
lean_ctor_set(v___x_3673_, 1, v_val_3672_);
v_extraMsg_3620_ = v___x_3673_;
v___y_3621_ = v___y_3665_;
v___y_3622_ = v___y_3666_;
v___y_3623_ = v___y_3667_;
v___y_3624_ = v___y_3668_;
goto v___jp_3619_;
}
else
{
lean_dec(v_a_3671_);
v_extraMsg_3620_ = v_msg_3664_;
v___y_3621_ = v___y_3665_;
v___y_3622_ = v___y_3666_;
v___y_3623_ = v___y_3667_;
v___y_3624_ = v___y_3668_;
goto v___jp_3619_;
}
}
else
{
lean_object* v_a_3674_; lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3681_; 
lean_dec_ref(v_msg_3664_);
lean_dec(v_declName_3604_);
v_a_3674_ = lean_ctor_get(v___x_3670_, 0);
v_isSharedCheck_3681_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3676_ = v___x_3670_;
v_isShared_3677_ = v_isSharedCheck_3681_;
goto v_resetjp_3675_;
}
else
{
lean_inc(v_a_3674_);
lean_dec(v___x_3670_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3681_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
lean_object* v___x_3679_; 
if (v_isShared_3677_ == 0)
{
v___x_3679_ = v___x_3676_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v_a_3674_);
v___x_3679_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
return v___x_3679_;
}
}
}
}
}
}
v___jp_3682_:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; 
v___x_3689_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_3690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3690_, 0, v___x_3689_);
lean_ctor_set(v___x_3690_, 1, v___x_3648_);
v___x_3691_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__5, &l_Lean_Linter_checkDeprecated___closed__5_once, _init_l_Lean_Linter_checkDeprecated___closed__5);
v___x_3692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3690_);
lean_ctor_set(v___x_3692_, 1, v___x_3691_);
v___x_3693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3693_, 0, v___x_3692_);
lean_ctor_set(v___x_3693_, 1, v___y_3688_);
v___x_3694_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__7, &l_Lean_Linter_checkDeprecated___closed__7_once, _init_l_Lean_Linter_checkDeprecated___closed__7);
v___x_3695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3695_, 0, v___x_3693_);
lean_ctor_set(v___x_3695_, 1, v___x_3694_);
v___x_3696_ = l_Lean_MessageData_ofName(v___x_3658_);
v___x_3697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3697_, 0, v___x_3695_);
lean_ctor_set(v___x_3697_, 1, v___x_3696_);
v___x_3698_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__9, &l_Lean_Linter_checkDeprecated___closed__9_once, _init_l_Lean_Linter_checkDeprecated___closed__9);
v___x_3699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3699_, 0, v___x_3697_);
lean_ctor_set(v___x_3699_, 1, v___x_3698_);
v___x_3700_ = l_Lean_MessageData_note(v___x_3699_);
v___x_3701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3701_, 0, v___y_3687_);
lean_ctor_set(v___x_3701_, 1, v___x_3700_);
v_msg_3664_ = v___x_3701_;
v___y_3665_ = v___y_3683_;
v___y_3666_ = v___y_3686_;
v___y_3667_ = v___y_3684_;
v___y_3668_ = v___y_3685_;
goto v___jp_3663_;
}
v___jp_3702_:
{
lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; 
v___x_3709_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__11, &l_Lean_Linter_checkDeprecated___closed__11_once, _init_l_Lean_Linter_checkDeprecated___closed__11);
v___x_3710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3710_, 0, v___x_3709_);
lean_ctor_set(v___x_3710_, 1, v___y_3708_);
v___x_3711_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__13, &l_Lean_Linter_checkDeprecated___closed__13_once, _init_l_Lean_Linter_checkDeprecated___closed__13);
v___x_3712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3712_, 0, v___x_3710_);
lean_ctor_set(v___x_3712_, 1, v___x_3711_);
v___x_3713_ = l_Lean_MessageData_note(v___x_3712_);
v___x_3714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3714_, 0, v___y_3707_);
lean_ctor_set(v___x_3714_, 1, v___x_3713_);
v_msg_3664_ = v___x_3714_;
v___y_3665_ = v___y_3703_;
v___y_3666_ = v___y_3706_;
v___y_3667_ = v___y_3704_;
v___y_3668_ = v___y_3705_;
goto v___jp_3663_;
}
v___jp_3715_:
{
if (v___y_3722_ == 0)
{
uint8_t v___x_3723_; 
lean_inc(v_declName_3604_);
lean_inc_ref(v_env_3653_);
v___x_3723_ = l_Lean_isProtected(v_env_3653_, v_declName_3604_);
if (v___x_3723_ == 0)
{
if (v___x_3618_ == 0)
{
lean_dec(v___x_3658_);
lean_dec_ref(v_env_3653_);
lean_dec_ref(v___x_3648_);
v_msg_3664_ = v___y_3721_;
v___y_3665_ = v___y_3717_;
v___y_3666_ = v___y_3720_;
v___y_3667_ = v___y_3718_;
v___y_3668_ = v___y_3719_;
goto v___jp_3663_;
}
else
{
uint8_t v___x_3724_; 
lean_inc(v_val_3646_);
v___x_3724_ = l_Lean_isProtected(v_env_3653_, v_val_3646_);
if (v___x_3724_ == 0)
{
lean_dec(v___x_3658_);
lean_dec_ref(v___x_3648_);
v_msg_3664_ = v___y_3721_;
v___y_3665_ = v___y_3717_;
v___y_3666_ = v___y_3720_;
v___y_3667_ = v___y_3718_;
v___y_3668_ = v___y_3719_;
goto v___jp_3663_;
}
else
{
lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; uint8_t v___x_3728_; 
lean_inc(v___x_3658_);
v___x_3725_ = l_Lean_Name_componentsRev(v___x_3658_);
v___x_3726_ = lean_unsigned_to_nat(1u);
v___x_3727_ = l_List_lengthTR___redArg(v___x_3725_);
v___x_3728_ = lean_nat_dec_lt(v___x_3726_, v___x_3727_);
lean_dec(v___x_3727_);
if (v___x_3728_ == 0)
{
lean_object* v___x_3729_; 
lean_dec(v___x_3725_);
v___x_3729_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__15, &l_Lean_Linter_checkDeprecated___closed__15_once, _init_l_Lean_Linter_checkDeprecated___closed__15);
v___y_3683_ = v___y_3717_;
v___y_3684_ = v___y_3718_;
v___y_3685_ = v___y_3719_;
v___y_3686_ = v___y_3720_;
v___y_3687_ = v___y_3721_;
v___y_3688_ = v___x_3729_;
goto v___jp_3682_;
}
else
{
lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; 
v___x_3730_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__17, &l_Lean_Linter_checkDeprecated___closed__17_once, _init_l_Lean_Linter_checkDeprecated___closed__17);
v___x_3731_ = lean_unsigned_to_nat(0u);
v___x_3732_ = l_List_get___redArg(v___x_3725_, v___x_3731_);
lean_dec(v___x_3725_);
v___x_3733_ = l_Lean_MessageData_ofName(v___x_3732_);
v___x_3734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3730_);
lean_ctor_set(v___x_3734_, 1, v___x_3733_);
v___x_3735_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__19, &l_Lean_Linter_checkDeprecated___closed__19_once, _init_l_Lean_Linter_checkDeprecated___closed__19);
v___x_3736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3736_, 0, v___x_3734_);
lean_ctor_set(v___x_3736_, 1, v___x_3735_);
v___y_3683_ = v___y_3717_;
v___y_3684_ = v___y_3718_;
v___y_3685_ = v___y_3719_;
v___y_3686_ = v___y_3720_;
v___y_3687_ = v___y_3721_;
v___y_3688_ = v___x_3736_;
goto v___jp_3682_;
}
}
}
}
else
{
lean_dec(v___x_3658_);
lean_dec_ref(v_env_3653_);
lean_dec_ref(v___x_3648_);
v_msg_3664_ = v___y_3721_;
v___y_3665_ = v___y_3717_;
v___y_3666_ = v___y_3720_;
v___y_3667_ = v___y_3718_;
v___y_3668_ = v___y_3719_;
goto v___jp_3663_;
}
}
else
{
lean_dec(v___x_3658_);
lean_dec_ref(v_env_3653_);
lean_dec_ref(v___x_3648_);
if (lean_obj_tag(v_declName_3604_) == 1)
{
lean_object* v_str_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; 
v_str_3737_ = lean_ctor_get(v_declName_3604_, 1);
v___x_3738_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__21, &l_Lean_Linter_checkDeprecated___closed__21_once, _init_l_Lean_Linter_checkDeprecated___closed__21);
lean_inc_ref(v_str_3737_);
v___x_3739_ = l_Lean_stringToMessageData(v_str_3737_);
v___x_3740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3740_, 0, v___x_3738_);
lean_ctor_set(v___x_3740_, 1, v___x_3739_);
v___x_3741_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__23, &l_Lean_Linter_checkDeprecated___closed__23_once, _init_l_Lean_Linter_checkDeprecated___closed__23);
v___x_3742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3742_, 0, v___x_3740_);
lean_ctor_set(v___x_3742_, 1, v___x_3741_);
lean_inc(v_val_3646_);
v___x_3743_ = l_Lean_MessageData_ofConstName(v_val_3646_, v___y_3716_);
v___x_3744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3744_, 0, v___x_3742_);
lean_ctor_set(v___x_3744_, 1, v___x_3743_);
v___x_3745_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__25, &l_Lean_Linter_checkDeprecated___closed__25_once, _init_l_Lean_Linter_checkDeprecated___closed__25);
v___x_3746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3746_, 0, v___x_3744_);
lean_ctor_set(v___x_3746_, 1, v___x_3745_);
v___y_3703_ = v___y_3717_;
v___y_3704_ = v___y_3718_;
v___y_3705_ = v___y_3719_;
v___y_3706_ = v___y_3720_;
v___y_3707_ = v___y_3721_;
v___y_3708_ = v___x_3746_;
goto v___jp_3702_;
}
else
{
lean_object* v___x_3747_; 
v___x_3747_ = l_Lean_MessageData_nil;
v___y_3703_ = v___y_3717_;
v___y_3704_ = v___y_3718_;
v___y_3705_ = v___y_3719_;
v___y_3706_ = v___y_3720_;
v___y_3707_ = v___y_3721_;
v___y_3708_ = v___x_3747_;
goto v___jp_3702_;
}
}
}
v___jp_3748_:
{
uint8_t v___x_3754_; 
v___x_3754_ = l_Lean_Name_isAnonymous(v___x_3654_);
if (v___x_3754_ == 0)
{
uint8_t v___x_3755_; 
v___x_3755_ = lean_name_eq(v___x_3654_, v___x_3658_);
lean_dec(v___x_3654_);
if (v___x_3755_ == 0)
{
v___y_3716_ = v___x_3754_;
v___y_3717_ = v___y_3750_;
v___y_3718_ = v___y_3752_;
v___y_3719_ = v___y_3753_;
v___y_3720_ = v___y_3751_;
v___y_3721_ = v_msg_3749_;
v___y_3722_ = v___x_3618_;
goto v___jp_3715_;
}
else
{
v___y_3716_ = v___x_3754_;
v___y_3717_ = v___y_3750_;
v___y_3718_ = v___y_3752_;
v___y_3719_ = v___y_3753_;
v___y_3720_ = v___y_3751_;
v___y_3721_ = v_msg_3749_;
v___y_3722_ = v___x_3754_;
goto v___jp_3715_;
}
}
else
{
lean_dec(v___x_3658_);
lean_dec(v___x_3654_);
lean_dec_ref(v_env_3653_);
lean_dec_ref(v___x_3648_);
v_msg_3664_ = v_msg_3749_;
v___y_3665_ = v___y_3750_;
v___y_3666_ = v___y_3751_;
v___y_3667_ = v___y_3752_;
v___y_3668_ = v___y_3753_;
goto v___jp_3663_;
}
}
}
else
{
lean_object* v_a_3768_; lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3775_; 
lean_dec(v_val_3660_);
lean_dec(v___x_3658_);
lean_dec(v_val_3657_);
lean_dec(v___x_3654_);
lean_dec_ref(v_env_3653_);
lean_dec_ref_known(v___x_3651_, 2);
lean_dec_ref(v___x_3648_);
lean_dec(v_val_3646_);
lean_dec(v_declName_3604_);
v_a_3768_ = lean_ctor_get(v___x_3661_, 0);
v_isSharedCheck_3775_ = !lean_is_exclusive(v___x_3661_);
if (v_isSharedCheck_3775_ == 0)
{
v___x_3770_ = v___x_3661_;
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
else
{
lean_inc(v_a_3768_);
lean_dec(v___x_3661_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
lean_object* v___x_3773_; 
if (v_isShared_3771_ == 0)
{
v___x_3773_ = v___x_3770_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_a_3768_);
v___x_3773_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
return v___x_3773_;
}
}
}
}
else
{
lean_dec(v___x_3659_);
lean_dec(v___x_3658_);
lean_dec(v_val_3657_);
lean_dec(v___x_3654_);
lean_dec_ref(v_env_3653_);
lean_dec_ref(v___x_3648_);
lean_dec(v_val_3646_);
v_extraMsg_3620_ = v___x_3651_;
v___y_3621_ = v_a_3606_;
v___y_3622_ = v_a_3607_;
v___y_3623_ = v_a_3608_;
v___y_3624_ = v_a_3609_;
goto v___jp_3619_;
}
}
else
{
lean_dec(v___x_3656_);
lean_dec(v___x_3654_);
lean_dec_ref(v_env_3653_);
lean_dec_ref(v___x_3648_);
lean_dec(v_val_3646_);
v_extraMsg_3620_ = v___x_3651_;
v___y_3621_ = v_a_3606_;
v___y_3622_ = v_a_3607_;
v___y_3623_ = v_a_3608_;
v___y_3624_ = v_a_3609_;
goto v___jp_3619_;
}
}
}
else
{
lean_object* v_val_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; 
lean_inc_ref(v_text_x3f_3643_);
lean_dec(v_val_3642_);
v_val_3776_ = lean_ctor_get(v_text_x3f_3643_, 0);
lean_inc(v_val_3776_);
lean_dec_ref_known(v_text_x3f_3643_, 1);
v___x_3777_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__27, &l_Lean_Linter_checkDeprecated___closed__27_once, _init_l_Lean_Linter_checkDeprecated___closed__27);
v___x_3778_ = l_Lean_stringToMessageData(v_val_3776_);
v___x_3779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3779_, 0, v___x_3777_);
lean_ctor_set(v___x_3779_, 1, v___x_3778_);
v_extraMsg_3620_ = v___x_3779_;
v___y_3621_ = v_a_3606_;
v___y_3622_ = v_a_3607_;
v___y_3623_ = v_a_3608_;
v___y_3624_ = v_a_3609_;
goto v___jp_3619_;
}
}
else
{
lean_object* v___x_3780_; lean_object* v___x_3782_; 
lean_dec(v___x_3641_);
lean_dec(v_declName_3604_);
v___x_3780_ = lean_box(0);
if (v_isShared_3616_ == 0)
{
lean_ctor_set(v___x_3615_, 0, v___x_3780_);
v___x_3782_ = v___x_3615_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v___x_3780_);
v___x_3782_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
return v___x_3782_;
}
}
}
v___jp_3619_:
{
lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; 
v___x_3625_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_3626_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_3627_ = l_Lean_MessageData_ofConstName(v_declName_3604_, v___x_3618_);
v___x_3628_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3628_, 0, v___x_3626_);
lean_ctor_set(v___x_3628_, 1, v___x_3627_);
v___x_3629_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__1, &l_Lean_Linter_checkDeprecated___closed__1_once, _init_l_Lean_Linter_checkDeprecated___closed__1);
v___x_3630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3630_, 0, v___x_3628_);
lean_ctor_set(v___x_3630_, 1, v___x_3629_);
v___x_3631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3631_, 0, v___x_3630_);
lean_ctor_set(v___x_3631_, 1, v_extraMsg_3620_);
v___x_3632_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3632_, 0, v___x_3625_);
lean_ctor_set(v___x_3632_, 1, v___x_3631_);
v___x_3633_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38(v___x_3632_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
return v___x_3633_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkDeprecated___boxed(lean_object* v_declName_3785_, lean_object* v_allowSuggestion_3786_, lean_object* v_a_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_){
_start:
{
uint8_t v_allowSuggestion_boxed_3792_; lean_object* v_res_3793_; 
v_allowSuggestion_boxed_3792_ = lean_unbox(v_allowSuggestion_3786_);
v_res_3793_ = l_Lean_Linter_checkDeprecated(v_declName_3785_, v_allowSuggestion_boxed_3792_, v_a_3787_, v_a_3788_, v_a_3789_, v_a_3790_);
lean_dec(v_a_3790_);
lean_dec_ref(v_a_3789_);
lean_dec(v_a_3788_);
lean_dec_ref(v_a_3787_);
return v_res_3793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0(lean_object* v_o_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_){
_start:
{
lean_object* v___x_3800_; 
v___x_3800_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(v_o_3794_, v___y_3798_);
return v___x_3800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___boxed(lean_object* v_o_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_){
_start:
{
lean_object* v_res_3807_; 
v_res_3807_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0(v_o_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_);
lean_dec(v___y_3805_);
lean_dec_ref(v___y_3804_);
lean_dec(v___y_3803_);
lean_dec_ref(v___y_3802_);
return v_res_3807_;
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
res = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_();
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
