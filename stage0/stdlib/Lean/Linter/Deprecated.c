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
lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1_ = stack[0].m_obj;
lean_object* v_decl_2_ = stack[1].m_obj;
lean_object* v_ref_3_ = stack[2].m_obj;
lean_object* v_res_29_;
v_res_29_ = l_Lean_Option_register___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__spec__0(v_name_1_, v_decl_2_, v_ref_3_);
stack->m_obj
 = v_res_29_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_30_, lean_object* v_decl_31_, lean_object* v_ref_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Option_register___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__spec__0(v_name_30_, v_decl_31_, v_ref_32_);
lean_dec_ref(v_decl_31_);
return v_res_34_;
}
}
lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_54_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_));
v___x_55_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_));
v___x_56_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_));
v___x_57_ = l_Lean_Option_register___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__spec__0(v___x_54_, v___x_55_, v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT void l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_58_;
v_res_58_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_();
stack->m_obj
 = v_res_58_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4____boxed(lean_object* v_a_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_();
return v_res_60_;
}
}
lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_79_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4_));
v___x_80_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4_));
v___x_81_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4_));
v___x_82_ = l_Lean_Option_register___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__spec__0(v___x_79_, v___x_80_, v___x_81_);
return v___x_82_;
}
}
LEAN_EXPORT void l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_83_;
v_res_83_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4_();
stack->m_obj
 = v_res_83_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4____boxed(lean_object* v_a_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_651724526____hygCtx___hyg_4_();
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate_spec__1(lean_object* v_a_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = lean_nat_to_int(v_a_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate_spec__2(lean_object* v_a_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = l_Rat_ofInt(v_a_92_);
return v___x_93_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___lam__0___closed__0(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = lean_unsigned_to_nat(1000000000u);
v___x_95_ = lean_nat_to_int(v___x_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___lam__0(lean_object* v_tz_96_, lean_object* v_a_97_, lean_object* v___x_98_, lean_object* v_x_99_){
_start:
{
lean_object* v_offset_100_; lean_object* v_second_101_; lean_object* v_nano_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v_nanos_106_; lean_object* v___x_107_; lean_object* v_nanos_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v_offset_100_ = lean_ctor_get(v_tz_96_, 0);
v_second_101_ = lean_ctor_get(v_a_97_, 0);
v_nano_102_ = lean_ctor_get(v_a_97_, 1);
v___x_103_ = lean_nat_to_int(v___x_98_);
v___x_104_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___lam__0___closed__0, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___lam__0___closed__0_once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___lam__0___closed__0);
v___x_105_ = lean_int_mul(v_second_101_, v___x_104_);
v_nanos_106_ = lean_int_add(v___x_105_, v_nano_102_);
lean_dec(v___x_105_);
v___x_107_ = lean_int_mul(v_offset_100_, v___x_104_);
v_nanos_108_ = lean_int_add(v___x_107_, v___x_103_);
lean_dec(v___x_103_);
lean_dec(v___x_107_);
v___x_109_ = lean_int_add(v_nanos_106_, v_nanos_108_);
lean_dec(v_nanos_108_);
lean_dec(v_nanos_106_);
v___x_110_ = l_Std_Time_Duration_ofNanoseconds(v___x_109_);
lean_dec(v___x_109_);
v___x_111_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___lam__0___boxed(lean_object* v_tz_112_, lean_object* v_a_113_, lean_object* v___x_114_, lean_object* v_x_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___lam__0(v_tz_112_, v_a_113_, v___x_114_, v_x_115_);
lean_dec_ref(v_a_113_);
lean_dec_ref(v_tz_112_);
return v_res_116_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__0(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_117_ = lean_unsigned_to_nat(0u);
v___x_118_ = lean_nat_to_int(v___x_117_);
return v___x_118_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__3(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_122_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__2));
v___x_123_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__0, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__0_once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__0);
v___x_124_ = l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone(v___x_123_, v___x_122_, v___x_122_);
return v___x_124_;
}
}
lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate(){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = lean_get_current_time();
if (lean_obj_tag(v___x_151_) == 0)
{
lean_object* v_a_152_; lean_object* v___x_153_; 
v_a_152_ = lean_ctor_get(v___x_151_, 0);
lean_inc(v_a_152_);
lean_dec_ref_known(v___x_151_, 1);
v___x_153_ = l_Std_Time_Database_defaultGetLocalZoneRules();
if (lean_obj_tag(v___x_153_) == 0)
{
lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_176_; 
v_a_154_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_176_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_176_ == 0)
{
v___x_156_ = v___x_153_;
v_isShared_157_ = v_isSharedCheck_176_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_153_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_176_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v_offset_160_; lean_object* v_second_161_; lean_object* v_nano_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v_nanos_166_; lean_object* v___x_167_; lean_object* v_nanos_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v_date_172_; lean_object* v___x_174_; 
v___x_158_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForTimestamp(v_a_154_, v_a_152_);
v___x_159_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v___x_158_);
lean_dec_ref(v___x_158_);
v_offset_160_ = lean_ctor_get(v___x_159_, 0);
lean_inc(v_offset_160_);
lean_dec_ref(v___x_159_);
v_second_161_ = lean_ctor_get(v_a_152_, 0);
lean_inc(v_second_161_);
v_nano_162_ = lean_ctor_get(v_a_152_, 1);
lean_inc(v_nano_162_);
lean_dec(v_a_152_);
v___x_163_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__0, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__0_once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__0);
v___x_164_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___lam__0___closed__0, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___lam__0___closed__0_once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___lam__0___closed__0);
v___x_165_ = lean_int_mul(v_second_161_, v___x_164_);
lean_dec(v_second_161_);
v_nanos_166_ = lean_int_add(v___x_165_, v_nano_162_);
lean_dec(v_nano_162_);
lean_dec(v___x_165_);
v___x_167_ = lean_int_mul(v_offset_160_, v___x_164_);
lean_dec(v_offset_160_);
v_nanos_168_ = lean_int_add(v___x_167_, v___x_163_);
lean_dec(v___x_167_);
v___x_169_ = lean_int_add(v_nanos_166_, v_nanos_168_);
lean_dec(v_nanos_168_);
lean_dec(v_nanos_166_);
v___x_170_ = l_Std_Time_Duration_ofNanoseconds(v___x_169_);
lean_dec(v___x_169_);
v___x_171_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_170_);
v_date_172_ = lean_ctor_get(v___x_171_, 0);
lean_inc_ref(v_date_172_);
lean_dec_ref(v___x_171_);
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 0, v_date_172_);
v___x_174_ = v___x_156_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_date_172_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
else
{
lean_dec_ref_known(v___x_153_, 1);
lean_dec(v_a_152_);
goto v___jp_126_;
}
}
else
{
lean_dec_ref_known(v___x_151_, 1);
goto v___jp_126_;
}
v___jp_126_:
{
lean_object* v___x_127_; 
v___x_127_ = lean_get_current_time();
if (lean_obj_tag(v___x_127_) == 0)
{
lean_object* v_a_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_142_; 
v_a_128_ = lean_ctor_get(v___x_127_, 0);
v_isSharedCheck_142_ = !lean_is_exclusive(v___x_127_);
if (v_isSharedCheck_142_ == 0)
{
v___x_130_ = v___x_127_;
v_isShared_131_ = v_isSharedCheck_142_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_a_128_);
lean_dec(v___x_127_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_142_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v_tz_134_; lean_object* v___f_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v_date_138_; lean_object* v___x_140_; 
v___x_132_ = lean_unsigned_to_nat(0u);
v___x_133_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__3, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__3_once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___closed__3);
v_tz_134_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v___x_133_, v_a_128_);
v___f_135_ = lean_alloc_closure((void*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___lam__0___boxed), 4, 3);
lean_closure_set(v___f_135_, 0, v_tz_134_);
lean_closure_set(v___f_135_, 1, v_a_128_);
lean_closure_set(v___f_135_, 2, v___x_132_);
v___x_136_ = lean_mk_thunk(v___f_135_);
v___x_137_ = lean_thunk_get_own(v___x_136_);
lean_dec_ref(v___x_136_);
v_date_138_ = lean_ctor_get(v___x_137_, 0);
lean_inc_ref(v_date_138_);
lean_dec(v___x_137_);
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 0, v_date_138_);
v___x_140_ = v___x_130_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v_date_138_);
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
lean_object* v_a_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_150_; 
v_a_143_ = lean_ctor_get(v___x_127_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v___x_127_);
if (v_isSharedCheck_150_ == 0)
{
v___x_145_ = v___x_127_;
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_a_143_);
lean_dec(v___x_127_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_148_; 
if (v_isShared_146_ == 0)
{
v___x_148_ = v___x_145_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_a_143_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_177_;
v_res_177_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate();
stack->m_obj
 = v_res_177_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate___boxed(lean_object* v_a_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate();
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate_spec__0(lean_object* v_a_180_){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = lean_nat_to_int(v_a_180_);
v___x_182_ = l_Rat_ofInt(v___x_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_mkSinceHint___lam__0(lean_object* v___x_184_, lean_object* v_x_185_){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_186_ = ((lean_object*)(l_Lean_Linter_mkSinceHint___lam__0___closed__0));
v___x_187_ = lean_string_append(v___x_186_, v___x_184_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_mkSinceHint___lam__0___boxed(lean_object* v___x_188_, lean_object* v_x_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Lean_Linter_mkSinceHint___lam__0(v___x_188_, v_x_189_);
lean_dec_ref(v_x_189_);
lean_dec_ref(v___x_188_);
return v_res_190_;
}
}
static lean_object* _init_l_Lean_Linter_mkSinceHint___closed__4(void){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = ((lean_object*)(l_Lean_Linter_mkSinceHint___closed__3));
v___x_197_ = l_Lean_MessageData_ofFormat(v___x_196_);
return v___x_197_;
}
}
lean_object* l_Lean_Linter_mkSinceHint(lean_object* v_stx_199_, lean_object* v_a_200_, lean_object* v_a_201_){
_start:
{
uint8_t v___x_203_; lean_object* v___x_204_; 
v___x_203_ = 1;
v___x_204_ = l_Lean_Syntax_getTailPos_x3f(v_stx_199_, v___x_203_);
if (lean_obj_tag(v___x_204_) == 1)
{
lean_object* v_val_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_253_; 
v_val_205_ = lean_ctor_get(v___x_204_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_253_ == 0)
{
v___x_207_ = v___x_204_;
v_isShared_208_ = v_isSharedCheck_253_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_val_205_);
lean_dec(v___x_204_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_253_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v_ref_209_; lean_object* v___x_210_; 
v_ref_209_ = lean_ctor_get(v_a_200_, 2);
v___x_210_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_currentDate();
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v_a_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___f_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_226_; 
v_a_211_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_a_211_);
lean_dec_ref_known(v___x_210_, 1);
v___x_212_ = ((lean_object*)(l_Lean_Linter_mkSinceHint___closed__0));
v___x_213_ = l_Std_Time_PlainDate_toLeanDateString(v_a_211_);
v___x_214_ = lean_string_append(v___x_212_, v___x_213_);
lean_dec_ref(v___x_213_);
v___x_215_ = ((lean_object*)(l_Lean_Linter_mkSinceHint___closed__1));
v___x_216_ = lean_string_append(v___x_214_, v___x_215_);
lean_inc_ref(v___x_216_);
v___f_217_ = lean_alloc_closure((void*)(l_Lean_Linter_mkSinceHint___lam__0___boxed), 2, 1);
lean_closure_set(v___f_217_, 0, v___x_216_);
v___x_218_ = lean_obj_once(&l_Lean_Linter_mkSinceHint___closed__4, &l_Lean_Linter_mkSinceHint___closed__4_once, _init_l_Lean_Linter_mkSinceHint___closed__4);
v___x_219_ = ((lean_object*)(l_Lean_Linter_mkSinceHint___closed__5));
v___x_220_ = lean_string_append(v___x_219_, v___x_216_);
v___x_221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
v___x_222_ = lean_box(0);
v___x_223_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_223_, 0, v___x_216_);
v___x_224_ = l_Lean_MessageData_ofFormat(v___x_223_);
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 0, v___x_224_);
v___x_226_ = v___x_207_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_224_);
v___x_226_ = v_reuseFailAlloc_240_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; uint8_t v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; uint8_t v___x_238_; lean_object* v___x_239_; 
v___x_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_227_, 0, v___f_217_);
v___x_228_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_228_, 0, v___x_221_);
lean_ctor_set(v___x_228_, 1, v___x_222_);
lean_ctor_set(v___x_228_, 2, v___x_222_);
lean_ctor_set(v___x_228_, 3, v___x_222_);
lean_ctor_set(v___x_228_, 4, v___x_226_);
lean_ctor_set(v___x_228_, 5, v___x_227_);
lean_inc(v_val_205_);
v___x_229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_229_, 0, v_val_205_);
lean_ctor_set(v___x_229_, 1, v_val_205_);
v___x_230_ = l_Lean_Syntax_ofRange(v___x_229_, v___x_203_);
v___x_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
v___x_232_ = 4;
v___x_233_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_233_, 0, v___x_228_);
lean_ctor_set(v___x_233_, 1, v___x_231_);
lean_ctor_set(v___x_233_, 2, v___x_222_);
lean_ctor_set_uint8(v___x_233_, sizeof(void*)*3, v___x_232_);
v___x_234_ = lean_unsigned_to_nat(1u);
v___x_235_ = lean_mk_empty_array_with_capacity(v___x_234_);
v___x_236_ = lean_array_push(v___x_235_, v___x_233_);
v___x_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_237_, 0, v_stx_199_);
v___x_238_ = 0;
v___x_239_ = l_Lean_MessageData_hint(v___x_218_, v___x_236_, v___x_237_, v___x_222_, v___x_238_, v_a_200_, v_a_201_);
lean_dec_ref(v___x_236_);
return v___x_239_;
}
}
else
{
lean_object* v_a_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_252_; 
lean_del_object(v___x_207_);
lean_dec(v_val_205_);
lean_dec(v_stx_199_);
v_a_241_ = lean_ctor_get(v___x_210_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_252_ == 0)
{
v___x_243_ = v___x_210_;
v_isShared_244_ = v_isSharedCheck_252_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_a_241_);
lean_dec(v___x_210_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_252_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_250_; 
v___x_245_ = lean_io_error_to_string(v_a_241_);
v___x_246_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
v___x_247_ = l_Lean_MessageData_ofFormat(v___x_246_);
lean_inc(v_ref_209_);
v___x_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_248_, 0, v_ref_209_);
lean_ctor_set(v___x_248_, 1, v___x_247_);
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 0, v___x_248_);
v___x_250_ = v___x_243_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___x_248_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
}
}
else
{
lean_object* v___x_254_; lean_object* v___x_255_; 
lean_dec(v___x_204_);
lean_dec(v_stx_199_);
v___x_254_ = l_Lean_MessageData_nil;
v___x_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
return v___x_255_;
}
}
}
LEAN_EXPORT void l_Lean_Linter_mkSinceHint_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_199_ = stack[0].m_obj;
lean_object* v_a_200_ = stack[1].m_obj;
lean_object* v_a_201_ = stack[2].m_obj;
lean_object* v_res_256_;
v_res_256_ = l_Lean_Linter_mkSinceHint(v_stx_199_, v_a_200_, v_a_201_);
stack->m_obj
 = v_res_256_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_mkSinceHint___boxed(lean_object* v_stx_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Lean_Linter_mkSinceHint(v_stx_257_, v_a_258_, v_a_259_);
lean_dec(v_a_259_);
lean_dec_ref(v_a_258_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq_spec__0(lean_object* v_a_265_, lean_object* v_a_266_){
_start:
{
if (lean_obj_tag(v_a_265_) == 0)
{
lean_object* v___x_267_; 
v___x_267_ = lean_array_to_list(v_a_266_);
return v___x_267_;
}
else
{
lean_object* v_tail_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v_tail_268_ = lean_ctor_get(v_a_265_, 1);
v___x_269_ = lean_array_get_size(v_a_266_);
v___x_270_ = ((lean_object*)(l_List_mapIdx_go___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq_spec__0___closed__1));
v___x_271_ = l_Lean_Name_num___override(v___x_270_, v___x_269_);
v___x_272_ = l_Lean_mkLevelParam(v___x_271_);
v___x_273_ = lean_array_push(v_a_266_, v___x_272_);
v_a_265_ = v_tail_268_;
v_a_266_ = v___x_273_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq_spec__0___boxed(lean_object* v_a_275_, lean_object* v_a_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_List_mapIdx_go___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq_spec__0(v_a_275_, v_a_276_);
lean_dec(v_a_275_);
return v_res_277_;
}
}
lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq(lean_object* v_decl_u2081_280_, lean_object* v_decl_u2082_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_){
_start:
{
lean_object* v___y_288_; lean_object* v___x_305_; lean_object* v___x_306_; uint8_t v___x_307_; 
v___x_305_ = l_Lean_ConstantInfo_numLevelParams(v_decl_u2081_280_);
v___x_306_ = l_Lean_ConstantInfo_numLevelParams(v_decl_u2082_281_);
v___x_307_ = lean_nat_dec_eq(v___x_305_, v___x_306_);
lean_dec(v___x_306_);
lean_dec(v___x_305_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = lean_box(v___x_307_);
v___x_309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
return v___x_309_;
}
else
{
lean_object* v___x_310_; uint8_t v_transparency_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v_levels_314_; lean_object* v_type_u2081_315_; lean_object* v_type_u2082_316_; uint8_t v___x_317_; uint8_t v___x_318_; 
v___x_310_ = l_Lean_Meta_Context_config(v_a_282_);
v_transparency_311_ = lean_ctor_get_uint8(v___x_310_, 9);
lean_dec_ref(v___x_310_);
v___x_312_ = l_Lean_ConstantInfo_levelParams(v_decl_u2081_280_);
v___x_313_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq___closed__0));
v_levels_314_ = l_List_mapIdx_go___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq_spec__0(v___x_312_, v___x_313_);
lean_dec(v___x_312_);
lean_inc(v_levels_314_);
v_type_u2081_315_ = l_Lean_ConstantInfo_instantiateTypeLevelParams(v_decl_u2081_280_, v_levels_314_);
v_type_u2082_316_ = l_Lean_ConstantInfo_instantiateTypeLevelParams(v_decl_u2082_281_, v_levels_314_);
v___x_317_ = 2;
v___x_318_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_311_, v___x_317_);
if (v___x_318_ == 0)
{
lean_object* v_keyedConfig_319_; uint8_t v_trackZetaDelta_320_; lean_object* v_zetaDeltaSet_321_; lean_object* v_lctx_322_; lean_object* v_localInstances_323_; lean_object* v_defEqCtx_x3f_324_; lean_object* v_synthPendingDepth_325_; lean_object* v_customCanUnfoldPredicate_x3f_326_; uint8_t v_univApprox_327_; uint8_t v_inTypeClassResolution_328_; uint8_t v_cacheInferType_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v_keyedConfig_319_ = lean_ctor_get(v_a_282_, 0);
v_trackZetaDelta_320_ = lean_ctor_get_uint8(v_a_282_, sizeof(void*)*7);
v_zetaDeltaSet_321_ = lean_ctor_get(v_a_282_, 1);
v_lctx_322_ = lean_ctor_get(v_a_282_, 2);
v_localInstances_323_ = lean_ctor_get(v_a_282_, 3);
v_defEqCtx_x3f_324_ = lean_ctor_get(v_a_282_, 4);
v_synthPendingDepth_325_ = lean_ctor_get(v_a_282_, 5);
v_customCanUnfoldPredicate_x3f_326_ = lean_ctor_get(v_a_282_, 6);
v_univApprox_327_ = lean_ctor_get_uint8(v_a_282_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_328_ = lean_ctor_get_uint8(v_a_282_, sizeof(void*)*7 + 2);
v_cacheInferType_329_ = lean_ctor_get_uint8(v_a_282_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_319_);
v___x_330_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_317_, v_keyedConfig_319_);
lean_inc(v_customCanUnfoldPredicate_x3f_326_);
lean_inc(v_synthPendingDepth_325_);
lean_inc(v_defEqCtx_x3f_324_);
lean_inc_ref(v_localInstances_323_);
lean_inc_ref(v_lctx_322_);
lean_inc(v_zetaDeltaSet_321_);
v___x_331_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_331_, 0, v___x_330_);
lean_ctor_set(v___x_331_, 1, v_zetaDeltaSet_321_);
lean_ctor_set(v___x_331_, 2, v_lctx_322_);
lean_ctor_set(v___x_331_, 3, v_localInstances_323_);
lean_ctor_set(v___x_331_, 4, v_defEqCtx_x3f_324_);
lean_ctor_set(v___x_331_, 5, v_synthPendingDepth_325_);
lean_ctor_set(v___x_331_, 6, v_customCanUnfoldPredicate_x3f_326_);
lean_ctor_set_uint8(v___x_331_, sizeof(void*)*7, v_trackZetaDelta_320_);
lean_ctor_set_uint8(v___x_331_, sizeof(void*)*7 + 1, v_univApprox_327_);
lean_ctor_set_uint8(v___x_331_, sizeof(void*)*7 + 2, v_inTypeClassResolution_328_);
lean_ctor_set_uint8(v___x_331_, sizeof(void*)*7 + 3, v_cacheInferType_329_);
v___x_332_ = l_Lean_Meta_isExprDefEqGuarded(v_type_u2081_315_, v_type_u2082_316_, v___x_331_, v_a_283_, v_a_284_, v_a_285_);
lean_dec_ref_known(v___x_331_, 7);
v___y_288_ = v___x_332_;
goto v___jp_287_;
}
else
{
lean_object* v___x_333_; 
v___x_333_ = l_Lean_Meta_isExprDefEqGuarded(v_type_u2081_315_, v_type_u2082_316_, v_a_282_, v_a_283_, v_a_284_, v_a_285_);
v___y_288_ = v___x_333_;
goto v___jp_287_;
}
}
v___jp_287_:
{
if (lean_obj_tag(v___y_288_) == 0)
{
lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_296_; 
v_a_289_ = lean_ctor_get(v___y_288_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___y_288_);
if (v_isSharedCheck_296_ == 0)
{
v___x_291_ = v___y_288_;
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___y_288_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_294_; 
if (v_isShared_292_ == 0)
{
v___x_294_ = v___x_291_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_a_289_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
else
{
lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_304_; 
v_a_297_ = lean_ctor_get(v___y_288_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v___y_288_);
if (v_isSharedCheck_304_ == 0)
{
v___x_299_ = v___y_288_;
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_a_297_);
lean_dec(v___y_288_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_302_; 
if (v_isShared_300_ == 0)
{
v___x_302_ = v___x_299_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_a_297_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_u2081_280_ = stack[0].m_obj;
lean_object* v_decl_u2082_281_ = stack[1].m_obj;
lean_object* v_a_282_ = stack[2].m_obj;
lean_object* v_a_283_ = stack[3].m_obj;
lean_object* v_a_284_ = stack[4].m_obj;
lean_object* v_a_285_ = stack[5].m_obj;
lean_object* v_res_334_;
v_res_334_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq(v_decl_u2081_280_, v_decl_u2082_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_);
stack->m_obj
 = v_res_334_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq___boxed(lean_object* v_decl_u2081_335_, lean_object* v_decl_u2082_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq(v_decl_u2081_335_, v_decl_u2082_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_);
lean_dec(v_a_340_);
lean_dec_ref(v_a_339_);
lean_dec(v_a_338_);
lean_dec_ref(v_a_337_);
lean_dec_ref(v_decl_u2082_336_);
lean_dec_ref(v_decl_u2081_335_);
return v_res_342_;
}
}
uint8_t l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4(lean_object* v_opts_343_, lean_object* v_opt_344_){
_start:
{
lean_object* v_name_345_; lean_object* v_defValue_346_; lean_object* v_map_347_; lean_object* v___x_348_; 
v_name_345_ = lean_ctor_get(v_opt_344_, 0);
v_defValue_346_ = lean_ctor_get(v_opt_344_, 1);
v_map_347_ = lean_ctor_get(v_opts_343_, 0);
v___x_348_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_347_, v_name_345_);
if (lean_obj_tag(v___x_348_) == 0)
{
uint8_t v___x_349_; 
v___x_349_ = lean_unbox(v_defValue_346_);
return v___x_349_;
}
else
{
lean_object* v_val_350_; 
v_val_350_ = lean_ctor_get(v___x_348_, 0);
lean_inc(v_val_350_);
lean_dec_ref_known(v___x_348_, 1);
if (lean_obj_tag(v_val_350_) == 1)
{
uint8_t v_v_351_; 
v_v_351_ = lean_ctor_get_uint8(v_val_350_, 0);
lean_dec_ref_known(v_val_350_, 0);
return v_v_351_;
}
else
{
uint8_t v___x_352_; 
lean_dec(v_val_350_);
v___x_352_ = lean_unbox(v_defValue_346_);
return v___x_352_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_343_ = stack[0].m_obj;
lean_object* v_opt_344_ = stack[1].m_obj;
uint8_t v_res_353_;
v_res_353_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4(v_opts_343_, v_opt_344_);
stack->m_num = v_res_353_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4___boxed(lean_object* v_opts_354_, lean_object* v_opt_355_){
_start:
{
uint8_t v_res_356_; lean_object* v_r_357_; 
v_res_356_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4(v_opts_354_, v_opt_355_);
lean_dec_ref(v_opt_355_);
lean_dec_ref(v_opts_354_);
v_r_357_ = lean_box(v_res_356_);
return v_r_357_;
}
}
uint8_t l_instBEqOption_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6(lean_object* v_x_358_, lean_object* v_x_359_){
_start:
{
if (lean_obj_tag(v_x_358_) == 0)
{
if (lean_obj_tag(v_x_359_) == 0)
{
uint8_t v___x_360_; 
v___x_360_ = 1;
return v___x_360_;
}
else
{
uint8_t v___x_361_; 
v___x_361_ = 0;
return v___x_361_;
}
}
else
{
if (lean_obj_tag(v_x_359_) == 0)
{
uint8_t v___x_362_; 
v___x_362_ = 0;
return v___x_362_;
}
else
{
lean_object* v_val_363_; lean_object* v_val_364_; uint8_t v___x_365_; 
v_val_363_ = lean_ctor_get(v_x_358_, 0);
v_val_364_ = lean_ctor_get(v_x_359_, 0);
v___x_365_ = lean_name_eq(v_val_363_, v_val_364_);
return v___x_365_;
}
}
}
}
LEAN_EXPORT void l_instBEqOption_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_358_ = stack[0].m_obj;
lean_object* v_x_359_ = stack[1].m_obj;
uint8_t v_res_366_;
v_res_366_ = l_instBEqOption_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6(v_x_358_, v_x_359_);
stack->m_num = v_res_366_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6___boxed(lean_object* v_x_367_, lean_object* v_x_368_){
_start:
{
uint8_t v_res_369_; lean_object* v_r_370_; 
v_res_369_ = l_instBEqOption_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6(v_x_367_, v_x_368_);
lean_dec(v_x_368_);
lean_dec(v_x_367_);
v_r_370_ = lean_box(v_res_369_);
return v_r_370_;
}
}
uint8_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(lean_object* v_env_371_, lean_object* v_n_372_, lean_object* v_x_373_){
_start:
{
uint8_t v___x_374_; uint8_t v___x_375_; 
v___x_374_ = 1;
v___x_375_ = l_Lean_Environment_contains(v_env_371_, v_n_372_, v___x_374_);
return v___x_375_;
}
}
LEAN_EXPORT void l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_env_371_ = stack[0].m_obj;
lean_object* v_n_372_ = stack[1].m_obj;
lean_object* v_x_373_ = stack[2].m_obj;
uint8_t v_res_376_;
v_res_376_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(v_env_371_, v_n_372_, v_x_373_);
stack->m_num = v_res_376_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2____boxed(lean_object* v_env_377_, lean_object* v_n_378_, lean_object* v_x_379_){
_start:
{
uint8_t v_res_380_; lean_object* v_r_381_; 
v_res_380_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(v_env_377_, v_n_378_, v_x_379_);
lean_dec_ref(v_x_379_);
v_r_381_ = lean_box(v_res_380_);
return v_r_381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(lean_object* v_x_383_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__0_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2____boxed(lean_object* v_x_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(v_x_385_);
lean_dec_ref(v_x_385_);
return v_res_386_;
}
}
lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(lean_object* v_x_387_, lean_object* v_x_388_, lean_object* v_x_389_, lean_object* v___y_390_){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = lean_box(0);
v___x_393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
return v___x_393_;
}
}
LEAN_EXPORT void l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_x_387_ = stack[0].m_obj;
lean_object* v_x_388_ = stack[1].m_obj;
lean_object* v_x_389_ = stack[2].m_obj;
lean_object* v___y_390_ = stack[3].m_obj;
lean_object* v_res_394_;
v_res_394_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(v_x_387_, v_x_388_, v_x_389_, v___y_390_);
stack->m_obj
 = v_res_394_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2____boxed(lean_object* v_x_395_, lean_object* v_x_396_, lean_object* v_x_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(v_x_395_, v_x_396_, v_x_397_, v___y_398_);
lean_dec(v___y_398_);
lean_dec_ref(v_x_397_);
lean_dec_ref(v_x_396_);
lean_dec(v_x_395_);
return v_res_400_;
}
}
uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0(uint8_t v_suppressElabErrors_409_, uint8_t v___y_410_, lean_object* v_x_411_){
_start:
{
if (lean_obj_tag(v_x_411_) == 1)
{
lean_object* v_pre_412_; 
v_pre_412_ = lean_ctor_get(v_x_411_, 0);
switch(lean_obj_tag(v_pre_412_))
{
case 1:
{
lean_object* v_pre_413_; 
v_pre_413_ = lean_ctor_get(v_pre_412_, 0);
switch(lean_obj_tag(v_pre_413_))
{
case 0:
{
lean_object* v_str_414_; lean_object* v_str_415_; lean_object* v___x_416_; uint8_t v___x_417_; 
v_str_414_ = lean_ctor_get(v_x_411_, 1);
v_str_415_ = lean_ctor_get(v_pre_412_, 1);
v___x_416_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__0));
v___x_417_ = lean_string_dec_eq(v_str_415_, v___x_416_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; uint8_t v___x_419_; 
v___x_418_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__1));
v___x_419_ = lean_string_dec_eq(v_str_415_, v___x_418_);
if (v___x_419_ == 0)
{
return v___x_419_;
}
else
{
lean_object* v___x_420_; uint8_t v___x_421_; 
v___x_420_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__2));
v___x_421_ = lean_string_dec_eq(v_str_414_, v___x_420_);
if (v___x_421_ == 0)
{
return v___x_421_;
}
else
{
return v_suppressElabErrors_409_;
}
}
}
else
{
lean_object* v___x_422_; uint8_t v___x_423_; 
v___x_422_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__3));
v___x_423_ = lean_string_dec_eq(v_str_414_, v___x_422_);
if (v___x_423_ == 0)
{
return v___x_423_;
}
else
{
return v_suppressElabErrors_409_;
}
}
}
case 1:
{
lean_object* v_pre_424_; 
v_pre_424_ = lean_ctor_get(v_pre_413_, 0);
if (lean_obj_tag(v_pre_424_) == 0)
{
lean_object* v_str_425_; lean_object* v_str_426_; lean_object* v_str_427_; lean_object* v___x_428_; uint8_t v___x_429_; 
v_str_425_ = lean_ctor_get(v_x_411_, 1);
v_str_426_ = lean_ctor_get(v_pre_412_, 1);
v_str_427_ = lean_ctor_get(v_pre_413_, 1);
v___x_428_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__4));
v___x_429_ = lean_string_dec_eq(v_str_427_, v___x_428_);
if (v___x_429_ == 0)
{
return v___x_429_;
}
else
{
lean_object* v___x_430_; uint8_t v___x_431_; 
v___x_430_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__5));
v___x_431_ = lean_string_dec_eq(v_str_426_, v___x_430_);
if (v___x_431_ == 0)
{
return v___x_431_;
}
else
{
lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_432_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__6));
v___x_433_ = lean_string_dec_eq(v_str_425_, v___x_432_);
if (v___x_433_ == 0)
{
return v___x_433_;
}
else
{
return v_suppressElabErrors_409_;
}
}
}
}
else
{
return v___y_410_;
}
}
default: 
{
return v___y_410_;
}
}
}
case 0:
{
lean_object* v_str_434_; lean_object* v___x_435_; uint8_t v___x_436_; 
v_str_434_ = lean_ctor_get(v_x_411_, 1);
v___x_435_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__7));
v___x_436_ = lean_string_dec_eq(v_str_434_, v___x_435_);
if (v___x_436_ == 0)
{
return v___x_436_;
}
else
{
return v_suppressElabErrors_409_;
}
}
default: 
{
return v___y_410_;
}
}
}
else
{
return v___y_410_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_409_ = stack[0].m_num;
uint8_t v___y_410_ = stack[1].m_num;
lean_object* v_x_411_ = stack[2].m_obj;
uint8_t v_res_437_;
v_res_437_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0(v_suppressElabErrors_409_, v___y_410_, v_x_411_);
stack->m_num = v_res_437_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___boxed(lean_object* v_suppressElabErrors_438_, lean_object* v___y_439_, lean_object* v_x_440_){
_start:
{
uint8_t v_suppressElabErrors_boxed_441_; uint8_t v___y_43620__boxed_442_; uint8_t v_res_443_; lean_object* v_r_444_; 
v_suppressElabErrors_boxed_441_ = lean_unbox(v_suppressElabErrors_438_);
v___y_43620__boxed_442_ = lean_unbox(v___y_439_);
v_res_443_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0(v_suppressElabErrors_boxed_441_, v___y_43620__boxed_442_, v_x_440_);
lean_dec(v_x_440_);
v_r_444_ = lean_box(v_res_443_);
return v_r_444_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44_spec__47(lean_object* v_msgData_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
lean_object* v___x_451_; lean_object* v_env_452_; uint8_t v___x_453_; lean_object* v_env_454_; lean_object* v___x_455_; lean_object* v_toCold_456_; lean_object* v_mctx_457_; lean_object* v_lctx_458_; lean_object* v_options_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_451_ = lean_st_ref_get(v___y_449_);
v_env_452_ = lean_ctor_get(v___x_451_, 0);
lean_inc_ref(v_env_452_);
lean_dec(v___x_451_);
v___x_453_ = 0;
v_env_454_ = l_Lean_Environment_setRecordingDeps(v_env_452_, v___x_453_);
v___x_455_ = lean_st_ref_get(v___y_447_);
v_toCold_456_ = lean_ctor_get(v___y_448_, 0);
v_mctx_457_ = lean_ctor_get(v___x_455_, 0);
lean_inc_ref(v_mctx_457_);
lean_dec(v___x_455_);
v_lctx_458_ = lean_ctor_get(v___y_446_, 2);
v_options_459_ = lean_ctor_get(v_toCold_456_, 2);
lean_inc_ref(v_options_459_);
lean_inc_ref(v_lctx_458_);
v___x_460_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_460_, 0, v_env_454_);
lean_ctor_set(v___x_460_, 1, v_mctx_457_);
lean_ctor_set(v___x_460_, 2, v_lctx_458_);
lean_ctor_set(v___x_460_, 3, v_options_459_);
v___x_461_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
lean_ctor_set(v___x_461_, 1, v_msgData_445_);
v___x_462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_462_, 0, v___x_461_);
return v___x_462_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44_spec__47_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_445_ = stack[0].m_obj;
lean_object* v___y_446_ = stack[1].m_obj;
lean_object* v___y_447_ = stack[2].m_obj;
lean_object* v___y_448_ = stack[3].m_obj;
lean_object* v___y_449_ = stack[4].m_obj;
lean_object* v_res_463_;
v_res_463_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44_spec__47(v_msgData_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
stack->m_obj
 = v_res_463_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44_spec__47___boxed(lean_object* v_msgData_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44_spec__47(v_msgData_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
return v_res_470_;
}
}
lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48(lean_object* v_ref_474_, lean_object* v_msgData_475_, uint8_t v_severity_476_, uint8_t v_isSilent_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
lean_object* v_a_484_; uint8_t v___y_488_; lean_object* v___y_489_; uint8_t v___y_490_; lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v___y_493_; lean_object* v___y_494_; lean_object* v_toCold_495_; lean_object* v___y_496_; lean_object* v___y_524_; lean_object* v___y_525_; uint8_t v___y_526_; uint8_t v___y_527_; lean_object* v___y_528_; uint8_t v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; uint8_t v___y_550_; lean_object* v___y_551_; lean_object* v___y_552_; uint8_t v___y_553_; uint8_t v___y_554_; lean_object* v___y_555_; lean_object* v___y_556_; uint8_t v___y_560_; uint8_t v___y_561_; uint8_t v___y_562_; uint8_t v___x_573_; uint8_t v___y_575_; uint8_t v___y_576_; uint8_t v___y_577_; uint8_t v___y_579_; uint8_t v___x_587_; 
v___x_573_ = 2;
v___x_587_ = l_Lean_instBEqMessageSeverity_beq(v_severity_476_, v___x_573_);
if (v___x_587_ == 0)
{
v___y_579_ = v___x_587_;
goto v___jp_578_;
}
else
{
uint8_t v___x_588_; 
lean_inc_ref(v_msgData_475_);
v___x_588_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_475_);
v___y_579_ = v___x_588_;
goto v___jp_578_;
}
v___jp_483_:
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_485_, 0, v_a_484_);
v___x_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
return v___x_486_;
}
v___jp_487_:
{
lean_object* v_currNamespace_497_; lean_object* v_openDecls_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v_env_503_; lean_object* v_nextMacroScope_504_; lean_object* v_ngen_505_; lean_object* v_auxDeclNGen_506_; lean_object* v_traceState_507_; lean_object* v_cache_508_; lean_object* v_recordedDeps_509_; lean_object* v_messages_510_; lean_object* v_infoState_511_; lean_object* v_snapshotTasks_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_522_; 
v_currNamespace_497_ = lean_ctor_get(v_toCold_495_, 4);
v_openDecls_498_ = lean_ctor_get(v_toCold_495_, 5);
lean_inc(v_openDecls_498_);
lean_inc(v_currNamespace_497_);
v___x_499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_499_, 0, v_currNamespace_497_);
lean_ctor_set(v___x_499_, 1, v_openDecls_498_);
v___x_500_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
lean_ctor_set(v___x_500_, 1, v___y_489_);
lean_inc_ref(v___y_493_);
lean_inc_ref(v___y_492_);
v___x_501_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_501_, 0, v___y_492_);
lean_ctor_set(v___x_501_, 1, v___y_494_);
lean_ctor_set(v___x_501_, 2, v___y_491_);
lean_ctor_set(v___x_501_, 3, v___y_493_);
lean_ctor_set(v___x_501_, 4, v___x_500_);
lean_ctor_set_uint8(v___x_501_, sizeof(void*)*5, v___y_490_);
lean_ctor_set_uint8(v___x_501_, sizeof(void*)*5 + 1, v___y_488_);
lean_ctor_set_uint8(v___x_501_, sizeof(void*)*5 + 2, v_isSilent_477_);
v___x_502_ = lean_st_ref_take(v___y_496_);
v_env_503_ = lean_ctor_get(v___x_502_, 0);
v_nextMacroScope_504_ = lean_ctor_get(v___x_502_, 1);
v_ngen_505_ = lean_ctor_get(v___x_502_, 2);
v_auxDeclNGen_506_ = lean_ctor_get(v___x_502_, 3);
v_traceState_507_ = lean_ctor_get(v___x_502_, 4);
v_cache_508_ = lean_ctor_get(v___x_502_, 5);
v_recordedDeps_509_ = lean_ctor_get(v___x_502_, 6);
v_messages_510_ = lean_ctor_get(v___x_502_, 7);
v_infoState_511_ = lean_ctor_get(v___x_502_, 8);
v_snapshotTasks_512_ = lean_ctor_get(v___x_502_, 9);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_522_ == 0)
{
v___x_514_ = v___x_502_;
v_isShared_515_ = v_isSharedCheck_522_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_snapshotTasks_512_);
lean_inc(v_infoState_511_);
lean_inc(v_messages_510_);
lean_inc(v_recordedDeps_509_);
lean_inc(v_cache_508_);
lean_inc(v_traceState_507_);
lean_inc(v_auxDeclNGen_506_);
lean_inc(v_ngen_505_);
lean_inc(v_nextMacroScope_504_);
lean_inc(v_env_503_);
lean_dec(v___x_502_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_522_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_519_; 
v___x_516_ = lean_box(0);
v___x_517_ = l_Lean_MessageLog_add(v___x_501_, v_messages_510_);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 7, v___x_517_);
v___x_519_ = v___x_514_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_env_503_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v_nextMacroScope_504_);
lean_ctor_set(v_reuseFailAlloc_521_, 2, v_ngen_505_);
lean_ctor_set(v_reuseFailAlloc_521_, 3, v_auxDeclNGen_506_);
lean_ctor_set(v_reuseFailAlloc_521_, 4, v_traceState_507_);
lean_ctor_set(v_reuseFailAlloc_521_, 5, v_cache_508_);
lean_ctor_set(v_reuseFailAlloc_521_, 6, v_recordedDeps_509_);
lean_ctor_set(v_reuseFailAlloc_521_, 7, v___x_517_);
lean_ctor_set(v_reuseFailAlloc_521_, 8, v_infoState_511_);
lean_ctor_set(v_reuseFailAlloc_521_, 9, v_snapshotTasks_512_);
v___x_519_ = v_reuseFailAlloc_521_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
lean_object* v___x_520_; 
v___x_520_ = lean_st_ref_put(v___y_496_, v___x_519_);
v_a_484_ = v___x_516_;
goto v___jp_483_;
}
}
}
v___jp_523_:
{
lean_object* v_fileName_532_; lean_object* v_fileMap_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v_a_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_548_; 
v_fileName_532_ = lean_ctor_get(v___y_530_, 0);
v_fileMap_533_ = lean_ctor_get(v___y_530_, 1);
v___x_534_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_475_);
v___x_535_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44_spec__47(v___x_534_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
v_a_536_ = lean_ctor_get(v___x_535_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_535_);
if (v_isSharedCheck_548_ == 0)
{
v___x_538_ = v___x_535_;
v_isShared_539_ = v_isSharedCheck_548_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_a_536_);
lean_dec(v___x_535_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_548_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_543_; 
lean_inc_ref_n(v_fileMap_533_, 2);
v___x_540_ = l_Lean_FileMap_toPosition(v_fileMap_533_, v___y_528_);
lean_dec(v___y_528_);
v___x_541_ = l_Lean_FileMap_toPosition(v_fileMap_533_, v___y_531_);
lean_dec(v___y_531_);
if (v_isShared_539_ == 0)
{
lean_ctor_set_tag(v___x_538_, 1);
lean_ctor_set(v___x_538_, 0, v___x_541_);
v___x_543_ = v___x_538_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_541_);
v___x_543_ = v_reuseFailAlloc_547_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_object* v___x_544_; 
v___x_544_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48___closed__0));
if (v___y_527_ == 0)
{
lean_dec_ref(v___y_524_);
v___y_488_ = v___y_526_;
v___y_489_ = v_a_536_;
v___y_490_ = v___y_529_;
v___y_491_ = v___x_543_;
v___y_492_ = v_fileName_532_;
v___y_493_ = v___x_544_;
v___y_494_ = v___x_540_;
v_toCold_495_ = v___y_525_;
v___y_496_ = v___y_481_;
goto v___jp_487_;
}
else
{
uint8_t v___x_545_; 
lean_inc(v_a_536_);
v___x_545_ = l_Lean_MessageData_hasTag(v___y_524_, v_a_536_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; 
lean_dec_ref(v___x_543_);
lean_dec_ref(v___x_540_);
lean_dec(v_a_536_);
v___x_546_ = lean_box(0);
v_a_484_ = v___x_546_;
goto v___jp_483_;
}
else
{
v___y_488_ = v___y_526_;
v___y_489_ = v_a_536_;
v___y_490_ = v___y_529_;
v___y_491_ = v___x_543_;
v___y_492_ = v_fileName_532_;
v___y_493_ = v___x_544_;
v___y_494_ = v___x_540_;
v_toCold_495_ = v___y_525_;
v___y_496_ = v___y_481_;
goto v___jp_487_;
}
}
}
}
}
v___jp_549_:
{
lean_object* v___x_557_; 
v___x_557_ = l_Lean_Syntax_getTailPos_x3f(v___y_555_, v___y_554_);
lean_dec(v___y_555_);
if (lean_obj_tag(v___x_557_) == 0)
{
lean_inc(v___y_556_);
v___y_524_ = v___y_551_;
v___y_525_ = v___y_552_;
v___y_526_ = v___y_553_;
v___y_527_ = v___y_550_;
v___y_528_ = v___y_556_;
v___y_529_ = v___y_554_;
v___y_530_ = v___y_552_;
v___y_531_ = v___y_556_;
goto v___jp_523_;
}
else
{
lean_object* v_val_558_; 
v_val_558_ = lean_ctor_get(v___x_557_, 0);
lean_inc(v_val_558_);
lean_dec_ref_known(v___x_557_, 1);
v___y_524_ = v___y_551_;
v___y_525_ = v___y_552_;
v___y_526_ = v___y_553_;
v___y_527_ = v___y_550_;
v___y_528_ = v___y_556_;
v___y_529_ = v___y_554_;
v___y_530_ = v___y_552_;
v___y_531_ = v_val_558_;
goto v___jp_523_;
}
}
v___jp_559_:
{
lean_object* v_toCold_563_; lean_object* v_ref_564_; uint8_t v_suppressElabErrors_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___f_568_; lean_object* v_ref_569_; lean_object* v___x_570_; 
v_toCold_563_ = lean_ctor_get(v___y_480_, 0);
v_ref_564_ = lean_ctor_get(v___y_480_, 2);
v_suppressElabErrors_565_ = lean_ctor_get_uint8(v___y_480_, sizeof(void*)*3 + 2);
v___x_566_ = lean_box(v_suppressElabErrors_565_);
v___x_567_ = lean_box(v___y_560_);
v___f_568_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___boxed), 3, 2);
lean_closure_set(v___f_568_, 0, v___x_566_);
lean_closure_set(v___f_568_, 1, v___x_567_);
v_ref_569_ = l_Lean_replaceRef(v_ref_474_, v_ref_564_);
v___x_570_ = l_Lean_Syntax_getPos_x3f(v_ref_569_, v___y_561_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v___x_571_; 
v___x_571_ = lean_unsigned_to_nat(0u);
v___y_550_ = v_suppressElabErrors_565_;
v___y_551_ = v___f_568_;
v___y_552_ = v_toCold_563_;
v___y_553_ = v___y_562_;
v___y_554_ = v___y_561_;
v___y_555_ = v_ref_569_;
v___y_556_ = v___x_571_;
goto v___jp_549_;
}
else
{
lean_object* v_val_572_; 
v_val_572_ = lean_ctor_get(v___x_570_, 0);
lean_inc(v_val_572_);
lean_dec_ref_known(v___x_570_, 1);
v___y_550_ = v_suppressElabErrors_565_;
v___y_551_ = v___f_568_;
v___y_552_ = v_toCold_563_;
v___y_553_ = v___y_562_;
v___y_554_ = v___y_561_;
v___y_555_ = v_ref_569_;
v___y_556_ = v_val_572_;
goto v___jp_549_;
}
}
v___jp_574_:
{
if (v___y_577_ == 0)
{
v___y_560_ = v___y_575_;
v___y_561_ = v___y_576_;
v___y_562_ = v_severity_476_;
goto v___jp_559_;
}
else
{
v___y_560_ = v___y_575_;
v___y_561_ = v___y_576_;
v___y_562_ = v___x_573_;
goto v___jp_559_;
}
}
v___jp_578_:
{
if (v___y_579_ == 0)
{
uint8_t v___x_580_; uint8_t v___x_581_; 
v___x_580_ = 1;
v___x_581_ = l_Lean_instBEqMessageSeverity_beq(v_severity_476_, v___x_580_);
if (v___x_581_ == 0)
{
v___y_575_ = v___y_579_;
v___y_576_ = v___y_579_;
v___y_577_ = v___x_581_;
goto v___jp_574_;
}
else
{
lean_object* v___x_582_; lean_object* v___x_583_; uint8_t v___x_584_; 
v___x_582_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_480_);
v___x_583_ = l_Lean_warningAsError;
v___x_584_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4(v___x_582_, v___x_583_);
lean_dec_ref(v___x_582_);
v___y_575_ = v___y_579_;
v___y_576_ = v___y_579_;
v___y_577_ = v___x_584_;
goto v___jp_574_;
}
}
else
{
lean_object* v___x_585_; lean_object* v___x_586_; 
lean_dec_ref(v_msgData_475_);
v___x_585_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48___closed__1));
v___x_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
return v___x_586_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_474_ = stack[0].m_obj;
lean_object* v_msgData_475_ = stack[1].m_obj;
uint8_t v_severity_476_ = stack[2].m_num;
uint8_t v_isSilent_477_ = stack[3].m_num;
lean_object* v___y_478_ = stack[4].m_obj;
lean_object* v___y_479_ = stack[5].m_obj;
lean_object* v___y_480_ = stack[6].m_obj;
lean_object* v___y_481_ = stack[7].m_obj;
lean_object* v_res_589_;
v_res_589_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48(v_ref_474_, v_msgData_475_, v_severity_476_, v_isSilent_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
stack->m_obj
 = v_res_589_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48___boxed(lean_object* v_ref_590_, lean_object* v_msgData_591_, lean_object* v_severity_592_, lean_object* v_isSilent_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
uint8_t v_severity_boxed_599_; uint8_t v_isSilent_boxed_600_; lean_object* v_res_601_; 
v_severity_boxed_599_ = lean_unbox(v_severity_592_);
v_isSilent_boxed_600_ = lean_unbox(v_isSilent_593_);
v_res_601_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48(v_ref_590_, v_msgData_591_, v_severity_boxed_599_, v_isSilent_boxed_600_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
lean_dec(v___y_595_);
lean_dec_ref(v___y_594_);
lean_dec(v_ref_590_);
return v_res_601_;
}
}
lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46(lean_object* v_msgData_602_, uint8_t v_severity_603_, uint8_t v_isSilent_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
lean_object* v_ref_610_; lean_object* v___x_611_; 
v_ref_610_ = lean_ctor_get(v___y_607_, 2);
v___x_611_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48(v_ref_610_, v_msgData_602_, v_severity_603_, v_isSilent_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_);
return v___x_611_;
}
}
LEAN_EXPORT void l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_602_ = stack[0].m_obj;
uint8_t v_severity_603_ = stack[1].m_num;
uint8_t v_isSilent_604_ = stack[2].m_num;
lean_object* v___y_605_ = stack[3].m_obj;
lean_object* v___y_606_ = stack[4].m_obj;
lean_object* v___y_607_ = stack[5].m_obj;
lean_object* v___y_608_ = stack[6].m_obj;
lean_object* v_res_612_;
v_res_612_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46(v_msgData_602_, v_severity_603_, v_isSilent_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_);
stack->m_obj
 = v_res_612_;
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46___boxed(lean_object* v_msgData_613_, lean_object* v_severity_614_, lean_object* v_isSilent_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
uint8_t v_severity_boxed_621_; uint8_t v_isSilent_boxed_622_; lean_object* v_res_623_; 
v_severity_boxed_621_ = lean_unbox(v_severity_614_);
v_isSilent_boxed_622_ = lean_unbox(v_isSilent_615_);
v_res_623_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46(v_msgData_613_, v_severity_boxed_621_, v_isSilent_boxed_622_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
return v_res_623_;
}
}
lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44(lean_object* v_msgData_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_){
_start:
{
uint8_t v___x_630_; uint8_t v___x_631_; lean_object* v___x_632_; 
v___x_630_ = 1;
v___x_631_ = 0;
v___x_632_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46(v_msgData_624_, v___x_630_, v___x_631_, v___y_625_, v___y_626_, v___y_627_, v___y_628_);
return v___x_632_;
}
}
LEAN_EXPORT void l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_624_ = stack[0].m_obj;
lean_object* v___y_625_ = stack[1].m_obj;
lean_object* v___y_626_ = stack[2].m_obj;
lean_object* v___y_627_ = stack[3].m_obj;
lean_object* v___y_628_ = stack[4].m_obj;
lean_object* v_res_633_;
v_res_633_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44(v_msgData_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_);
stack->m_obj
 = v_res_633_;
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44___boxed(lean_object* v_msgData_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44(v_msgData_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
return v_res_640_;
}
}
lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43___redArg(lean_object* v_opt_641_, lean_object* v___y_642_){
_start:
{
lean_object* v___x_644_; uint8_t v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_644_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_642_);
v___x_645_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4(v___x_644_, v_opt_641_);
lean_dec_ref(v___x_644_);
v___x_646_ = lean_box(v___x_645_);
v___x_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_647_, 0, v___x_646_);
v___x_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_648_, 0, v___x_647_);
return v___x_648_;
}
}
LEAN_EXPORT void l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_opt_641_ = stack[0].m_obj;
lean_object* v___y_642_ = stack[1].m_obj;
lean_object* v_res_649_;
v_res_649_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43___redArg(v_opt_641_, v___y_642_);
stack->m_obj
 = v_res_649_;
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43___redArg___boxed(lean_object* v_opt_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43___redArg(v_opt_650_, v___y_651_);
lean_dec_ref(v___y_651_);
lean_dec_ref(v_opt_650_);
return v_res_653_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___closed__1(void){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_655_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___closed__0));
v___x_656_ = l_Lean_stringToMessageData(v___x_655_);
return v___x_656_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___closed__3(void){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___closed__2));
v___x_659_ = l_Lean_stringToMessageData(v___x_658_);
return v___x_659_;
}
}
lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40(lean_object* v_id_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
lean_object* v___x_666_; lean_object* v_env_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_690_; 
v___x_666_ = lean_st_ref_get(v___y_664_);
v_env_667_ = lean_ctor_get(v___x_666_, 0);
lean_inc_ref(v_env_667_);
lean_dec(v___x_666_);
v___x_668_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_669_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43___redArg(v___x_668_, v___y_663_);
v_a_670_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_690_ == 0)
{
v___x_672_ = v___x_669_;
v_isShared_673_ = v_isSharedCheck_690_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_669_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_690_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
uint8_t v_isExporting_679_; 
v_isExporting_679_ = lean_ctor_get_uint8(v_env_667_, sizeof(void*)*13);
lean_dec_ref(v_env_667_);
if (v_isExporting_679_ == 0)
{
lean_dec(v_a_670_);
lean_dec(v_id_660_);
goto v___jp_674_;
}
else
{
lean_object* v_val_680_; uint8_t v___x_681_; 
v_val_680_ = lean_ctor_get(v_a_670_, 0);
lean_inc(v_val_680_);
lean_dec(v_a_670_);
v___x_681_ = l_Lean_isPrivateName(v_id_660_);
if (v___x_681_ == 0)
{
lean_dec(v_val_680_);
lean_dec(v_id_660_);
goto v___jp_674_;
}
else
{
uint8_t v___x_682_; 
v___x_682_ = lean_unbox(v_val_680_);
lean_dec(v_val_680_);
if (v___x_682_ == 0)
{
lean_dec(v_id_660_);
goto v___jp_674_;
}
else
{
lean_object* v___x_683_; uint8_t v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
lean_del_object(v___x_672_);
v___x_683_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___closed__1);
v___x_684_ = 0;
v___x_685_ = l_Lean_MessageData_ofConstName(v_id_660_, v___x_684_);
v___x_686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_686_, 0, v___x_683_);
lean_ctor_set(v___x_686_, 1, v___x_685_);
v___x_687_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___closed__3);
v___x_688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_688_, 0, v___x_686_);
lean_ctor_set(v___x_688_, 1, v___x_687_);
v___x_689_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44(v___x_688_, v___y_661_, v___y_662_, v___y_663_, v___y_664_);
return v___x_689_;
}
}
}
v___jp_674_:
{
lean_object* v___x_675_; lean_object* v___x_677_; 
v___x_675_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48___closed__1));
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 0, v___x_675_);
v___x_677_ = v___x_672_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_675_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_660_ = stack[0].m_obj;
lean_object* v___y_661_ = stack[1].m_obj;
lean_object* v___y_662_ = stack[2].m_obj;
lean_object* v___y_663_ = stack[3].m_obj;
lean_object* v___y_664_ = stack[4].m_obj;
lean_object* v_res_691_;
v_res_691_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40(v_id_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_);
stack->m_obj
 = v_res_691_;
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___boxed(lean_object* v_id_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40(v_id_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__31(lean_object* v_x_699_){
_start:
{
if (lean_obj_tag(v_x_699_) == 0)
{
lean_object* v___x_700_; 
v___x_700_ = lean_box(0);
return v___x_700_;
}
else
{
lean_object* v_head_701_; lean_object* v_tail_702_; lean_object* v_fst_703_; uint8_t v___x_704_; 
v_head_701_ = lean_ctor_get(v_x_699_, 0);
v_tail_702_ = lean_ctor_get(v_x_699_, 1);
v_fst_703_ = lean_ctor_get(v_head_701_, 0);
v___x_704_ = l_Lean_isPrivateName(v_fst_703_);
if (v___x_704_ == 0)
{
v_x_699_ = v_tail_702_;
goto _start;
}
else
{
lean_object* v___x_706_; 
lean_inc(v_head_701_);
v___x_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_706_, 0, v_head_701_);
return v___x_706_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__31___boxed(lean_object* v_x_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__31(v_x_707_);
lean_dec(v_x_707_);
return v_res_708_;
}
}
lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34(lean_object* v_id_709_, uint8_t v_enableLog_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
lean_object* v___x_716_; lean_object* v_toCold_717_; lean_object* v_env_718_; lean_object* v_currNamespace_719_; lean_object* v_openDecls_720_; lean_object* v___x_721_; lean_object* v_res_722_; lean_object* v___x_726_; 
v___x_716_ = lean_st_ref_get(v___y_714_);
v_toCold_717_ = lean_ctor_get(v___y_713_, 0);
v_env_718_ = lean_ctor_get(v___x_716_, 0);
lean_inc_ref(v_env_718_);
lean_dec(v___x_716_);
v_currNamespace_719_ = lean_ctor_get(v_toCold_717_, 4);
v_openDecls_720_ = lean_ctor_get(v_toCold_717_, 5);
v___x_721_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_713_);
lean_inc(v_openDecls_720_);
lean_inc(v_currNamespace_719_);
v_res_722_ = l_Lean_ResolveName_resolveGlobalName(v_env_718_, v___x_721_, v_currNamespace_719_, v_openDecls_720_, v_id_709_);
lean_dec_ref(v___x_721_);
v___x_726_ = lean_st_ref_get(v___y_714_);
if (v_enableLog_710_ == 0)
{
lean_dec(v___x_726_);
goto v___jp_723_;
}
else
{
lean_object* v_env_727_; uint8_t v_isExporting_728_; 
v_env_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc_ref(v_env_727_);
lean_dec(v___x_726_);
v_isExporting_728_ = lean_ctor_get_uint8(v_env_727_, sizeof(void*)*13);
lean_dec_ref(v_env_727_);
if (v_isExporting_728_ == 0)
{
goto v___jp_723_;
}
else
{
lean_object* v___x_729_; 
v___x_729_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__31(v_res_722_);
if (lean_obj_tag(v___x_729_) == 1)
{
lean_object* v_val_730_; lean_object* v_fst_731_; lean_object* v___x_732_; 
v_val_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_val_730_);
lean_dec_ref_known(v___x_729_, 1);
v_fst_731_ = lean_ctor_get(v_val_730_, 0);
lean_inc(v_fst_731_);
lean_dec(v_val_730_);
v___x_732_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40(v_fst_731_, v___y_711_, v___y_712_, v___y_713_, v___y_714_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_741_; 
v_a_733_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_741_ == 0)
{
v___x_735_ = v___x_732_;
v_isShared_736_ = v_isSharedCheck_741_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_732_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_741_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
if (lean_obj_tag(v_a_733_) == 0)
{
lean_object* v___x_737_; lean_object* v___x_739_; 
lean_dec(v_res_722_);
v___x_737_ = lean_box(0);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 0, v___x_737_);
v___x_739_ = v___x_735_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_737_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
else
{
lean_dec_ref_known(v_a_733_, 1);
lean_del_object(v___x_735_);
goto v___jp_723_;
}
}
}
else
{
lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_749_; 
lean_dec(v_res_722_);
v_a_742_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_749_ == 0)
{
v___x_744_ = v___x_732_;
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_a_742_);
lean_dec(v___x_732_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_747_; 
if (v_isShared_745_ == 0)
{
v___x_747_ = v___x_744_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_a_742_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
else
{
lean_dec(v___x_729_);
goto v___jp_723_;
}
}
}
v___jp_723_:
{
lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_724_, 0, v_res_722_);
v___x_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
return v___x_725_;
}
}
}
LEAN_EXPORT void l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_709_ = stack[0].m_obj;
uint8_t v_enableLog_710_ = stack[1].m_num;
lean_object* v___y_711_ = stack[2].m_obj;
lean_object* v___y_712_ = stack[3].m_obj;
lean_object* v___y_713_ = stack[4].m_obj;
lean_object* v___y_714_ = stack[5].m_obj;
lean_object* v_res_750_;
v_res_750_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34(v_id_709_, v_enableLog_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_);
stack->m_obj
 = v_res_750_;
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34___boxed(lean_object* v_id_751_, lean_object* v_enableLog_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
uint8_t v_enableLog_boxed_758_; lean_object* v_res_759_; 
v_enableLog_boxed_758_ = lean_unbox(v_enableLog_752_);
v_res_759_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34(v_id_751_, v_enableLog_boxed_758_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
return v_res_759_;
}
}
lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22___lam__0(lean_object* v___x_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_766_, 0, v___x_760_);
return v___x_766_;
}
}
LEAN_EXPORT void l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_760_ = stack[0].m_obj;
lean_object* v___y_761_ = stack[1].m_obj;
lean_object* v___y_762_ = stack[2].m_obj;
lean_object* v___y_763_ = stack[3].m_obj;
lean_object* v___y_764_ = stack[4].m_obj;
lean_object* v_res_767_;
v_res_767_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22___lam__0(v___x_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_);
stack->m_obj
 = v_res_767_;
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22___lam__0___boxed(lean_object* v___x_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22___lam__0(v___x_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
return v_res_774_;
}
}
lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25(lean_object* v_n_u2080_779_, lean_object* v_filter_780_, lean_object* v_view_x3f_781_, lean_object* v_n_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_858_; 
if (lean_obj_tag(v_view_x3f_781_) == 1)
{
lean_object* v_val_885_; lean_object* v_imported_886_; lean_object* v_ctx_887_; lean_object* v_scopes_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_896_; 
v_val_885_ = lean_ctor_get(v_view_x3f_781_, 0);
lean_inc(v_val_885_);
lean_dec_ref_known(v_view_x3f_781_, 1);
v_imported_886_ = lean_ctor_get(v_val_885_, 1);
v_ctx_887_ = lean_ctor_get(v_val_885_, 2);
v_scopes_888_ = lean_ctor_get(v_val_885_, 3);
v_isSharedCheck_896_ = !lean_is_exclusive(v_val_885_);
if (v_isSharedCheck_896_ == 0)
{
lean_object* v_unused_897_; 
v_unused_897_ = lean_ctor_get(v_val_885_, 0);
lean_dec(v_unused_897_);
v___x_890_ = v_val_885_;
v_isShared_891_ = v_isSharedCheck_896_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_scopes_888_);
lean_inc(v_ctx_887_);
lean_inc(v_imported_886_);
lean_dec(v_val_885_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_896_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 0, v_n_782_);
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_n_782_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v_imported_886_);
lean_ctor_set(v_reuseFailAlloc_895_, 2, v_ctx_887_);
lean_ctor_set(v_reuseFailAlloc_895_, 3, v_scopes_888_);
v___x_893_ = v_reuseFailAlloc_895_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
lean_object* v___x_894_; 
v___x_894_ = l_Lean_MacroScopesView_review(v___x_893_);
v___y_858_ = v___x_894_;
goto v___jp_857_;
}
}
}
else
{
lean_dec(v_view_x3f_781_);
v___y_858_ = v_n_782_;
goto v___jp_857_;
}
v___jp_788_:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = lean_box(0);
v___x_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
return v___x_790_;
}
v___jp_791_:
{
lean_object* v___x_794_; 
lean_inc_ref(v___y_793_);
lean_inc(v___y_786_);
lean_inc_ref(v___y_785_);
lean_inc(v___y_784_);
lean_inc_ref(v___y_783_);
v___x_794_ = lean_apply_5(v___y_793_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, lean_box(0));
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_814_; 
v_a_795_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_814_ == 0)
{
v___x_797_ = v___x_794_;
v_isShared_798_ = v_isSharedCheck_814_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_794_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_814_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
if (lean_obj_tag(v_a_795_) == 0)
{
lean_object* v___x_799_; lean_object* v___x_801_; 
lean_dec(v___y_792_);
v___x_799_ = lean_box(0);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 0, v___x_799_);
v___x_801_ = v___x_797_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v___x_799_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
else
{
lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_812_; 
v_isSharedCheck_812_ = !lean_is_exclusive(v_a_795_);
if (v_isSharedCheck_812_ == 0)
{
lean_object* v_unused_813_; 
v_unused_813_ = lean_ctor_get(v_a_795_, 0);
lean_dec(v_unused_813_);
v___x_804_ = v_a_795_;
v_isShared_805_ = v_isSharedCheck_812_;
goto v_resetjp_803_;
}
else
{
lean_dec(v_a_795_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_812_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_807_; 
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 0, v___y_792_);
v___x_807_ = v___x_804_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___y_792_);
v___x_807_ = v_reuseFailAlloc_811_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
lean_object* v___x_809_; 
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 0, v___x_807_);
v___x_809_ = v___x_797_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v___x_807_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
}
}
}
else
{
lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_822_; 
lean_dec(v___y_792_);
v_a_815_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_822_ == 0)
{
v___x_817_ = v___x_794_;
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v___x_794_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_820_; 
if (v_isShared_818_ == 0)
{
v___x_820_ = v___x_817_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_a_815_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
v___jp_823_:
{
lean_object* v___x_826_; 
lean_inc_ref(v___y_825_);
lean_inc(v___y_786_);
lean_inc_ref(v___y_785_);
lean_inc(v___y_784_);
lean_inc_ref(v___y_783_);
v___x_826_ = lean_apply_5(v___y_825_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, lean_box(0));
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_848_; 
v_a_827_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_848_ == 0)
{
v___x_829_ = v___x_826_;
v_isShared_830_ = v_isSharedCheck_848_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_826_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_848_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
if (lean_obj_tag(v_a_827_) == 0)
{
lean_object* v___x_831_; lean_object* v___x_833_; 
lean_dec(v___y_824_);
lean_dec_ref(v_filter_780_);
v___x_831_ = lean_box(0);
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 0, v___x_831_);
v___x_833_ = v___x_829_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v___x_831_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
else
{
lean_object* v___x_835_; 
lean_dec_ref_known(v_a_827_, 1);
lean_del_object(v___x_829_);
lean_inc(v___y_786_);
lean_inc_ref(v___y_785_);
lean_inc(v___y_784_);
lean_inc_ref(v___y_783_);
lean_inc(v___y_824_);
v___x_835_ = lean_apply_6(v_filter_780_, v___y_824_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, lean_box(0));
if (lean_obj_tag(v___x_835_) == 0)
{
lean_object* v_a_836_; uint8_t v___x_837_; 
v_a_836_ = lean_ctor_get(v___x_835_, 0);
lean_inc(v_a_836_);
lean_dec_ref_known(v___x_835_, 1);
v___x_837_ = lean_unbox(v_a_836_);
lean_dec(v_a_836_);
if (v___x_837_ == 0)
{
lean_object* v___f_838_; 
v___f_838_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__0));
v___y_792_ = v___y_824_;
v___y_793_ = v___f_838_;
goto v___jp_791_;
}
else
{
lean_object* v___f_839_; 
v___f_839_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__1));
v___y_792_ = v___y_824_;
v___y_793_ = v___f_839_;
goto v___jp_791_;
}
}
else
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
lean_dec(v___y_824_);
v_a_840_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_835_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_835_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_840_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
}
}
else
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_856_; 
lean_dec(v___y_824_);
lean_dec_ref(v_filter_780_);
v_a_849_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_856_ == 0)
{
v___x_851_ = v___x_826_;
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_826_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_854_; 
if (v_isShared_852_ == 0)
{
v___x_854_ = v___x_851_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_a_849_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
v___jp_857_:
{
uint8_t v___x_859_; lean_object* v___x_860_; 
v___x_859_ = 0;
lean_inc(v___y_858_);
v___x_860_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34(v___y_858_, v___x_859_, v___y_783_, v___y_784_, v___y_785_, v___y_786_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_876_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_876_ == 0)
{
v___x_863_ = v___x_860_;
v_isShared_864_ = v_isSharedCheck_876_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_860_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_876_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
if (lean_obj_tag(v_a_861_) == 0)
{
lean_object* v___x_865_; lean_object* v___x_867_; 
lean_dec(v___y_858_);
lean_dec_ref(v_filter_780_);
v___x_865_ = lean_box(0);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v___x_865_);
v___x_867_ = v___x_863_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v___x_865_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
else
{
lean_object* v_val_869_; 
lean_del_object(v___x_863_);
v_val_869_ = lean_ctor_get(v_a_861_, 0);
lean_inc(v_val_869_);
lean_dec_ref_known(v_a_861_, 1);
if (lean_obj_tag(v_val_869_) == 1)
{
lean_object* v_head_870_; lean_object* v_tail_871_; 
v_head_870_ = lean_ctor_get(v_val_869_, 0);
lean_inc(v_head_870_);
v_tail_871_ = lean_ctor_get(v_val_869_, 1);
lean_inc(v_tail_871_);
lean_dec_ref_known(v_val_869_, 2);
if (lean_obj_tag(v_tail_871_) == 0)
{
lean_object* v_fst_872_; uint8_t v___x_873_; 
v_fst_872_ = lean_ctor_get(v_head_870_, 0);
lean_inc(v_fst_872_);
lean_dec(v_head_870_);
v___x_873_ = lean_name_eq(v_fst_872_, v_n_u2080_779_);
lean_dec(v_fst_872_);
if (v___x_873_ == 0)
{
lean_object* v___f_874_; 
v___f_874_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__0));
v___y_824_ = v___y_858_;
v___y_825_ = v___f_874_;
goto v___jp_823_;
}
else
{
lean_object* v___f_875_; 
v___f_875_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__1));
v___y_824_ = v___y_858_;
v___y_825_ = v___f_875_;
goto v___jp_823_;
}
}
else
{
lean_dec(v_tail_871_);
lean_dec(v_head_870_);
lean_dec(v___y_858_);
lean_dec_ref(v_filter_780_);
goto v___jp_788_;
}
}
else
{
lean_dec(v_val_869_);
lean_dec(v___y_858_);
lean_dec_ref(v_filter_780_);
goto v___jp_788_;
}
}
}
}
else
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_884_; 
lean_dec(v___y_858_);
lean_dec_ref(v_filter_780_);
v_a_877_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_884_ == 0)
{
v___x_879_ = v___x_860_;
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_860_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_882_; 
if (v_isShared_880_ == 0)
{
v___x_882_ = v___x_879_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_877_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_u2080_779_ = stack[0].m_obj;
lean_object* v_filter_780_ = stack[1].m_obj;
lean_object* v_view_x3f_781_ = stack[2].m_obj;
lean_object* v_n_782_ = stack[3].m_obj;
lean_object* v___y_783_ = stack[4].m_obj;
lean_object* v___y_784_ = stack[5].m_obj;
lean_object* v___y_785_ = stack[6].m_obj;
lean_object* v___y_786_ = stack[7].m_obj;
lean_object* v_res_898_;
v_res_898_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25(v_n_u2080_779_, v_filter_780_, v_view_x3f_781_, v_n_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_);
stack->m_obj
 = v_res_898_;
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25___boxed(lean_object* v_n_u2080_899_, lean_object* v_filter_900_, lean_object* v_view_x3f_901_, lean_object* v_n_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25(v_n_u2080_899_, v_filter_900_, v_view_x3f_901_, v_n_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v_n_u2080_899_);
return v_res_908_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30___redArg(lean_object* v_n_u2080_909_, lean_object* v_filter_910_, lean_object* v_view_x3f_911_, lean_object* v_as_x27_912_, lean_object* v_b_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
if (lean_obj_tag(v_as_x27_912_) == 0)
{
lean_object* v___x_919_; lean_object* v___x_920_; 
lean_dec(v_view_x3f_911_);
lean_dec_ref(v_filter_910_);
v___x_919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_919_, 0, v_b_913_);
v___x_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_920_, 0, v___x_919_);
return v___x_920_;
}
else
{
lean_object* v_head_921_; lean_object* v_tail_922_; lean_object* v_snd_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_961_; 
v_head_921_ = lean_ctor_get(v_as_x27_912_, 0);
v_tail_922_ = lean_ctor_get(v_as_x27_912_, 1);
v_snd_923_ = lean_ctor_get(v_b_913_, 1);
v_isSharedCheck_961_ = !lean_is_exclusive(v_b_913_);
if (v_isSharedCheck_961_ == 0)
{
lean_object* v_unused_962_; 
v_unused_962_ = lean_ctor_get(v_b_913_, 0);
lean_dec(v_unused_962_);
v___x_925_ = v_b_913_;
v_isShared_926_ = v_isSharedCheck_961_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_snd_923_);
lean_dec(v_b_913_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_961_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_927_ = lean_box(0);
v___x_928_ = l_Lean_Name_appendCore(v_head_921_, v_snd_923_);
lean_inc(v___x_928_);
lean_inc(v_view_x3f_911_);
lean_inc_ref(v_filter_910_);
v___x_929_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25(v_n_u2080_909_, v_filter_910_, v_view_x3f_911_, v___x_928_, v___y_914_, v___y_915_, v___y_916_, v___y_917_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_952_; 
v_a_930_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_952_ == 0)
{
v___x_932_ = v___x_929_;
v_isShared_933_ = v_isSharedCheck_952_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v___x_929_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_952_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
if (lean_obj_tag(v_a_930_) == 0)
{
lean_object* v___x_935_; 
lean_del_object(v___x_932_);
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 1, v___x_928_);
lean_ctor_set(v___x_925_, 0, v___x_927_);
v___x_935_ = v___x_925_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_927_);
lean_ctor_set(v_reuseFailAlloc_937_, 1, v___x_928_);
v___x_935_ = v_reuseFailAlloc_937_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
v_as_x27_912_ = v_tail_922_;
v_b_913_ = v___x_935_;
goto _start;
}
}
else
{
lean_object* v___x_939_; 
lean_dec(v_view_x3f_911_);
lean_dec_ref(v_filter_910_);
lean_inc_ref(v_a_930_);
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 1, v___x_928_);
lean_ctor_set(v___x_925_, 0, v_a_930_);
v___x_939_ = v___x_925_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_a_930_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v___x_928_);
v___x_939_ = v_reuseFailAlloc_951_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_949_; 
v_isSharedCheck_949_ = !lean_is_exclusive(v_a_930_);
if (v_isSharedCheck_949_ == 0)
{
lean_object* v_unused_950_; 
v_unused_950_ = lean_ctor_get(v_a_930_, 0);
lean_dec(v_unused_950_);
v___x_941_ = v_a_930_;
v_isShared_942_ = v_isSharedCheck_949_;
goto v_resetjp_940_;
}
else
{
lean_dec(v_a_930_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_949_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_944_; 
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 0, v___x_939_);
v___x_944_ = v___x_941_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_939_);
v___x_944_ = v_reuseFailAlloc_948_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
lean_object* v___x_946_; 
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 0, v___x_944_);
v___x_946_ = v___x_932_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_944_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_960_; 
lean_dec(v___x_928_);
lean_del_object(v___x_925_);
lean_dec(v_view_x3f_911_);
lean_dec_ref(v_filter_910_);
v_a_953_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_960_ == 0)
{
v___x_955_ = v___x_929_;
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___x_929_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_958_; 
if (v_isShared_956_ == 0)
{
v___x_958_ = v___x_955_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_a_953_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_u2080_909_ = stack[0].m_obj;
lean_object* v_filter_910_ = stack[1].m_obj;
lean_object* v_view_x3f_911_ = stack[2].m_obj;
lean_object* v_as_x27_912_ = stack[3].m_obj;
lean_object* v_b_913_ = stack[4].m_obj;
lean_object* v___y_914_ = stack[5].m_obj;
lean_object* v___y_915_ = stack[6].m_obj;
lean_object* v___y_916_ = stack[7].m_obj;
lean_object* v___y_917_ = stack[8].m_obj;
lean_object* v_res_963_;
v_res_963_ = l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30___redArg(v_n_u2080_909_, v_filter_910_, v_view_x3f_911_, v_as_x27_912_, v_b_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_);
stack->m_obj
 = v_res_963_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30___redArg___boxed(lean_object* v_n_u2080_964_, lean_object* v_filter_965_, lean_object* v_view_x3f_966_, lean_object* v_as_x27_967_, lean_object* v_b_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30___redArg(v_n_u2080_964_, v_filter_965_, v_view_x3f_966_, v_as_x27_967_, v_b_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v_as_x27_967_);
lean_dec(v_n_u2080_964_);
return v_res_974_;
}
}
lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22(lean_object* v_n_u2080_978_, lean_object* v_filter_979_, lean_object* v_view_x3f_980_, lean_object* v_n_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v___y_988_; uint8_t v___x_1029_; 
v___x_1029_ = l_Lean_Name_hasMacroScopes(v_n_981_);
if (v___x_1029_ == 0)
{
lean_object* v___f_1030_; 
v___f_1030_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__1));
v___y_988_ = v___f_1030_;
goto v___jp_987_;
}
else
{
lean_object* v___f_1031_; 
v___f_1031_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__0));
v___y_988_ = v___f_1031_;
goto v___jp_987_;
}
v___jp_987_:
{
lean_object* v___x_989_; 
lean_inc_ref(v___y_988_);
lean_inc(v___y_985_);
lean_inc_ref(v___y_984_);
lean_inc(v___y_983_);
lean_inc_ref(v___y_982_);
v___x_989_ = lean_apply_5(v___y_988_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, lean_box(0));
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1020_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_992_ = v___x_989_;
v_isShared_993_ = v_isSharedCheck_1020_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_989_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1020_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
if (lean_obj_tag(v_a_990_) == 0)
{
lean_object* v___x_994_; lean_object* v___x_996_; 
lean_dec(v_n_981_);
lean_dec(v_view_x3f_980_);
lean_dec_ref(v_filter_979_);
v___x_994_ = lean_box(0);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 0, v___x_994_);
v___x_996_ = v___x_992_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_994_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
else
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
lean_dec_ref_known(v_a_990_, 1);
lean_del_object(v___x_992_);
v___x_998_ = l_Lean_privateToUserName(v_n_981_);
v___x_999_ = l_Lean_Name_componentsRev(v___x_998_);
v___x_1000_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22___closed__0));
v___x_1001_ = l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30___redArg(v_n_u2080_978_, v_filter_979_, v_view_x3f_980_, v___x_999_, v___x_1000_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
lean_dec(v___x_999_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1011_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1004_ = v___x_1001_;
v_isShared_1005_ = v_isSharedCheck_1011_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_1001_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1011_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v_val_1006_; lean_object* v_fst_1007_; lean_object* v___x_1009_; 
v_val_1006_ = lean_ctor_get(v_a_1002_, 0);
lean_inc(v_val_1006_);
lean_dec(v_a_1002_);
v_fst_1007_ = lean_ctor_get(v_val_1006_, 0);
lean_inc(v_fst_1007_);
lean_dec(v_val_1006_);
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 0, v_fst_1007_);
v___x_1009_ = v___x_1004_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_fst_1007_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
else
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1019_; 
v_a_1012_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1014_ = v___x_1001_;
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_1001_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1017_; 
if (v_isShared_1015_ == 0)
{
v___x_1017_ = v___x_1014_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_a_1012_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
}
}
}
else
{
lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1028_; 
lean_dec(v_n_981_);
lean_dec(v_view_x3f_980_);
lean_dec_ref(v_filter_979_);
v_a_1021_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1023_ = v___x_989_;
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_989_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
if (v_isShared_1024_ == 0)
{
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_a_1021_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_u2080_978_ = stack[0].m_obj;
lean_object* v_filter_979_ = stack[1].m_obj;
lean_object* v_view_x3f_980_ = stack[2].m_obj;
lean_object* v_n_981_ = stack[3].m_obj;
lean_object* v___y_982_ = stack[4].m_obj;
lean_object* v___y_983_ = stack[5].m_obj;
lean_object* v___y_984_ = stack[6].m_obj;
lean_object* v___y_985_ = stack[7].m_obj;
lean_object* v_res_1032_;
v_res_1032_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22(v_n_u2080_978_, v_filter_979_, v_view_x3f_980_, v_n_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
stack->m_obj
 = v_res_1032_;
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22___boxed(lean_object* v_n_u2080_1033_, lean_object* v_filter_1034_, lean_object* v_view_x3f_1035_, lean_object* v_n_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22(v_n_u2080_1033_, v_filter_1034_, v_view_x3f_1035_, v_n_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v_n_u2080_1033_);
return v_res_1042_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__23(lean_object* v_n_u2080_1043_, lean_object* v_filter_1044_, lean_object* v_as_1045_, lean_object* v_i_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v___x_1052_; uint8_t v___x_1053_; 
v___x_1052_ = lean_array_get_size(v_as_1045_);
v___x_1053_ = lean_nat_dec_lt(v_i_1046_, v___x_1052_);
if (v___x_1053_ == 0)
{
lean_object* v___x_1054_; lean_object* v___x_1055_; 
lean_dec(v_i_1046_);
lean_dec_ref(v_filter_1044_);
v___x_1054_ = lean_box(0);
v___x_1055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1054_);
return v___x_1055_;
}
else
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1056_ = lean_box(0);
v___x_1057_ = lean_array_fget_borrowed(v_as_1045_, v_i_1046_);
lean_inc(v___x_1057_);
lean_inc_ref(v_filter_1044_);
v___x_1058_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22(v_n_u2080_1043_, v_filter_1044_, v___x_1056_, v___x_1057_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_object* v_a_1059_; 
v_a_1059_ = lean_ctor_get(v___x_1058_, 0);
if (lean_obj_tag(v_a_1059_) == 0)
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
lean_dec_ref_known(v___x_1058_, 1);
v___x_1060_ = lean_unsigned_to_nat(1u);
v___x_1061_ = lean_nat_add(v_i_1046_, v___x_1060_);
lean_dec(v_i_1046_);
v_i_1046_ = v___x_1061_;
goto _start;
}
else
{
lean_dec(v_i_1046_);
lean_dec_ref(v_filter_1044_);
return v___x_1058_;
}
}
else
{
lean_dec(v_i_1046_);
lean_dec_ref(v_filter_1044_);
return v___x_1058_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__23_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_u2080_1043_ = stack[0].m_obj;
lean_object* v_filter_1044_ = stack[1].m_obj;
lean_object* v_as_1045_ = stack[2].m_obj;
lean_object* v_i_1046_ = stack[3].m_obj;
lean_object* v___y_1047_ = stack[4].m_obj;
lean_object* v___y_1048_ = stack[5].m_obj;
lean_object* v___y_1049_ = stack[6].m_obj;
lean_object* v___y_1050_ = stack[7].m_obj;
lean_object* v_res_1063_;
v_res_1063_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__23(v_n_u2080_1043_, v_filter_1044_, v_as_1045_, v_i_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
stack->m_obj
 = v_res_1063_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__23___boxed(lean_object* v_n_u2080_1064_, lean_object* v_filter_1065_, lean_object* v_as_1066_, lean_object* v_i_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__23(v_n_u2080_1064_, v_filter_1065_, v_as_1066_, v_i_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec_ref(v_as_1066_);
lean_dec(v_n_u2080_1064_);
return v_res_1073_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__24(lean_object* v_n_u2081_1074_, lean_object* v_as_1075_, size_t v_i_1076_, size_t v_stop_1077_, lean_object* v_b_1078_){
_start:
{
lean_object* v___y_1080_; uint8_t v___x_1084_; 
v___x_1084_ = lean_usize_dec_eq(v_i_1076_, v_stop_1077_);
if (v___x_1084_ == 0)
{
lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; uint8_t v___x_1088_; 
v___x_1085_ = lean_array_uget_borrowed(v_as_1075_, v_i_1076_);
v___x_1086_ = l_Lean_Name_getPrefix(v___x_1085_);
v___x_1087_ = l_Lean_Name_getPrefix(v_n_u2081_1074_);
v___x_1088_ = l_Lean_Name_isPrefixOf(v___x_1086_, v___x_1087_);
lean_dec(v___x_1087_);
lean_dec(v___x_1086_);
if (v___x_1088_ == 0)
{
v___y_1080_ = v_b_1078_;
goto v___jp_1079_;
}
else
{
lean_object* v___x_1089_; 
lean_inc(v___x_1085_);
v___x_1089_ = lean_array_push(v_b_1078_, v___x_1085_);
v___y_1080_ = v___x_1089_;
goto v___jp_1079_;
}
}
else
{
return v_b_1078_;
}
v___jp_1079_:
{
size_t v___x_1081_; size_t v___x_1082_; 
v___x_1081_ = ((size_t)1ULL);
v___x_1082_ = lean_usize_add(v_i_1076_, v___x_1081_);
v_i_1076_ = v___x_1082_;
v_b_1078_ = v___y_1080_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__24_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_u2081_1074_ = stack[0].m_obj;
lean_object* v_as_1075_ = stack[1].m_obj;
size_t v_i_1076_ = stack[2].m_num;
size_t v_stop_1077_ = stack[3].m_num;
lean_object* v_b_1078_ = stack[4].m_obj;
lean_object* v_res_1090_;
v_res_1090_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__24(v_n_u2081_1074_, v_as_1075_, v_i_1076_, v_stop_1077_, v_b_1078_);
stack->m_obj
 = v_res_1090_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__24___boxed(lean_object* v_n_u2081_1091_, lean_object* v_as_1092_, lean_object* v_i_1093_, lean_object* v_stop_1094_, lean_object* v_b_1095_){
_start:
{
size_t v_i_boxed_1096_; size_t v_stop_boxed_1097_; lean_object* v_res_1098_; 
v_i_boxed_1096_ = lean_unbox_usize(v_i_1093_);
lean_dec(v_i_1093_);
v_stop_boxed_1097_ = lean_unbox_usize(v_stop_1094_);
lean_dec(v_stop_1094_);
v_res_1098_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__24(v_n_u2081_1091_, v_as_1092_, v_i_boxed_1096_, v_stop_boxed_1097_, v_b_1095_);
lean_dec_ref(v_as_1092_);
lean_dec(v_n_u2081_1091_);
return v_res_1098_;
}
}
lean_object* l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12(lean_object* v_n_u2080_1101_, uint8_t v_fullNames_1102_, uint8_t v_allowHorizAliases_1103_, lean_object* v_filter_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v_view_1110_; lean_object* v_name_1111_; lean_object* v_n_u2081_1112_; 
lean_inc(v_n_u2080_1101_);
v_view_1110_ = l_Lean_extractMacroScopes(v_n_u2080_1101_);
v_name_1111_ = lean_ctor_get(v_view_1110_, 0);
lean_inc(v_name_1111_);
v_n_u2081_1112_ = l_Lean_privateToUserName(v_name_1111_);
if (v_fullNames_1102_ == 0)
{
lean_object* v___x_1113_; lean_object* v_aliases_1115_; lean_object* v_env_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1113_ = lean_st_ref_get(v___y_1108_);
v_env_1130_ = lean_ctor_get(v___x_1113_, 0);
lean_inc_ref(v_env_1130_);
lean_dec(v___x_1113_);
lean_inc(v_n_u2080_1101_);
v___x_1131_ = l_Lean_getRevAliases(v_env_1130_, v_n_u2080_1101_);
v___x_1132_ = lean_array_mk(v___x_1131_);
if (v_allowHorizAliases_1103_ == 0)
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; uint8_t v___x_1136_; 
v___x_1133_ = lean_unsigned_to_nat(0u);
v___x_1134_ = lean_array_get_size(v___x_1132_);
v___x_1135_ = ((lean_object*)(l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12___closed__0));
v___x_1136_ = lean_nat_dec_lt(v___x_1133_, v___x_1134_);
if (v___x_1136_ == 0)
{
lean_dec_ref(v___x_1132_);
v_aliases_1115_ = v___x_1135_;
goto v___jp_1114_;
}
else
{
size_t v___x_1137_; size_t v___x_1138_; lean_object* v___x_1139_; 
v___x_1137_ = ((size_t)0ULL);
v___x_1138_ = lean_usize_of_nat(v___x_1134_);
v___x_1139_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__24(v_n_u2081_1112_, v___x_1132_, v___x_1137_, v___x_1138_, v___x_1135_);
lean_dec_ref(v___x_1132_);
v_aliases_1115_ = v___x_1139_;
goto v___jp_1114_;
}
}
else
{
v_aliases_1115_ = v___x_1132_;
goto v___jp_1114_;
}
v___jp_1114_:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1116_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_filter_1104_);
v___x_1117_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__23(v_n_u2080_1101_, v_filter_1104_, v_aliases_1115_, v___x_1116_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
lean_dec_ref(v_aliases_1115_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
if (lean_obj_tag(v_a_1118_) == 0)
{
lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1128_; 
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1128_ == 0)
{
lean_object* v_unused_1129_; 
v_unused_1129_ = lean_ctor_get(v___x_1117_, 0);
lean_dec(v_unused_1129_);
v___x_1120_ = v___x_1117_;
v_isShared_1121_ = v_isSharedCheck_1128_;
goto v_resetjp_1119_;
}
else
{
lean_dec(v___x_1117_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1128_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
lean_ctor_set_tag(v___x_1120_, 1);
lean_ctor_set(v___x_1120_, 0, v_view_1110_);
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_view_1110_);
v___x_1123_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1124_ = l_Lean_rootNamespace;
v___x_1125_ = l_Lean_Name_append(v___x_1124_, v_n_u2081_1112_);
v___x_1126_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22(v_n_u2080_1101_, v_filter_1104_, v___x_1123_, v___x_1125_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
lean_dec(v_n_u2080_1101_);
return v___x_1126_;
}
}
}
else
{
lean_dec(v_n_u2081_1112_);
lean_dec_ref(v_view_1110_);
lean_dec_ref(v_filter_1104_);
lean_dec(v_n_u2080_1101_);
return v___x_1117_;
}
}
else
{
lean_dec(v_n_u2081_1112_);
lean_dec_ref(v_view_1110_);
lean_dec_ref(v_filter_1104_);
lean_dec(v_n_u2080_1101_);
return v___x_1117_;
}
}
}
else
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1140_, 0, v_view_1110_);
lean_inc(v_n_u2081_1112_);
lean_inc_ref(v___x_1140_);
lean_inc_ref(v_filter_1104_);
v___x_1141_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25(v_n_u2080_1101_, v_filter_1104_, v___x_1140_, v_n_u2081_1112_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v_a_1142_; 
v_a_1142_ = lean_ctor_get(v___x_1141_, 0);
if (lean_obj_tag(v_a_1142_) == 0)
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
lean_dec_ref_known(v___x_1141_, 1);
v___x_1143_ = l_Lean_rootNamespace;
v___x_1144_ = l_Lean_Name_append(v___x_1143_, v_n_u2081_1112_);
v___x_1145_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25(v_n_u2080_1101_, v_filter_1104_, v___x_1140_, v___x_1144_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
lean_dec(v_n_u2080_1101_);
return v___x_1145_;
}
else
{
lean_dec_ref_known(v___x_1140_, 1);
lean_dec(v_n_u2081_1112_);
lean_dec_ref(v_filter_1104_);
lean_dec(v_n_u2080_1101_);
return v___x_1141_;
}
}
else
{
lean_dec_ref_known(v___x_1140_, 1);
lean_dec(v_n_u2081_1112_);
lean_dec_ref(v_filter_1104_);
lean_dec(v_n_u2080_1101_);
return v___x_1141_;
}
}
}
}
LEAN_EXPORT void l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_u2080_1101_ = stack[0].m_obj;
uint8_t v_fullNames_1102_ = stack[1].m_num;
uint8_t v_allowHorizAliases_1103_ = stack[2].m_num;
lean_object* v_filter_1104_ = stack[3].m_obj;
lean_object* v___y_1105_ = stack[4].m_obj;
lean_object* v___y_1106_ = stack[5].m_obj;
lean_object* v___y_1107_ = stack[6].m_obj;
lean_object* v___y_1108_ = stack[7].m_obj;
lean_object* v_res_1146_;
v_res_1146_ = l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12(v_n_u2080_1101_, v_fullNames_1102_, v_allowHorizAliases_1103_, v_filter_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
stack->m_obj
 = v_res_1146_;
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12___boxed(lean_object* v_n_u2080_1147_, lean_object* v_fullNames_1148_, lean_object* v_allowHorizAliases_1149_, lean_object* v_filter_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
uint8_t v_fullNames_boxed_1156_; uint8_t v_allowHorizAliases_boxed_1157_; lean_object* v_res_1158_; 
v_fullNames_boxed_1156_ = lean_unbox(v_fullNames_1148_);
v_allowHorizAliases_boxed_1157_ = lean_unbox(v_allowHorizAliases_1149_);
v_res_1158_ = l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12(v_n_u2080_1147_, v_fullNames_boxed_1156_, v_allowHorizAliases_boxed_1157_, v_filter_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
lean_dec(v___y_1154_);
lean_dec_ref(v___y_1153_);
lean_dec(v___y_1152_);
lean_dec_ref(v___y_1151_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg___lam__0(lean_object* v_localDecl_1159_, lean_object* v_givenName_1160_){
_start:
{
lean_object* v___x_1161_; uint8_t v___x_1162_; 
v___x_1161_ = l_Lean_LocalDecl_userName(v_localDecl_1159_);
v___x_1162_ = lean_name_eq(v___x_1161_, v_givenName_1160_);
lean_dec(v___x_1161_);
if (v___x_1162_ == 0)
{
lean_object* v___x_1163_; 
lean_dec_ref(v_localDecl_1159_);
v___x_1163_ = lean_box(0);
return v___x_1163_;
}
else
{
lean_object* v___x_1164_; 
v___x_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1164_, 0, v_localDecl_1159_);
return v___x_1164_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg___lam__0___boxed(lean_object* v_localDecl_1165_, lean_object* v_givenName_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg___lam__0(v_localDecl_1165_, v_givenName_1166_);
lean_dec(v_givenName_1166_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__17___redArg(lean_object* v_t_1168_, lean_object* v_k_1169_){
_start:
{
if (lean_obj_tag(v_t_1168_) == 0)
{
lean_object* v_k_1170_; lean_object* v_v_1171_; lean_object* v_l_1172_; lean_object* v_r_1173_; uint8_t v___x_1174_; 
v_k_1170_ = lean_ctor_get(v_t_1168_, 1);
v_v_1171_ = lean_ctor_get(v_t_1168_, 2);
v_l_1172_ = lean_ctor_get(v_t_1168_, 3);
v_r_1173_ = lean_ctor_get(v_t_1168_, 4);
v___x_1174_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1169_, v_k_1170_);
switch(v___x_1174_)
{
case 0:
{
v_t_1168_ = v_l_1172_;
goto _start;
}
case 1:
{
lean_object* v___x_1176_; 
lean_inc(v_v_1171_);
v___x_1176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1176_, 0, v_v_1171_);
return v___x_1176_;
}
default: 
{
v_t_1168_ = v_r_1173_;
goto _start;
}
}
}
else
{
lean_object* v___x_1178_; 
v___x_1178_ = lean_box(0);
return v___x_1178_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__17___redArg___boxed(lean_object* v_t_1179_, lean_object* v_k_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__17___redArg(v_t_1179_, v_k_1180_);
lean_dec(v_k_1180_);
lean_dec(v_t_1179_);
return v_res_1181_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg(lean_object* v_givenName_1182_, uint8_t v_skipAuxDecl_1183_, lean_object* v_auxDeclToFullName_1184_, lean_object* v___x_1185_, lean_object* v_givenNameView_1186_, lean_object* v_as_1187_, lean_object* v_i_1188_){
_start:
{
lean_object* v_zero_1189_; uint8_t v_isZero_1190_; 
v_zero_1189_ = lean_unsigned_to_nat(0u);
v_isZero_1190_ = lean_nat_dec_eq(v_i_1188_, v_zero_1189_);
if (v_isZero_1190_ == 1)
{
lean_object* v___x_1191_; 
lean_dec(v_i_1188_);
lean_dec_ref(v_givenNameView_1186_);
lean_dec(v___x_1185_);
v___x_1191_ = lean_box(0);
return v___x_1191_;
}
else
{
lean_object* v_one_1192_; lean_object* v_n_1193_; lean_object* v___y_1195_; lean_object* v___x_1197_; 
v_one_1192_ = lean_unsigned_to_nat(1u);
v_n_1193_ = lean_nat_sub(v_i_1188_, v_one_1192_);
lean_dec(v_i_1188_);
v___x_1197_ = lean_array_fget_borrowed(v_as_1187_, v_n_1193_);
if (lean_obj_tag(v___x_1197_) == 0)
{
v___y_1195_ = v___x_1197_;
goto v___jp_1194_;
}
else
{
lean_object* v_val_1198_; uint8_t v___x_1199_; 
v_val_1198_ = lean_ctor_get(v___x_1197_, 0);
v___x_1199_ = l_Lean_LocalDecl_isAuxDecl(v_val_1198_);
if (v___x_1199_ == 0)
{
lean_object* v___x_1200_; 
lean_inc(v_val_1198_);
v___x_1200_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg___lam__0(v_val_1198_, v_givenName_1182_);
v___y_1195_ = v___x_1200_;
goto v___jp_1194_;
}
else
{
if (v_skipAuxDecl_1183_ == 0)
{
if (v___x_1199_ == 0)
{
v_i_1188_ = v_n_1193_;
goto _start;
}
else
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1202_ = l_Lean_LocalDecl_fvarId(v_val_1198_);
v___x_1203_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__17___redArg(v_auxDeclToFullName_1184_, v___x_1202_);
lean_dec(v___x_1202_);
if (lean_obj_tag(v___x_1203_) == 1)
{
lean_object* v_val_1204_; lean_object* v_fullDeclView_1205_; lean_object* v___y_1207_; lean_object* v_name_1228_; lean_object* v___x_1229_; 
v_val_1204_ = lean_ctor_get(v___x_1203_, 0);
lean_inc(v_val_1204_);
lean_dec_ref_known(v___x_1203_, 1);
v_fullDeclView_1205_ = l_Lean_extractMacroScopes(v_val_1204_);
v_name_1228_ = lean_ctor_get(v_fullDeclView_1205_, 0);
lean_inc(v_name_1228_);
v___x_1229_ = l_Lean_privateToUserName_x3f(v_name_1228_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_inc(v_name_1228_);
v___y_1207_ = v_name_1228_;
goto v___jp_1206_;
}
else
{
lean_object* v_val_1230_; 
v_val_1230_ = lean_ctor_get(v___x_1229_, 0);
lean_inc(v_val_1230_);
lean_dec_ref_known(v___x_1229_, 1);
v___y_1207_ = v_val_1230_;
goto v___jp_1206_;
}
v___jp_1206_:
{
lean_object* v_imported_1208_; lean_object* v_ctx_1209_; lean_object* v_scopes_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1226_; 
v_imported_1208_ = lean_ctor_get(v_fullDeclView_1205_, 1);
v_ctx_1209_ = lean_ctor_get(v_fullDeclView_1205_, 2);
v_scopes_1210_ = lean_ctor_get(v_fullDeclView_1205_, 3);
v_isSharedCheck_1226_ = !lean_is_exclusive(v_fullDeclView_1205_);
if (v_isSharedCheck_1226_ == 0)
{
lean_object* v_unused_1227_; 
v_unused_1227_ = lean_ctor_get(v_fullDeclView_1205_, 0);
lean_dec(v_unused_1227_);
v___x_1212_ = v_fullDeclView_1205_;
v_isShared_1213_ = v_isSharedCheck_1226_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_scopes_1210_);
lean_inc(v_ctx_1209_);
lean_inc(v_imported_1208_);
lean_dec(v_fullDeclView_1205_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1226_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v_fullDeclView_1215_; 
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 0, v___y_1207_);
v_fullDeclView_1215_ = v___x_1212_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___y_1207_);
lean_ctor_set(v_reuseFailAlloc_1225_, 1, v_imported_1208_);
lean_ctor_set(v_reuseFailAlloc_1225_, 2, v_ctx_1209_);
lean_ctor_set(v_reuseFailAlloc_1225_, 3, v_scopes_1210_);
v_fullDeclView_1215_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
lean_object* v_fullDeclName_1216_; uint8_t v___x_1217_; 
lean_inc_ref(v_fullDeclView_1215_);
v_fullDeclName_1216_ = l_Lean_MacroScopesView_review(v_fullDeclView_1215_);
v___x_1217_ = l_Lean_Name_isPrefixOf(v___x_1185_, v_fullDeclName_1216_);
if (v___x_1217_ == 0)
{
lean_object* v___x_1218_; 
lean_dec_ref(v_fullDeclView_1215_);
lean_inc(v___x_1185_);
lean_inc_ref(v_givenNameView_1186_);
lean_inc(v_val_1198_);
v___x_1218_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_val_1198_, v_givenNameView_1186_, v_fullDeclName_1216_, v___x_1185_);
lean_dec(v_fullDeclName_1216_);
v___y_1195_ = v___x_1218_;
goto v___jp_1194_;
}
else
{
lean_object* v___x_1219_; lean_object* v_localDeclNameView_1220_; uint8_t v___x_1221_; 
lean_dec(v_fullDeclName_1216_);
v___x_1219_ = l_Lean_LocalDecl_userName(v_val_1198_);
v_localDeclNameView_1220_ = l_Lean_extractMacroScopes(v___x_1219_);
v___x_1221_ = l_Lean_MacroScopesView_isSuffixOf(v_localDeclNameView_1220_, v_givenNameView_1186_);
lean_dec_ref(v_localDeclNameView_1220_);
if (v___x_1221_ == 0)
{
lean_dec_ref(v_fullDeclView_1215_);
v_i_1188_ = v_n_1193_;
goto _start;
}
else
{
uint8_t v___x_1223_; 
v___x_1223_ = l_Lean_MacroScopesView_isSuffixOf(v_givenNameView_1186_, v_fullDeclView_1215_);
lean_dec_ref(v_fullDeclView_1215_);
if (v___x_1223_ == 0)
{
v_i_1188_ = v_n_1193_;
goto _start;
}
else
{
lean_inc_ref(v___x_1197_);
v___y_1195_ = v___x_1197_;
goto v___jp_1194_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1231_; 
lean_dec(v___x_1203_);
lean_inc(v_val_1198_);
v___x_1231_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg___lam__0(v_val_1198_, v_givenName_1182_);
v___y_1195_ = v___x_1231_;
goto v___jp_1194_;
}
}
}
else
{
v_i_1188_ = v_n_1193_;
goto _start;
}
}
}
v___jp_1194_:
{
if (lean_obj_tag(v___y_1195_) == 0)
{
v_i_1188_ = v_n_1193_;
goto _start;
}
else
{
lean_dec(v_n_1193_);
lean_dec_ref(v_givenNameView_1186_);
lean_dec(v___x_1185_);
return v___y_1195_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_givenName_1182_ = stack[0].m_obj;
uint8_t v_skipAuxDecl_1183_ = stack[1].m_num;
lean_object* v_auxDeclToFullName_1184_ = stack[2].m_obj;
lean_object* v___x_1185_ = stack[3].m_obj;
lean_object* v_givenNameView_1186_ = stack[4].m_obj;
lean_object* v_as_1187_ = stack[5].m_obj;
lean_object* v_i_1188_ = stack[6].m_obj;
lean_object* v_res_1233_;
v_res_1233_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg(v_givenName_1182_, v_skipAuxDecl_1183_, v_auxDeclToFullName_1184_, v___x_1185_, v_givenNameView_1186_, v_as_1187_, v_i_1188_);
stack->m_obj
 = v_res_1233_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg___boxed(lean_object* v_givenName_1234_, lean_object* v_skipAuxDecl_1235_, lean_object* v_auxDeclToFullName_1236_, lean_object* v___x_1237_, lean_object* v_givenNameView_1238_, lean_object* v_as_1239_, lean_object* v_i_1240_){
_start:
{
uint8_t v_skipAuxDecl_boxed_1241_; lean_object* v_res_1242_; 
v_skipAuxDecl_boxed_1241_ = lean_unbox(v_skipAuxDecl_1235_);
v_res_1242_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg(v_givenName_1234_, v_skipAuxDecl_boxed_1241_, v_auxDeclToFullName_1236_, v___x_1237_, v_givenNameView_1238_, v_as_1239_, v_i_1240_);
lean_dec_ref(v_as_1239_);
lean_dec(v_auxDeclToFullName_1236_);
lean_dec(v_givenName_1234_);
return v_res_1242_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24___redArg(lean_object* v_givenName_1243_, uint8_t v_skipAuxDecl_1244_, lean_object* v_auxDeclToFullName_1245_, lean_object* v___x_1246_, lean_object* v_givenNameView_1247_, lean_object* v_as_1248_, lean_object* v_i_1249_){
_start:
{
lean_object* v_zero_1250_; uint8_t v_isZero_1251_; 
v_zero_1250_ = lean_unsigned_to_nat(0u);
v_isZero_1251_ = lean_nat_dec_eq(v_i_1249_, v_zero_1250_);
if (v_isZero_1251_ == 1)
{
lean_object* v___x_1252_; 
lean_dec(v_i_1249_);
lean_dec_ref(v_givenNameView_1247_);
lean_dec(v___x_1246_);
v___x_1252_ = lean_box(0);
return v___x_1252_;
}
else
{
lean_object* v_one_1253_; lean_object* v_n_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v_one_1253_ = lean_unsigned_to_nat(1u);
v_n_1254_ = lean_nat_sub(v_i_1249_, v_one_1253_);
lean_dec(v_i_1249_);
v___x_1255_ = lean_array_fget_borrowed(v_as_1248_, v_n_1254_);
lean_inc_ref(v_givenNameView_1247_);
lean_inc(v___x_1246_);
v___x_1256_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21(v_givenName_1243_, v_skipAuxDecl_1244_, v_auxDeclToFullName_1245_, v___x_1246_, v_givenNameView_1247_, v___x_1255_);
if (lean_obj_tag(v___x_1256_) == 0)
{
v_i_1249_ = v_n_1254_;
goto _start;
}
else
{
lean_dec(v_n_1254_);
lean_dec_ref(v_givenNameView_1247_);
lean_dec(v___x_1246_);
return v___x_1256_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_givenName_1243_ = stack[0].m_obj;
uint8_t v_skipAuxDecl_1244_ = stack[1].m_num;
lean_object* v_auxDeclToFullName_1245_ = stack[2].m_obj;
lean_object* v___x_1246_ = stack[3].m_obj;
lean_object* v_givenNameView_1247_ = stack[4].m_obj;
lean_object* v_as_1248_ = stack[5].m_obj;
lean_object* v_i_1249_ = stack[6].m_obj;
lean_object* v_res_1258_;
v_res_1258_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24___redArg(v_givenName_1243_, v_skipAuxDecl_1244_, v_auxDeclToFullName_1245_, v___x_1246_, v_givenNameView_1247_, v_as_1248_, v_i_1249_);
stack->m_obj
 = v_res_1258_;
}
lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21(lean_object* v_givenName_1259_, uint8_t v_skipAuxDecl_1260_, lean_object* v_auxDeclToFullName_1261_, lean_object* v___x_1262_, lean_object* v_givenNameView_1263_, lean_object* v_x_1264_){
_start:
{
if (lean_obj_tag(v_x_1264_) == 0)
{
lean_object* v_cs_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v_cs_1265_ = lean_ctor_get(v_x_1264_, 0);
v___x_1266_ = lean_array_get_size(v_cs_1265_);
v___x_1267_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24___redArg(v_givenName_1259_, v_skipAuxDecl_1260_, v_auxDeclToFullName_1261_, v___x_1262_, v_givenNameView_1263_, v_cs_1265_, v___x_1266_);
return v___x_1267_;
}
else
{
lean_object* v_vs_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v_vs_1268_ = lean_ctor_get(v_x_1264_, 0);
v___x_1269_ = lean_array_get_size(v_vs_1268_);
v___x_1270_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg(v_givenName_1259_, v_skipAuxDecl_1260_, v_auxDeclToFullName_1261_, v___x_1262_, v_givenNameView_1263_, v_vs_1268_, v___x_1269_);
return v___x_1270_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_0interp(lean_interpreter_value* stack)
{
lean_object* v_givenName_1259_ = stack[0].m_obj;
uint8_t v_skipAuxDecl_1260_ = stack[1].m_num;
lean_object* v_auxDeclToFullName_1261_ = stack[2].m_obj;
lean_object* v___x_1262_ = stack[3].m_obj;
lean_object* v_givenNameView_1263_ = stack[4].m_obj;
lean_object* v_x_1264_ = stack[5].m_obj;
lean_object* v_res_1271_;
v_res_1271_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21(v_givenName_1259_, v_skipAuxDecl_1260_, v_auxDeclToFullName_1261_, v___x_1262_, v_givenNameView_1263_, v_x_1264_);
stack->m_obj
 = v_res_1271_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21___boxed(lean_object* v_givenName_1272_, lean_object* v_skipAuxDecl_1273_, lean_object* v_auxDeclToFullName_1274_, lean_object* v___x_1275_, lean_object* v_givenNameView_1276_, lean_object* v_x_1277_){
_start:
{
uint8_t v_skipAuxDecl_boxed_1278_; lean_object* v_res_1279_; 
v_skipAuxDecl_boxed_1278_ = lean_unbox(v_skipAuxDecl_1273_);
v_res_1279_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21(v_givenName_1272_, v_skipAuxDecl_boxed_1278_, v_auxDeclToFullName_1274_, v___x_1275_, v_givenNameView_1276_, v_x_1277_);
lean_dec_ref(v_x_1277_);
lean_dec(v_auxDeclToFullName_1274_);
lean_dec(v_givenName_1272_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24___redArg___boxed(lean_object* v_givenName_1280_, lean_object* v_skipAuxDecl_1281_, lean_object* v_auxDeclToFullName_1282_, lean_object* v___x_1283_, lean_object* v_givenNameView_1284_, lean_object* v_as_1285_, lean_object* v_i_1286_){
_start:
{
uint8_t v_skipAuxDecl_boxed_1287_; lean_object* v_res_1288_; 
v_skipAuxDecl_boxed_1287_ = lean_unbox(v_skipAuxDecl_1281_);
v_res_1288_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24___redArg(v_givenName_1280_, v_skipAuxDecl_boxed_1287_, v_auxDeclToFullName_1282_, v___x_1283_, v_givenNameView_1284_, v_as_1285_, v_i_1286_);
lean_dec_ref(v_as_1285_);
lean_dec(v_auxDeclToFullName_1282_);
lean_dec(v_givenName_1280_);
return v_res_1288_;
}
}
lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18(lean_object* v_givenName_1289_, uint8_t v_skipAuxDecl_1290_, lean_object* v_auxDeclToFullName_1291_, lean_object* v___x_1292_, lean_object* v_givenNameView_1293_, lean_object* v_t_1294_){
_start:
{
lean_object* v_root_1295_; lean_object* v_tail_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v_root_1295_ = lean_ctor_get(v_t_1294_, 0);
v_tail_1296_ = lean_ctor_get(v_t_1294_, 1);
v___x_1297_ = lean_array_get_size(v_tail_1296_);
lean_inc_ref(v_givenNameView_1293_);
lean_inc(v___x_1292_);
v___x_1298_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg(v_givenName_1289_, v_skipAuxDecl_1290_, v_auxDeclToFullName_1291_, v___x_1292_, v_givenNameView_1293_, v_tail_1296_, v___x_1297_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_object* v___x_1299_; 
v___x_1299_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21(v_givenName_1289_, v_skipAuxDecl_1290_, v_auxDeclToFullName_1291_, v___x_1292_, v_givenNameView_1293_, v_root_1295_);
return v___x_1299_;
}
else
{
lean_dec_ref(v_givenNameView_1293_);
lean_dec(v___x_1292_);
return v___x_1298_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_0interp(lean_interpreter_value* stack)
{
lean_object* v_givenName_1289_ = stack[0].m_obj;
uint8_t v_skipAuxDecl_1290_ = stack[1].m_num;
lean_object* v_auxDeclToFullName_1291_ = stack[2].m_obj;
lean_object* v___x_1292_ = stack[3].m_obj;
lean_object* v_givenNameView_1293_ = stack[4].m_obj;
lean_object* v_t_1294_ = stack[5].m_obj;
lean_object* v_res_1300_;
v_res_1300_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18(v_givenName_1289_, v_skipAuxDecl_1290_, v_auxDeclToFullName_1291_, v___x_1292_, v_givenNameView_1293_, v_t_1294_);
stack->m_obj
 = v_res_1300_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18___boxed(lean_object* v_givenName_1301_, lean_object* v_skipAuxDecl_1302_, lean_object* v_auxDeclToFullName_1303_, lean_object* v___x_1304_, lean_object* v_givenNameView_1305_, lean_object* v_t_1306_){
_start:
{
uint8_t v_skipAuxDecl_boxed_1307_; lean_object* v_res_1308_; 
v_skipAuxDecl_boxed_1307_ = lean_unbox(v_skipAuxDecl_1302_);
v_res_1308_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18(v_givenName_1301_, v_skipAuxDecl_boxed_1307_, v_auxDeclToFullName_1303_, v___x_1304_, v_givenNameView_1305_, v_t_1306_);
lean_dec_ref(v_t_1306_);
lean_dec(v_auxDeclToFullName_1303_);
lean_dec(v_givenName_1301_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___redArg(lean_object* v_localDecl_x3f_1309_, lean_object* v_givenName_1310_, lean_object* v_as_1311_, lean_object* v_i_1312_){
_start:
{
lean_object* v_zero_1313_; uint8_t v_isZero_1314_; 
v_zero_1313_ = lean_unsigned_to_nat(0u);
v_isZero_1314_ = lean_nat_dec_eq(v_i_1312_, v_zero_1313_);
if (v_isZero_1314_ == 1)
{
lean_object* v___x_1315_; 
lean_dec(v_i_1312_);
v___x_1315_ = lean_box(0);
return v___x_1315_;
}
else
{
lean_object* v_one_1316_; lean_object* v_n_1317_; lean_object* v___y_1319_; lean_object* v___x_1321_; 
v_one_1316_ = lean_unsigned_to_nat(1u);
v_n_1317_ = lean_nat_sub(v_i_1312_, v_one_1316_);
lean_dec(v_i_1312_);
v___x_1321_ = lean_array_fget_borrowed(v_as_1311_, v_n_1317_);
if (lean_obj_tag(v___x_1321_) == 0)
{
v___y_1319_ = v___x_1321_;
goto v___jp_1318_;
}
else
{
lean_object* v_val_1322_; uint8_t v___x_1323_; 
v_val_1322_ = lean_ctor_get(v___x_1321_, 0);
v___x_1323_ = l_Lean_LocalDecl_isAuxDecl(v_val_1322_);
if (v___x_1323_ == 0)
{
v___y_1319_ = v_localDecl_x3f_1309_;
goto v___jp_1318_;
}
else
{
lean_object* v___x_1324_; uint8_t v___x_1325_; 
v___x_1324_ = l_Lean_LocalDecl_userName(v_val_1322_);
v___x_1325_ = lean_name_eq(v___x_1324_, v_givenName_1310_);
lean_dec(v___x_1324_);
if (v___x_1325_ == 0)
{
v_i_1312_ = v_n_1317_;
goto _start;
}
else
{
v___y_1319_ = v___x_1321_;
goto v___jp_1318_;
}
}
}
v___jp_1318_:
{
if (lean_obj_tag(v___y_1319_) == 0)
{
v_i_1312_ = v_n_1317_;
goto _start;
}
else
{
lean_dec(v_n_1317_);
lean_inc_ref(v___y_1319_);
return v___y_1319_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___redArg___boxed(lean_object* v_localDecl_x3f_1327_, lean_object* v_givenName_1328_, lean_object* v_as_1329_, lean_object* v_i_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___redArg(v_localDecl_x3f_1327_, v_givenName_1328_, v_as_1329_, v_i_1330_);
lean_dec_ref(v_as_1329_);
lean_dec(v_givenName_1328_);
lean_dec(v_localDecl_x3f_1327_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28___redArg(lean_object* v_localDecl_x3f_1332_, lean_object* v_givenName_1333_, lean_object* v_as_1334_, lean_object* v_i_1335_){
_start:
{
lean_object* v_zero_1336_; uint8_t v_isZero_1337_; 
v_zero_1336_ = lean_unsigned_to_nat(0u);
v_isZero_1337_ = lean_nat_dec_eq(v_i_1335_, v_zero_1336_);
if (v_isZero_1337_ == 1)
{
lean_object* v___x_1338_; 
lean_dec(v_i_1335_);
v___x_1338_ = lean_box(0);
return v___x_1338_;
}
else
{
lean_object* v_one_1339_; lean_object* v_n_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v_one_1339_ = lean_unsigned_to_nat(1u);
v_n_1340_ = lean_nat_sub(v_i_1335_, v_one_1339_);
lean_dec(v_i_1335_);
v___x_1341_ = lean_array_fget_borrowed(v_as_1334_, v_n_1340_);
v___x_1342_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24(v_localDecl_x3f_1332_, v_givenName_1333_, v___x_1341_);
if (lean_obj_tag(v___x_1342_) == 0)
{
v_i_1335_ = v_n_1340_;
goto _start;
}
else
{
lean_dec(v_n_1340_);
return v___x_1342_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24(lean_object* v_localDecl_x3f_1344_, lean_object* v_givenName_1345_, lean_object* v_x_1346_){
_start:
{
if (lean_obj_tag(v_x_1346_) == 0)
{
lean_object* v_cs_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v_cs_1347_ = lean_ctor_get(v_x_1346_, 0);
v___x_1348_ = lean_array_get_size(v_cs_1347_);
v___x_1349_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28___redArg(v_localDecl_x3f_1344_, v_givenName_1345_, v_cs_1347_, v___x_1348_);
return v___x_1349_;
}
else
{
lean_object* v_vs_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v_vs_1350_ = lean_ctor_get(v_x_1346_, 0);
v___x_1351_ = lean_array_get_size(v_vs_1350_);
v___x_1352_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___redArg(v_localDecl_x3f_1344_, v_givenName_1345_, v_vs_1350_, v___x_1351_);
return v___x_1352_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24___boxed(lean_object* v_localDecl_x3f_1353_, lean_object* v_givenName_1354_, lean_object* v_x_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24(v_localDecl_x3f_1353_, v_givenName_1354_, v_x_1355_);
lean_dec_ref(v_x_1355_);
lean_dec(v_givenName_1354_);
lean_dec(v_localDecl_x3f_1353_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28___redArg___boxed(lean_object* v_localDecl_x3f_1357_, lean_object* v_givenName_1358_, lean_object* v_as_1359_, lean_object* v_i_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28___redArg(v_localDecl_x3f_1357_, v_givenName_1358_, v_as_1359_, v_i_1360_);
lean_dec_ref(v_as_1359_);
lean_dec(v_givenName_1358_);
lean_dec(v_localDecl_x3f_1357_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19(lean_object* v_localDecl_x3f_1362_, lean_object* v_givenName_1363_, lean_object* v_t_1364_){
_start:
{
lean_object* v_root_1365_; lean_object* v_tail_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
v_root_1365_ = lean_ctor_get(v_t_1364_, 0);
v_tail_1366_ = lean_ctor_get(v_t_1364_, 1);
v___x_1367_ = lean_array_get_size(v_tail_1366_);
v___x_1368_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___redArg(v_localDecl_x3f_1362_, v_givenName_1363_, v_tail_1366_, v___x_1367_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v___x_1369_; 
v___x_1369_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24(v_localDecl_x3f_1362_, v_givenName_1363_, v_root_1365_);
return v___x_1369_;
}
else
{
return v___x_1368_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19___boxed(lean_object* v_localDecl_x3f_1370_, lean_object* v_givenName_1371_, lean_object* v_t_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19(v_localDecl_x3f_1370_, v_givenName_1371_, v_t_1372_);
lean_dec_ref(v_t_1372_);
lean_dec(v_givenName_1371_);
lean_dec(v_localDecl_x3f_1370_);
return v_res_1373_;
}
}
lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11___lam__0(lean_object* v_auxDeclToFullName_1374_, lean_object* v_currNamespace_1375_, lean_object* v_decls_1376_, lean_object* v_givenNameView_1377_, uint8_t v_skipAuxDecl_1378_){
_start:
{
lean_object* v_givenName_1379_; lean_object* v_localDecl_x3f_1380_; 
lean_inc_ref(v_givenNameView_1377_);
v_givenName_1379_ = l_Lean_MacroScopesView_review(v_givenNameView_1377_);
v_localDecl_x3f_1380_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18(v_givenName_1379_, v_skipAuxDecl_1378_, v_auxDeclToFullName_1374_, v_currNamespace_1375_, v_givenNameView_1377_, v_decls_1376_);
if (lean_obj_tag(v_localDecl_x3f_1380_) == 0)
{
if (v_skipAuxDecl_1378_ == 0)
{
lean_object* v___x_1381_; 
v___x_1381_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19(v_localDecl_x3f_1380_, v_givenName_1379_, v_decls_1376_);
lean_dec(v_givenName_1379_);
return v___x_1381_;
}
else
{
lean_dec(v_givenName_1379_);
return v_localDecl_x3f_1380_;
}
}
else
{
lean_dec(v_givenName_1379_);
return v_localDecl_x3f_1380_;
}
}
}
LEAN_EXPORT void l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_auxDeclToFullName_1374_ = stack[0].m_obj;
lean_object* v_currNamespace_1375_ = stack[1].m_obj;
lean_object* v_decls_1376_ = stack[2].m_obj;
lean_object* v_givenNameView_1377_ = stack[3].m_obj;
uint8_t v_skipAuxDecl_1378_ = stack[4].m_num;
lean_object* v_res_1382_;
v_res_1382_ = l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11___lam__0(v_auxDeclToFullName_1374_, v_currNamespace_1375_, v_decls_1376_, v_givenNameView_1377_, v_skipAuxDecl_1378_);
stack->m_obj
 = v_res_1382_;
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11___lam__0___boxed(lean_object* v_auxDeclToFullName_1383_, lean_object* v_currNamespace_1384_, lean_object* v_decls_1385_, lean_object* v_givenNameView_1386_, lean_object* v_skipAuxDecl_1387_){
_start:
{
uint8_t v_skipAuxDecl_boxed_1388_; lean_object* v_res_1389_; 
v_skipAuxDecl_boxed_1388_ = lean_unbox(v_skipAuxDecl_1387_);
v_res_1389_ = l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11___lam__0(v_auxDeclToFullName_1383_, v_currNamespace_1384_, v_decls_1385_, v_givenNameView_1386_, v_skipAuxDecl_boxed_1388_);
lean_dec_ref(v_decls_1385_);
lean_dec(v_auxDeclToFullName_1383_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__27(lean_object* v_a_1390_, lean_object* v_a_1391_){
_start:
{
if (lean_obj_tag(v_a_1390_) == 0)
{
lean_object* v___x_1392_; 
v___x_1392_ = l_List_reverse___redArg(v_a_1391_);
return v___x_1392_;
}
else
{
lean_object* v_head_1393_; lean_object* v_tail_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1405_; 
v_head_1393_ = lean_ctor_get(v_a_1390_, 0);
v_tail_1394_ = lean_ctor_get(v_a_1390_, 1);
v_isSharedCheck_1405_ = !lean_is_exclusive(v_a_1390_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1396_ = v_a_1390_;
v_isShared_1397_ = v_isSharedCheck_1405_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_tail_1394_);
lean_inc(v_head_1393_);
lean_dec(v_a_1390_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1405_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v_snd_1398_; uint8_t v___x_1399_; 
v_snd_1398_ = lean_ctor_get(v_head_1393_, 1);
v___x_1399_ = l_List_isEmpty___redArg(v_snd_1398_);
if (v___x_1399_ == 0)
{
lean_del_object(v___x_1396_);
lean_dec(v_head_1393_);
v_a_1390_ = v_tail_1394_;
goto _start;
}
else
{
lean_object* v___x_1402_; 
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 1, v_a_1391_);
v___x_1402_ = v___x_1396_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_head_1393_);
lean_ctor_set(v_reuseFailAlloc_1404_, 1, v_a_1391_);
v___x_1402_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
v_a_1390_ = v_tail_1394_;
v_a_1391_ = v___x_1402_;
goto _start;
}
}
}
}
}
}
lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44(lean_object* v_ref_1406_, lean_object* v_msgData_1407_, uint8_t v_severity_1408_, uint8_t v_isSilent_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
uint8_t v___y_1416_; lean_object* v___y_1417_; uint8_t v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v_toCold_1423_; lean_object* v___y_1424_; lean_object* v___y_1453_; lean_object* v___y_1454_; lean_object* v___y_1455_; uint8_t v___y_1456_; uint8_t v___y_1457_; uint8_t v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1480_; uint8_t v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1483_; uint8_t v___y_1484_; uint8_t v___y_1485_; lean_object* v___y_1486_; uint8_t v___y_1490_; uint8_t v___y_1491_; uint8_t v___y_1492_; uint8_t v___x_1503_; uint8_t v___y_1505_; uint8_t v___y_1506_; uint8_t v___y_1507_; uint8_t v___y_1509_; uint8_t v___x_1517_; 
v___x_1503_ = 2;
v___x_1517_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1408_, v___x_1503_);
if (v___x_1517_ == 0)
{
v___y_1509_ = v___x_1517_;
goto v___jp_1508_;
}
else
{
uint8_t v___x_1518_; 
lean_inc_ref(v_msgData_1407_);
v___x_1518_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1407_);
v___y_1509_ = v___x_1518_;
goto v___jp_1508_;
}
v___jp_1415_:
{
lean_object* v_currNamespace_1425_; lean_object* v_openDecls_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v_env_1431_; lean_object* v_nextMacroScope_1432_; lean_object* v_ngen_1433_; lean_object* v_auxDeclNGen_1434_; lean_object* v_traceState_1435_; lean_object* v_cache_1436_; lean_object* v_recordedDeps_1437_; lean_object* v_messages_1438_; lean_object* v_infoState_1439_; lean_object* v_snapshotTasks_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1451_; 
v_currNamespace_1425_ = lean_ctor_get(v_toCold_1423_, 4);
v_openDecls_1426_ = lean_ctor_get(v_toCold_1423_, 5);
lean_inc(v_openDecls_1426_);
lean_inc(v_currNamespace_1425_);
v___x_1427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1427_, 0, v_currNamespace_1425_);
lean_ctor_set(v___x_1427_, 1, v_openDecls_1426_);
v___x_1428_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1427_);
lean_ctor_set(v___x_1428_, 1, v___y_1417_);
lean_inc_ref(v___y_1419_);
lean_inc_ref(v___y_1422_);
v___x_1429_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1429_, 0, v___y_1422_);
lean_ctor_set(v___x_1429_, 1, v___y_1421_);
lean_ctor_set(v___x_1429_, 2, v___y_1420_);
lean_ctor_set(v___x_1429_, 3, v___y_1419_);
lean_ctor_set(v___x_1429_, 4, v___x_1428_);
lean_ctor_set_uint8(v___x_1429_, sizeof(void*)*5, v___y_1418_);
lean_ctor_set_uint8(v___x_1429_, sizeof(void*)*5 + 1, v___y_1416_);
lean_ctor_set_uint8(v___x_1429_, sizeof(void*)*5 + 2, v_isSilent_1409_);
v___x_1430_ = lean_st_ref_take(v___y_1424_);
v_env_1431_ = lean_ctor_get(v___x_1430_, 0);
v_nextMacroScope_1432_ = lean_ctor_get(v___x_1430_, 1);
v_ngen_1433_ = lean_ctor_get(v___x_1430_, 2);
v_auxDeclNGen_1434_ = lean_ctor_get(v___x_1430_, 3);
v_traceState_1435_ = lean_ctor_get(v___x_1430_, 4);
v_cache_1436_ = lean_ctor_get(v___x_1430_, 5);
v_recordedDeps_1437_ = lean_ctor_get(v___x_1430_, 6);
v_messages_1438_ = lean_ctor_get(v___x_1430_, 7);
v_infoState_1439_ = lean_ctor_get(v___x_1430_, 8);
v_snapshotTasks_1440_ = lean_ctor_get(v___x_1430_, 9);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1442_ = v___x_1430_;
v_isShared_1443_ = v_isSharedCheck_1451_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_snapshotTasks_1440_);
lean_inc(v_infoState_1439_);
lean_inc(v_messages_1438_);
lean_inc(v_recordedDeps_1437_);
lean_inc(v_cache_1436_);
lean_inc(v_traceState_1435_);
lean_inc(v_auxDeclNGen_1434_);
lean_inc(v_ngen_1433_);
lean_inc(v_nextMacroScope_1432_);
lean_inc(v_env_1431_);
lean_dec(v___x_1430_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1451_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1447_; 
v___x_1444_ = lean_box(0);
v___x_1445_ = l_Lean_MessageLog_add(v___x_1429_, v_messages_1438_);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 7, v___x_1445_);
v___x_1447_ = v___x_1442_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_env_1431_);
lean_ctor_set(v_reuseFailAlloc_1450_, 1, v_nextMacroScope_1432_);
lean_ctor_set(v_reuseFailAlloc_1450_, 2, v_ngen_1433_);
lean_ctor_set(v_reuseFailAlloc_1450_, 3, v_auxDeclNGen_1434_);
lean_ctor_set(v_reuseFailAlloc_1450_, 4, v_traceState_1435_);
lean_ctor_set(v_reuseFailAlloc_1450_, 5, v_cache_1436_);
lean_ctor_set(v_reuseFailAlloc_1450_, 6, v_recordedDeps_1437_);
lean_ctor_set(v_reuseFailAlloc_1450_, 7, v___x_1445_);
lean_ctor_set(v_reuseFailAlloc_1450_, 8, v_infoState_1439_);
lean_ctor_set(v_reuseFailAlloc_1450_, 9, v_snapshotTasks_1440_);
v___x_1447_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1448_ = lean_st_ref_put(v___y_1424_, v___x_1447_);
v___x_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1444_);
return v___x_1449_;
}
}
}
v___jp_1452_:
{
lean_object* v_fileName_1461_; lean_object* v_fileMap_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1478_; 
v_fileName_1461_ = lean_ctor_get(v___y_1455_, 0);
v_fileMap_1462_ = lean_ctor_get(v___y_1455_, 1);
v___x_1463_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1407_);
v___x_1464_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44_spec__47(v___x_1463_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
v_a_1465_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1467_ = v___x_1464_;
v_isShared_1468_ = v_isSharedCheck_1478_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1464_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1478_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
lean_inc_ref_n(v_fileMap_1462_, 2);
v___x_1469_ = l_Lean_FileMap_toPosition(v_fileMap_1462_, v___y_1459_);
lean_dec(v___y_1459_);
v___x_1470_ = l_Lean_FileMap_toPosition(v_fileMap_1462_, v___y_1460_);
lean_dec(v___y_1460_);
v___x_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1470_);
v___x_1472_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48___closed__0));
if (v___y_1457_ == 0)
{
lean_del_object(v___x_1467_);
lean_dec_ref(v___y_1454_);
v___y_1416_ = v___y_1456_;
v___y_1417_ = v_a_1465_;
v___y_1418_ = v___y_1458_;
v___y_1419_ = v___x_1472_;
v___y_1420_ = v___x_1471_;
v___y_1421_ = v___x_1469_;
v___y_1422_ = v_fileName_1461_;
v_toCold_1423_ = v___y_1453_;
v___y_1424_ = v___y_1413_;
goto v___jp_1415_;
}
else
{
uint8_t v___x_1473_; 
lean_inc(v_a_1465_);
v___x_1473_ = l_Lean_MessageData_hasTag(v___y_1454_, v_a_1465_);
if (v___x_1473_ == 0)
{
lean_object* v___x_1474_; lean_object* v___x_1476_; 
lean_dec_ref_known(v___x_1471_, 1);
lean_dec_ref(v___x_1469_);
lean_dec(v_a_1465_);
v___x_1474_ = lean_box(0);
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 0, v___x_1474_);
v___x_1476_ = v___x_1467_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v___x_1474_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
else
{
lean_del_object(v___x_1467_);
v___y_1416_ = v___y_1456_;
v___y_1417_ = v_a_1465_;
v___y_1418_ = v___y_1458_;
v___y_1419_ = v___x_1472_;
v___y_1420_ = v___x_1471_;
v___y_1421_ = v___x_1469_;
v___y_1422_ = v_fileName_1461_;
v_toCold_1423_ = v___y_1453_;
v___y_1424_ = v___y_1413_;
goto v___jp_1415_;
}
}
}
}
v___jp_1479_:
{
lean_object* v___x_1487_; 
v___x_1487_ = l_Lean_Syntax_getTailPos_x3f(v___y_1483_, v___y_1485_);
lean_dec(v___y_1483_);
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_inc(v___y_1486_);
v___y_1453_ = v___y_1480_;
v___y_1454_ = v___y_1482_;
v___y_1455_ = v___y_1480_;
v___y_1456_ = v___y_1484_;
v___y_1457_ = v___y_1481_;
v___y_1458_ = v___y_1485_;
v___y_1459_ = v___y_1486_;
v___y_1460_ = v___y_1486_;
goto v___jp_1452_;
}
else
{
lean_object* v_val_1488_; 
v_val_1488_ = lean_ctor_get(v___x_1487_, 0);
lean_inc(v_val_1488_);
lean_dec_ref_known(v___x_1487_, 1);
v___y_1453_ = v___y_1480_;
v___y_1454_ = v___y_1482_;
v___y_1455_ = v___y_1480_;
v___y_1456_ = v___y_1484_;
v___y_1457_ = v___y_1481_;
v___y_1458_ = v___y_1485_;
v___y_1459_ = v___y_1486_;
v___y_1460_ = v_val_1488_;
goto v___jp_1452_;
}
}
v___jp_1489_:
{
lean_object* v_toCold_1493_; lean_object* v_ref_1494_; uint8_t v_suppressElabErrors_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___f_1498_; lean_object* v_ref_1499_; lean_object* v___x_1500_; 
v_toCold_1493_ = lean_ctor_get(v___y_1412_, 0);
v_ref_1494_ = lean_ctor_get(v___y_1412_, 2);
v_suppressElabErrors_1495_ = lean_ctor_get_uint8(v___y_1412_, sizeof(void*)*3 + 2);
v___x_1496_ = lean_box(v_suppressElabErrors_1495_);
v___x_1497_ = lean_box(v___y_1490_);
v___f_1498_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1498_, 0, v___x_1496_);
lean_closure_set(v___f_1498_, 1, v___x_1497_);
v_ref_1499_ = l_Lean_replaceRef(v_ref_1406_, v_ref_1494_);
v___x_1500_ = l_Lean_Syntax_getPos_x3f(v_ref_1499_, v___y_1491_);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v___x_1501_; 
v___x_1501_ = lean_unsigned_to_nat(0u);
v___y_1480_ = v_toCold_1493_;
v___y_1481_ = v_suppressElabErrors_1495_;
v___y_1482_ = v___f_1498_;
v___y_1483_ = v_ref_1499_;
v___y_1484_ = v___y_1492_;
v___y_1485_ = v___y_1491_;
v___y_1486_ = v___x_1501_;
goto v___jp_1479_;
}
else
{
lean_object* v_val_1502_; 
v_val_1502_ = lean_ctor_get(v___x_1500_, 0);
lean_inc(v_val_1502_);
lean_dec_ref_known(v___x_1500_, 1);
v___y_1480_ = v_toCold_1493_;
v___y_1481_ = v_suppressElabErrors_1495_;
v___y_1482_ = v___f_1498_;
v___y_1483_ = v_ref_1499_;
v___y_1484_ = v___y_1492_;
v___y_1485_ = v___y_1491_;
v___y_1486_ = v_val_1502_;
goto v___jp_1479_;
}
}
v___jp_1504_:
{
if (v___y_1507_ == 0)
{
v___y_1490_ = v___y_1505_;
v___y_1491_ = v___y_1506_;
v___y_1492_ = v_severity_1408_;
goto v___jp_1489_;
}
else
{
v___y_1490_ = v___y_1505_;
v___y_1491_ = v___y_1506_;
v___y_1492_ = v___x_1503_;
goto v___jp_1489_;
}
}
v___jp_1508_:
{
if (v___y_1509_ == 0)
{
uint8_t v___x_1510_; uint8_t v___x_1511_; 
v___x_1510_ = 1;
v___x_1511_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1408_, v___x_1510_);
if (v___x_1511_ == 0)
{
v___y_1505_ = v___y_1509_;
v___y_1506_ = v___y_1509_;
v___y_1507_ = v___x_1511_;
goto v___jp_1504_;
}
else
{
lean_object* v___x_1512_; lean_object* v___x_1513_; uint8_t v___x_1514_; 
v___x_1512_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1412_);
v___x_1513_ = l_Lean_warningAsError;
v___x_1514_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4(v___x_1512_, v___x_1513_);
lean_dec_ref(v___x_1512_);
v___y_1505_ = v___y_1509_;
v___y_1506_ = v___y_1509_;
v___y_1507_ = v___x_1514_;
goto v___jp_1504_;
}
}
else
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
lean_dec_ref(v_msgData_1407_);
v___x_1515_ = lean_box(0);
v___x_1516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1515_);
return v___x_1516_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1406_ = stack[0].m_obj;
lean_object* v_msgData_1407_ = stack[1].m_obj;
uint8_t v_severity_1408_ = stack[2].m_num;
uint8_t v_isSilent_1409_ = stack[3].m_num;
lean_object* v___y_1410_ = stack[4].m_obj;
lean_object* v___y_1411_ = stack[5].m_obj;
lean_object* v___y_1412_ = stack[6].m_obj;
lean_object* v___y_1413_ = stack[7].m_obj;
lean_object* v_res_1519_;
v_res_1519_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44(v_ref_1406_, v_msgData_1407_, v_severity_1408_, v_isSilent_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
stack->m_obj
 = v_res_1519_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44___boxed(lean_object* v_ref_1520_, lean_object* v_msgData_1521_, lean_object* v_severity_1522_, lean_object* v_isSilent_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
uint8_t v_severity_boxed_1529_; uint8_t v_isSilent_boxed_1530_; lean_object* v_res_1531_; 
v_severity_boxed_1529_ = lean_unbox(v_severity_1522_);
v_isSilent_boxed_1530_ = lean_unbox(v_isSilent_1523_);
v_res_1531_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44(v_ref_1520_, v_msgData_1521_, v_severity_boxed_1529_, v_isSilent_boxed_1530_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v_ref_1520_);
return v_res_1531_;
}
}
lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42(lean_object* v_msgData_1532_, uint8_t v_severity_1533_, uint8_t v_isSilent_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
lean_object* v_ref_1540_; lean_object* v___x_1541_; 
v_ref_1540_ = lean_ctor_get(v___y_1537_, 2);
v___x_1541_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44(v_ref_1540_, v_msgData_1532_, v_severity_1533_, v_isSilent_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
return v___x_1541_;
}
}
LEAN_EXPORT void l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1532_ = stack[0].m_obj;
uint8_t v_severity_1533_ = stack[1].m_num;
uint8_t v_isSilent_1534_ = stack[2].m_num;
lean_object* v___y_1535_ = stack[3].m_obj;
lean_object* v___y_1536_ = stack[4].m_obj;
lean_object* v___y_1537_ = stack[5].m_obj;
lean_object* v___y_1538_ = stack[6].m_obj;
lean_object* v_res_1542_;
v_res_1542_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42(v_msgData_1532_, v_severity_1533_, v_isSilent_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
stack->m_obj
 = v_res_1542_;
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42___boxed(lean_object* v_msgData_1543_, lean_object* v_severity_1544_, lean_object* v_isSilent_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
uint8_t v_severity_boxed_1551_; uint8_t v_isSilent_boxed_1552_; lean_object* v_res_1553_; 
v_severity_boxed_1551_ = lean_unbox(v_severity_1544_);
v_isSilent_boxed_1552_ = lean_unbox(v_isSilent_1545_);
v_res_1553_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42(v_msgData_1543_, v_severity_boxed_1551_, v_isSilent_boxed_1552_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
return v_res_1553_;
}
}
lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38(lean_object* v_msgData_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_){
_start:
{
uint8_t v___x_1560_; uint8_t v___x_1561_; lean_object* v___x_1562_; 
v___x_1560_ = 1;
v___x_1561_ = 0;
v___x_1562_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42(v_msgData_1554_, v___x_1560_, v___x_1561_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
return v___x_1562_;
}
}
LEAN_EXPORT void l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1554_ = stack[0].m_obj;
lean_object* v___y_1555_ = stack[1].m_obj;
lean_object* v___y_1556_ = stack[2].m_obj;
lean_object* v___y_1557_ = stack[3].m_obj;
lean_object* v___y_1558_ = stack[4].m_obj;
lean_object* v_res_1563_;
v_res_1563_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38(v_msgData_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
stack->m_obj
 = v_res_1563_;
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38___boxed(lean_object* v_msgData_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
lean_object* v_res_1570_; 
v_res_1570_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38(v_msgData_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
return v_res_1570_;
}
}
lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37___redArg(lean_object* v_opt_1571_, lean_object* v___y_1572_){
_start:
{
lean_object* v___x_1574_; uint8_t v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1574_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1572_);
v___x_1575_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4(v___x_1574_, v_opt_1571_);
lean_dec_ref(v___x_1574_);
v___x_1576_ = lean_box(v___x_1575_);
v___x_1577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1576_);
return v___x_1577_;
}
}
LEAN_EXPORT void l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_opt_1571_ = stack[0].m_obj;
lean_object* v___y_1572_ = stack[1].m_obj;
lean_object* v_res_1578_;
v_res_1578_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37___redArg(v_opt_1571_, v___y_1572_);
stack->m_obj
 = v_res_1578_;
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37___redArg___boxed(lean_object* v_opt_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37___redArg(v_opt_1579_, v___y_1580_);
lean_dec_ref(v___y_1580_);
lean_dec_ref(v_opt_1579_);
return v_res_1582_;
}
}
lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32(lean_object* v_id_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_){
_start:
{
lean_object* v___x_1589_; lean_object* v_env_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1612_; 
v___x_1589_ = lean_st_ref_get(v___y_1587_);
v_env_1590_ = lean_ctor_get(v___x_1589_, 0);
lean_inc_ref(v_env_1590_);
lean_dec(v___x_1589_);
v___x_1591_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1592_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37___redArg(v___x_1591_, v___y_1586_);
v_a_1593_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1595_ = v___x_1592_;
v_isShared_1596_ = v_isSharedCheck_1612_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1592_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1612_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
uint8_t v_isExporting_1602_; 
v_isExporting_1602_ = lean_ctor_get_uint8(v_env_1590_, sizeof(void*)*13);
lean_dec_ref(v_env_1590_);
if (v_isExporting_1602_ == 0)
{
lean_dec(v_a_1593_);
lean_dec(v_id_1583_);
goto v___jp_1597_;
}
else
{
uint8_t v___x_1603_; 
v___x_1603_ = l_Lean_isPrivateName(v_id_1583_);
if (v___x_1603_ == 0)
{
lean_dec(v_a_1593_);
lean_dec(v_id_1583_);
goto v___jp_1597_;
}
else
{
uint8_t v___x_1604_; 
v___x_1604_ = lean_unbox(v_a_1593_);
lean_dec(v_a_1593_);
if (v___x_1604_ == 0)
{
lean_dec(v_id_1583_);
goto v___jp_1597_;
}
else
{
lean_object* v___x_1605_; uint8_t v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; 
lean_del_object(v___x_1595_);
v___x_1605_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___closed__1);
v___x_1606_ = 0;
v___x_1607_ = l_Lean_MessageData_ofConstName(v_id_1583_, v___x_1606_);
v___x_1608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1605_);
lean_ctor_set(v___x_1608_, 1, v___x_1607_);
v___x_1609_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___closed__3);
v___x_1610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1608_);
lean_ctor_set(v___x_1610_, 1, v___x_1609_);
v___x_1611_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38(v___x_1610_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_);
return v___x_1611_;
}
}
}
v___jp_1597_:
{
lean_object* v___x_1598_; lean_object* v___x_1600_; 
v___x_1598_ = lean_box(0);
if (v_isShared_1596_ == 0)
{
lean_ctor_set(v___x_1595_, 0, v___x_1598_);
v___x_1600_ = v___x_1595_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1598_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_1583_ = stack[0].m_obj;
lean_object* v___y_1584_ = stack[1].m_obj;
lean_object* v___y_1585_ = stack[2].m_obj;
lean_object* v___y_1586_ = stack[3].m_obj;
lean_object* v___y_1587_ = stack[4].m_obj;
lean_object* v_res_1613_;
v_res_1613_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32(v_id_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_);
stack->m_obj
 = v_res_1613_;
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___boxed(lean_object* v_id_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32(v_id_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
return v_res_1620_;
}
}
lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26(lean_object* v_id_1621_, uint8_t v_enableLog_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
lean_object* v___x_1628_; lean_object* v_toCold_1629_; lean_object* v_env_1630_; lean_object* v_currNamespace_1631_; lean_object* v_openDecls_1632_; lean_object* v___x_1633_; lean_object* v_res_1634_; lean_object* v___x_1635_; 
v___x_1628_ = lean_st_ref_get(v___y_1626_);
v_toCold_1629_ = lean_ctor_get(v___y_1625_, 0);
v_env_1630_ = lean_ctor_get(v___x_1628_, 0);
lean_inc_ref(v_env_1630_);
lean_dec(v___x_1628_);
v_currNamespace_1631_ = lean_ctor_get(v_toCold_1629_, 4);
v_openDecls_1632_ = lean_ctor_get(v_toCold_1629_, 5);
v___x_1633_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1625_);
lean_inc(v_openDecls_1632_);
lean_inc(v_currNamespace_1631_);
v_res_1634_ = l_Lean_ResolveName_resolveGlobalName(v_env_1630_, v___x_1633_, v_currNamespace_1631_, v_openDecls_1632_, v_id_1621_);
lean_dec_ref(v___x_1633_);
v___x_1635_ = lean_st_ref_get(v___y_1626_);
if (v_enableLog_1622_ == 0)
{
lean_object* v___x_1636_; 
lean_dec(v___x_1635_);
v___x_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1636_, 0, v_res_1634_);
return v___x_1636_;
}
else
{
lean_object* v_env_1637_; uint8_t v_isExporting_1638_; 
v_env_1637_ = lean_ctor_get(v___x_1635_, 0);
lean_inc_ref(v_env_1637_);
lean_dec(v___x_1635_);
v_isExporting_1638_ = lean_ctor_get_uint8(v_env_1637_, sizeof(void*)*13);
lean_dec_ref(v_env_1637_);
if (v_isExporting_1638_ == 0)
{
lean_object* v___x_1639_; 
v___x_1639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1639_, 0, v_res_1634_);
return v___x_1639_;
}
else
{
lean_object* v___x_1640_; 
v___x_1640_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__31(v_res_1634_);
if (lean_obj_tag(v___x_1640_) == 1)
{
lean_object* v_val_1641_; lean_object* v_fst_1642_; lean_object* v___x_1643_; 
v_val_1641_ = lean_ctor_get(v___x_1640_, 0);
lean_inc(v_val_1641_);
lean_dec_ref_known(v___x_1640_, 1);
v_fst_1642_ = lean_ctor_get(v_val_1641_, 0);
lean_inc(v_fst_1642_);
lean_dec(v_val_1641_);
v___x_1643_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32(v_fst_1642_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1650_ == 0)
{
lean_object* v_unused_1651_; 
v_unused_1651_ = lean_ctor_get(v___x_1643_, 0);
lean_dec(v_unused_1651_);
v___x_1645_ = v___x_1643_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_dec(v___x_1643_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 0, v_res_1634_);
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_res_1634_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
else
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
lean_dec(v_res_1634_);
v_a_1652_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v___x_1643_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1643_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1652_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
else
{
lean_object* v___x_1660_; 
lean_dec(v___x_1640_);
v___x_1660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1660_, 0, v_res_1634_);
return v___x_1660_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_1621_ = stack[0].m_obj;
uint8_t v_enableLog_1622_ = stack[1].m_num;
lean_object* v___y_1623_ = stack[2].m_obj;
lean_object* v___y_1624_ = stack[3].m_obj;
lean_object* v___y_1625_ = stack[4].m_obj;
lean_object* v___y_1626_ = stack[5].m_obj;
lean_object* v_res_1661_;
v_res_1661_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26(v_id_1621_, v_enableLog_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
stack->m_obj
 = v_res_1661_;
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26___boxed(lean_object* v_id_1662_, lean_object* v_enableLog_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_){
_start:
{
uint8_t v_enableLog_boxed_1669_; lean_object* v_res_1670_; 
v_enableLog_boxed_1669_ = lean_unbox(v_enableLog_1663_);
v_res_1670_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26(v_id_1662_, v_enableLog_boxed_1669_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1664_);
return v_res_1670_;
}
}
lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20(lean_object* v_view_1671_, lean_object* v_findLocalDecl_x3f_1672_, lean_object* v_n_1673_, lean_object* v_projs_1674_, uint8_t v_globalDeclFound_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
lean_object* v___y_1682_; lean_object* v___y_1683_; uint8_t v_globalDeclFoundNext_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v_imported_1691_; lean_object* v_ctx_1692_; lean_object* v_scopes_1693_; lean_object* v_givenNameView_1694_; uint8_t v___y_1696_; 
v_imported_1691_ = lean_ctor_get(v_view_1671_, 1);
v_ctx_1692_ = lean_ctor_get(v_view_1671_, 2);
v_scopes_1693_ = lean_ctor_get(v_view_1671_, 3);
lean_inc(v_scopes_1693_);
lean_inc(v_ctx_1692_);
lean_inc(v_imported_1691_);
lean_inc(v_n_1673_);
v_givenNameView_1694_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_givenNameView_1694_, 0, v_n_1673_);
lean_ctor_set(v_givenNameView_1694_, 1, v_imported_1691_);
lean_ctor_set(v_givenNameView_1694_, 2, v_ctx_1692_);
lean_ctor_set(v_givenNameView_1694_, 3, v_scopes_1693_);
if (v_globalDeclFound_1675_ == 0)
{
v___y_1696_ = v_globalDeclFound_1675_;
goto v___jp_1695_;
}
else
{
uint8_t v___x_1731_; 
v___x_1731_ = l_List_isEmpty___redArg(v_projs_1674_);
if (v___x_1731_ == 0)
{
v___y_1696_ = v_globalDeclFound_1675_;
goto v___jp_1695_;
}
else
{
uint8_t v___x_1732_; 
v___x_1732_ = 0;
v___y_1696_ = v___x_1732_;
goto v___jp_1695_;
}
}
v___jp_1681_:
{
lean_object* v___x_1689_; 
v___x_1689_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1689_, 0, v___y_1683_);
lean_ctor_set(v___x_1689_, 1, v_projs_1674_);
v_n_1673_ = v___y_1682_;
v_projs_1674_ = v___x_1689_;
v_globalDeclFound_1675_ = v_globalDeclFoundNext_1684_;
v___y_1676_ = v___y_1685_;
v___y_1677_ = v___y_1686_;
v___y_1678_ = v___y_1687_;
v___y_1679_ = v___y_1688_;
goto _start;
}
v___jp_1695_:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1697_ = lean_box(v___y_1696_);
lean_inc_ref(v_findLocalDecl_x3f_1672_);
lean_inc_ref(v_givenNameView_1694_);
v___x_1698_ = lean_apply_2(v_findLocalDecl_x3f_1672_, v_givenNameView_1694_, v___x_1697_);
if (lean_obj_tag(v___x_1698_) == 0)
{
if (lean_obj_tag(v_n_1673_) == 1)
{
if (v_globalDeclFound_1675_ == 0)
{
lean_object* v_pre_1699_; lean_object* v_str_1700_; uint8_t v_globalDeclFoundNext_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
v_pre_1699_ = lean_ctor_get(v_n_1673_, 0);
lean_inc(v_pre_1699_);
v_str_1700_ = lean_ctor_get(v_n_1673_, 1);
lean_inc_ref(v_str_1700_);
lean_dec_ref_known(v_n_1673_, 2);
v_globalDeclFoundNext_1701_ = 1;
v___x_1702_ = l_Lean_MacroScopesView_review(v_givenNameView_1694_);
v___x_1703_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26(v___x_1702_, v_globalDeclFound_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_object* v_a_1704_; lean_object* v___x_1705_; lean_object* v_r_1706_; uint8_t v___x_1707_; 
v_a_1704_ = lean_ctor_get(v___x_1703_, 0);
lean_inc(v_a_1704_);
lean_dec_ref_known(v___x_1703_, 1);
v___x_1705_ = lean_box(0);
v_r_1706_ = l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__27(v_a_1704_, v___x_1705_);
v___x_1707_ = l_List_isEmpty___redArg(v_r_1706_);
lean_dec(v_r_1706_);
if (v___x_1707_ == 0)
{
v___y_1682_ = v_pre_1699_;
v___y_1683_ = v_str_1700_;
v_globalDeclFoundNext_1684_ = v_globalDeclFoundNext_1701_;
v___y_1685_ = v___y_1676_;
v___y_1686_ = v___y_1677_;
v___y_1687_ = v___y_1678_;
v___y_1688_ = v___y_1679_;
goto v___jp_1681_;
}
else
{
v___y_1682_ = v_pre_1699_;
v___y_1683_ = v_str_1700_;
v_globalDeclFoundNext_1684_ = v_globalDeclFound_1675_;
v___y_1685_ = v___y_1676_;
v___y_1686_ = v___y_1677_;
v___y_1687_ = v___y_1678_;
v___y_1688_ = v___y_1679_;
goto v___jp_1681_;
}
}
else
{
lean_object* v_a_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1715_; 
lean_dec_ref(v_str_1700_);
lean_dec(v_pre_1699_);
lean_dec(v_projs_1674_);
lean_dec_ref(v_findLocalDecl_x3f_1672_);
v_a_1708_ = lean_ctor_get(v___x_1703_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1703_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1710_ = v___x_1703_;
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_a_1708_);
lean_dec(v___x_1703_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1713_; 
if (v_isShared_1711_ == 0)
{
v___x_1713_ = v___x_1710_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_a_1708_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
}
else
{
lean_object* v_pre_1716_; lean_object* v_str_1717_; 
lean_dec_ref_known(v_givenNameView_1694_, 4);
v_pre_1716_ = lean_ctor_get(v_n_1673_, 0);
lean_inc(v_pre_1716_);
v_str_1717_ = lean_ctor_get(v_n_1673_, 1);
lean_inc_ref(v_str_1717_);
lean_dec_ref_known(v_n_1673_, 2);
v___y_1682_ = v_pre_1716_;
v___y_1683_ = v_str_1717_;
v_globalDeclFoundNext_1684_ = v_globalDeclFound_1675_;
v___y_1685_ = v___y_1676_;
v___y_1686_ = v___y_1677_;
v___y_1687_ = v___y_1678_;
v___y_1688_ = v___y_1679_;
goto v___jp_1681_;
}
}
else
{
lean_object* v___x_1718_; lean_object* v___x_1719_; 
lean_dec_ref_known(v_givenNameView_1694_, 4);
lean_dec(v_projs_1674_);
lean_dec(v_n_1673_);
lean_dec_ref(v_findLocalDecl_x3f_1672_);
v___x_1718_ = lean_box(0);
v___x_1719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1718_);
return v___x_1719_;
}
}
else
{
lean_object* v_val_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1730_; 
lean_dec_ref_known(v_givenNameView_1694_, 4);
lean_dec(v_n_1673_);
lean_dec_ref(v_findLocalDecl_x3f_1672_);
v_val_1720_ = lean_ctor_get(v___x_1698_, 0);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1722_ = v___x_1698_;
v_isShared_1723_ = v_isSharedCheck_1730_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_val_1720_);
lean_dec(v___x_1698_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1730_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1727_; 
v___x_1724_ = l_Lean_LocalDecl_toExpr(v_val_1720_);
v___x_1725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1725_, 0, v___x_1724_);
lean_ctor_set(v___x_1725_, 1, v_projs_1674_);
if (v_isShared_1723_ == 0)
{
lean_ctor_set(v___x_1722_, 0, v___x_1725_);
v___x_1727_ = v___x_1722_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v___x_1725_);
v___x_1727_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
lean_object* v___x_1728_; 
v___x_1728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1727_);
return v___x_1728_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_0interp(lean_interpreter_value* stack)
{
lean_object* v_view_1671_ = stack[0].m_obj;
lean_object* v_findLocalDecl_x3f_1672_ = stack[1].m_obj;
lean_object* v_n_1673_ = stack[2].m_obj;
lean_object* v_projs_1674_ = stack[3].m_obj;
uint8_t v_globalDeclFound_1675_ = stack[4].m_num;
lean_object* v___y_1676_ = stack[5].m_obj;
lean_object* v___y_1677_ = stack[6].m_obj;
lean_object* v___y_1678_ = stack[7].m_obj;
lean_object* v___y_1679_ = stack[8].m_obj;
lean_object* v_res_1733_;
v_res_1733_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20(v_view_1671_, v_findLocalDecl_x3f_1672_, v_n_1673_, v_projs_1674_, v_globalDeclFound_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
stack->m_obj
 = v_res_1733_;
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20___boxed(lean_object* v_view_1734_, lean_object* v_findLocalDecl_x3f_1735_, lean_object* v_n_1736_, lean_object* v_projs_1737_, lean_object* v_globalDeclFound_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
uint8_t v_globalDeclFound_boxed_1744_; lean_object* v_res_1745_; 
v_globalDeclFound_boxed_1744_ = lean_unbox(v_globalDeclFound_1738_);
v_res_1745_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20(v_view_1734_, v_findLocalDecl_x3f_1735_, v_n_1736_, v_projs_1737_, v_globalDeclFound_boxed_1744_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec_ref(v_view_1734_);
return v_res_1745_;
}
}
lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11(lean_object* v_n_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
lean_object* v_lctx_1752_; lean_object* v_toCold_1753_; lean_object* v_decls_1754_; lean_object* v_auxDeclToFullName_1755_; lean_object* v_currNamespace_1756_; lean_object* v_view_1757_; lean_object* v_name_1758_; lean_object* v_findLocalDecl_x3f_1759_; lean_object* v___x_1760_; uint8_t v___x_1761_; lean_object* v___x_1762_; 
v_lctx_1752_ = lean_ctor_get(v___y_1747_, 2);
v_toCold_1753_ = lean_ctor_get(v___y_1749_, 0);
v_decls_1754_ = lean_ctor_get(v_lctx_1752_, 1);
v_auxDeclToFullName_1755_ = lean_ctor_get(v_lctx_1752_, 2);
v_currNamespace_1756_ = lean_ctor_get(v_toCold_1753_, 4);
v_view_1757_ = l_Lean_extractMacroScopes(v_n_1746_);
v_name_1758_ = lean_ctor_get(v_view_1757_, 0);
lean_inc(v_name_1758_);
lean_inc_ref(v_decls_1754_);
lean_inc(v_currNamespace_1756_);
lean_inc(v_auxDeclToFullName_1755_);
v_findLocalDecl_x3f_1759_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11___lam__0___boxed), 5, 3);
lean_closure_set(v_findLocalDecl_x3f_1759_, 0, v_auxDeclToFullName_1755_);
lean_closure_set(v_findLocalDecl_x3f_1759_, 1, v_currNamespace_1756_);
lean_closure_set(v_findLocalDecl_x3f_1759_, 2, v_decls_1754_);
v___x_1760_ = lean_box(0);
v___x_1761_ = 0;
v___x_1762_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20(v_view_1757_, v_findLocalDecl_x3f_1759_, v_name_1758_, v___x_1760_, v___x_1761_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
lean_dec_ref(v_view_1757_);
return v___x_1762_;
}
}
LEAN_EXPORT void l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1746_ = stack[0].m_obj;
lean_object* v___y_1747_ = stack[1].m_obj;
lean_object* v___y_1748_ = stack[2].m_obj;
lean_object* v___y_1749_ = stack[3].m_obj;
lean_object* v___y_1750_ = stack[4].m_obj;
lean_object* v_res_1763_;
v_res_1763_ = l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11(v_n_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
stack->m_obj
 = v_res_1763_;
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11___boxed(lean_object* v_n_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11(v_n_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
return v_res_1770_;
}
}
lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5___lam__0(uint8_t v___x_1771_, lean_object* v_n_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
lean_object* v___x_1778_; 
v___x_1778_ = l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11(v_n_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1792_; 
v_a_1779_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1781_ = v___x_1778_;
v_isShared_1782_ = v_isSharedCheck_1792_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1778_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1792_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
if (lean_obj_tag(v_a_1779_) == 0)
{
uint8_t v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1786_; 
v___x_1783_ = 1;
v___x_1784_ = lean_box(v___x_1783_);
if (v_isShared_1782_ == 0)
{
lean_ctor_set(v___x_1781_, 0, v___x_1784_);
v___x_1786_ = v___x_1781_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1784_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
else
{
lean_object* v___x_1788_; lean_object* v___x_1790_; 
lean_dec_ref_known(v_a_1779_, 1);
v___x_1788_ = lean_box(v___x_1771_);
if (v_isShared_1782_ == 0)
{
lean_ctor_set(v___x_1781_, 0, v___x_1788_);
v___x_1790_ = v___x_1781_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1788_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
}
else
{
lean_object* v_a_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1800_; 
v_a_1793_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1795_ = v___x_1778_;
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_a_1793_);
lean_dec(v___x_1778_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1796_ == 0)
{
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_a_1793_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1771_ = stack[0].m_num;
lean_object* v_n_1772_ = stack[1].m_obj;
lean_object* v___y_1773_ = stack[2].m_obj;
lean_object* v___y_1774_ = stack[3].m_obj;
lean_object* v___y_1775_ = stack[4].m_obj;
lean_object* v___y_1776_ = stack[5].m_obj;
lean_object* v_res_1801_;
v_res_1801_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5___lam__0(v___x_1771_, v_n_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_);
stack->m_obj
 = v_res_1801_;
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5___lam__0___boxed(lean_object* v___x_1802_, lean_object* v_n_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
uint8_t v___x_46477__boxed_1809_; lean_object* v_res_1810_; 
v___x_46477__boxed_1809_ = lean_unbox(v___x_1802_);
v_res_1810_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5___lam__0(v___x_46477__boxed_1809_, v_n_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
return v_res_1810_;
}
}
lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5(lean_object* v_n_u2080_1814_, uint8_t v_fullNames_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
uint8_t v___x_1821_; lean_object* v___f_1822_; lean_object* v___x_1823_; 
v___x_1821_ = 0;
v___f_1822_ = ((lean_object*)(l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5___closed__0));
v___x_1823_ = l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12(v_n_u2080_1814_, v_fullNames_1815_, v___x_1821_, v___f_1822_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
return v___x_1823_;
}
}
LEAN_EXPORT void l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_u2080_1814_ = stack[0].m_obj;
uint8_t v_fullNames_1815_ = stack[1].m_num;
lean_object* v___y_1816_ = stack[2].m_obj;
lean_object* v___y_1817_ = stack[3].m_obj;
lean_object* v___y_1818_ = stack[4].m_obj;
lean_object* v___y_1819_ = stack[5].m_obj;
lean_object* v_res_1824_;
v_res_1824_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5(v_n_u2080_1814_, v_fullNames_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
stack->m_obj
 = v_res_1824_;
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5___boxed(lean_object* v_n_u2080_1825_, lean_object* v_fullNames_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
uint8_t v_fullNames_boxed_1832_; lean_object* v_res_1833_; 
v_fullNames_boxed_1832_ = lean_unbox(v_fullNames_1826_);
v_res_1833_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5(v_n_u2080_1825_, v_fullNames_boxed_1832_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
return v_res_1833_;
}
}
lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3_spec__8___redArg(lean_object* v_o_1834_, lean_object* v___y_1835_){
_start:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v_env_1839_; lean_object* v___x_1840_; lean_object* v_toEnvExtension_1841_; lean_object* v_asyncMode_1842_; lean_object* v___x_1843_; uint8_t v___x_1844_; lean_object* v___x_1845_; lean_object* v_merged_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1854_; 
v___x_1837_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_1838_ = lean_st_ref_get(v___y_1835_);
v_env_1839_ = lean_ctor_get(v___x_1838_, 0);
lean_inc_ref(v_env_1839_);
lean_dec(v___x_1838_);
v___x_1840_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_1841_ = lean_ctor_get(v___x_1840_, 0);
v_asyncMode_1842_ = lean_ctor_get(v_toEnvExtension_1841_, 2);
v___x_1843_ = lean_box(0);
v___x_1844_ = 0;
v___x_1845_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1837_, v___x_1840_, v_env_1839_, v_asyncMode_1842_, v___x_1843_, v___x_1844_);
v_merged_1846_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1854_ == 0)
{
lean_object* v_unused_1855_; 
v_unused_1855_ = lean_ctor_get(v___x_1845_, 1);
lean_dec(v_unused_1855_);
v___x_1848_ = v___x_1845_;
v_isShared_1849_ = v_isSharedCheck_1854_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_merged_1846_);
lean_dec(v___x_1845_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1854_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1851_; 
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 1, v_merged_1846_);
lean_ctor_set(v___x_1848_, 0, v_o_1834_);
v___x_1851_ = v___x_1848_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_o_1834_);
lean_ctor_set(v_reuseFailAlloc_1853_, 1, v_merged_1846_);
v___x_1851_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
lean_object* v___x_1852_; 
v___x_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1851_);
return v___x_1852_;
}
}
}
}
LEAN_EXPORT void l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_1834_ = stack[0].m_obj;
lean_object* v___y_1835_ = stack[1].m_obj;
lean_object* v_res_1856_;
v_res_1856_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3_spec__8___redArg(v_o_1834_, v___y_1835_);
stack->m_obj
 = v_res_1856_;
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3_spec__8___redArg___boxed(lean_object* v_o_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3_spec__8___redArg(v_o_1857_, v___y_1858_);
lean_dec(v___y_1858_);
return v_res_1860_;
}
}
lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3(lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1864_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1861_);
v___x_1865_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3_spec__8___redArg(v___x_1864_, v___y_1862_);
return v___x_1865_;
}
}
LEAN_EXPORT void l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1861_ = stack[0].m_obj;
lean_object* v___y_1862_ = stack[1].m_obj;
lean_object* v_res_1866_;
v_res_1866_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3(v___y_1861_, v___y_1862_);
stack->m_obj
 = v_res_1866_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3___boxed(lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3(v___y_1867_, v___y_1868_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___lam__0(lean_object* v___x_1871_, lean_object* v_entry_1872_, lean_object* v_s_1873_){
_start:
{
lean_object* v_addEntryFn_1874_; lean_object* v_importedEntries_1875_; lean_object* v_state_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1884_; 
v_addEntryFn_1874_ = lean_ctor_get(v___x_1871_, 3);
lean_inc(v_addEntryFn_1874_);
lean_dec_ref(v___x_1871_);
v_importedEntries_1875_ = lean_ctor_get(v_s_1873_, 0);
v_state_1876_ = lean_ctor_get(v_s_1873_, 1);
v_isSharedCheck_1884_ = !lean_is_exclusive(v_s_1873_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1878_ = v_s_1873_;
v_isShared_1879_ = v_isSharedCheck_1884_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_state_1876_);
lean_inc(v_importedEntries_1875_);
lean_dec(v_s_1873_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1884_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v_state_1880_; lean_object* v___x_1882_; 
v_state_1880_ = lean_apply_2(v_addEntryFn_1874_, v_state_1876_, v_entry_1872_);
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 1, v_state_1880_);
v___x_1882_ = v___x_1878_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_importedEntries_1875_);
lean_ctor_set(v_reuseFailAlloc_1883_, 1, v_state_1880_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1885_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1886_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_1887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1887_, 0, v___x_1886_);
return v___x_1887_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1888_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1889_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_1890_ = lean_unsigned_to_nat(0u);
v___x_1891_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1890_);
lean_ctor_set(v___x_1891_, 1, v___x_1890_);
lean_ctor_set(v___x_1891_, 2, v___x_1890_);
lean_ctor_set(v___x_1891_, 3, v___x_1890_);
lean_ctor_set(v___x_1891_, 4, v___x_1889_);
lean_ctor_set(v___x_1891_, 5, v___x_1889_);
lean_ctor_set(v___x_1891_, 6, v___x_1889_);
lean_ctor_set(v___x_1891_, 7, v___x_1889_);
lean_ctor_set(v___x_1891_, 8, v___x_1889_);
lean_ctor_set(v___x_1891_, 9, v___x_1889_);
lean_ctor_set(v___x_1891_, 10, v___x_1889_);
lean_ctor_set(v___x_1891_, 11, v___x_1888_);
return v___x_1891_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1892_ = lean_unsigned_to_nat(32u);
v___x_1893_ = lean_mk_empty_array_with_capacity(v___x_1892_);
v___x_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1893_);
return v___x_1894_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1895_ = ((size_t)5ULL);
v___x_1896_ = lean_unsigned_to_nat(0u);
v___x_1897_ = lean_unsigned_to_nat(32u);
v___x_1898_ = lean_mk_empty_array_with_capacity(v___x_1897_);
v___x_1899_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_1900_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1900_, 0, v___x_1899_);
lean_ctor_set(v___x_1900_, 1, v___x_1898_);
lean_ctor_set(v___x_1900_, 2, v___x_1896_);
lean_ctor_set(v___x_1900_, 3, v___x_1896_);
lean_ctor_set_usize(v___x_1900_, 4, v___x_1895_);
return v___x_1900_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1901_ = lean_box(1);
v___x_1902_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_1903_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_1904_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1903_);
lean_ctor_set(v___x_1904_, 1, v___x_1902_);
lean_ctor_set(v___x_1904_, 2, v___x_1901_);
return v___x_1904_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_){
_start:
{
lean_object* v___x_1909_; lean_object* v_toCold_1910_; lean_object* v_env_1911_; lean_object* v_options_1912_; uint8_t v___x_1913_; lean_object* v_env_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1909_ = lean_st_ref_get(v___y_1907_);
v_toCold_1910_ = lean_ctor_get(v___y_1906_, 0);
v_env_1911_ = lean_ctor_get(v___x_1909_, 0);
lean_inc_ref(v_env_1911_);
lean_dec(v___x_1909_);
v_options_1912_ = lean_ctor_get(v_toCold_1910_, 2);
v___x_1913_ = 0;
v_env_1914_ = l_Lean_Environment_setRecordingDeps(v_env_1911_, v___x_1913_);
v___x_1915_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_1916_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_1912_);
v___x_1917_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1917_, 0, v_env_1914_);
lean_ctor_set(v___x_1917_, 1, v___x_1915_);
lean_ctor_set(v___x_1917_, 2, v___x_1916_);
lean_ctor_set(v___x_1917_, 3, v_options_1912_);
v___x_1918_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1917_);
lean_ctor_set(v___x_1918_, 1, v_msgData_1905_);
v___x_1919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1918_);
return v___x_1919_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1905_ = stack[0].m_obj;
lean_object* v___y_1906_ = stack[1].m_obj;
lean_object* v___y_1907_ = stack[2].m_obj;
lean_object* v_res_1920_;
v_res_1920_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0(v_msgData_1905_, v___y_1906_, v___y_1907_);
stack->m_obj
 = v_res_1920_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0(v_msgData_1921_, v___y_1922_, v___y_1923_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
return v_res_1925_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0(void){
_start:
{
lean_object* v___x_1926_; double v___x_1927_; 
v___x_1926_ = lean_unsigned_to_nat(0u);
v___x_1927_ = lean_float_of_nat(v___x_1926_);
return v___x_1927_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__9(lean_object* v_cls_1930_, lean_object* v_msg_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_){
_start:
{
lean_object* v_ref_1935_; lean_object* v___x_1936_; lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1982_; 
v_ref_1935_ = lean_ctor_get(v___y_1932_, 2);
v___x_1936_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0(v_msg_1931_, v___y_1932_, v___y_1933_);
v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1939_ = v___x_1936_;
v_isShared_1940_ = v_isSharedCheck_1982_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1936_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1982_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1941_; lean_object* v_traceState_1942_; lean_object* v_env_1943_; lean_object* v_nextMacroScope_1944_; lean_object* v_ngen_1945_; lean_object* v_auxDeclNGen_1946_; lean_object* v_cache_1947_; lean_object* v_recordedDeps_1948_; lean_object* v_messages_1949_; lean_object* v_infoState_1950_; lean_object* v_snapshotTasks_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1981_; 
v___x_1941_ = lean_st_ref_take(v___y_1933_);
v_traceState_1942_ = lean_ctor_get(v___x_1941_, 4);
v_env_1943_ = lean_ctor_get(v___x_1941_, 0);
v_nextMacroScope_1944_ = lean_ctor_get(v___x_1941_, 1);
v_ngen_1945_ = lean_ctor_get(v___x_1941_, 2);
v_auxDeclNGen_1946_ = lean_ctor_get(v___x_1941_, 3);
v_cache_1947_ = lean_ctor_get(v___x_1941_, 5);
v_recordedDeps_1948_ = lean_ctor_get(v___x_1941_, 6);
v_messages_1949_ = lean_ctor_get(v___x_1941_, 7);
v_infoState_1950_ = lean_ctor_get(v___x_1941_, 8);
v_snapshotTasks_1951_ = lean_ctor_get(v___x_1941_, 9);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1953_ = v___x_1941_;
v_isShared_1954_ = v_isSharedCheck_1981_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_snapshotTasks_1951_);
lean_inc(v_infoState_1950_);
lean_inc(v_messages_1949_);
lean_inc(v_recordedDeps_1948_);
lean_inc(v_cache_1947_);
lean_inc(v_traceState_1942_);
lean_inc(v_auxDeclNGen_1946_);
lean_inc(v_ngen_1945_);
lean_inc(v_nextMacroScope_1944_);
lean_inc(v_env_1943_);
lean_dec(v___x_1941_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1981_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
uint64_t v_tid_1955_; lean_object* v_traces_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1980_; 
v_tid_1955_ = lean_ctor_get_uint64(v_traceState_1942_, sizeof(void*)*1);
v_traces_1956_ = lean_ctor_get(v_traceState_1942_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v_traceState_1942_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1958_ = v_traceState_1942_;
v_isShared_1959_ = v_isSharedCheck_1980_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_traces_1956_);
lean_dec(v_traceState_1942_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1980_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; double v___x_1962_; uint8_t v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1971_; 
v___x_1960_ = lean_box(0);
v___x_1961_ = lean_box(0);
v___x_1962_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0);
v___x_1963_ = 0;
v___x_1964_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48___closed__0));
v___x_1965_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1965_, 0, v_cls_1930_);
lean_ctor_set(v___x_1965_, 1, v___x_1961_);
lean_ctor_set(v___x_1965_, 2, v___x_1964_);
lean_ctor_set_float(v___x_1965_, sizeof(void*)*3, v___x_1962_);
lean_ctor_set_float(v___x_1965_, sizeof(void*)*3 + 8, v___x_1962_);
lean_ctor_set_uint8(v___x_1965_, sizeof(void*)*3 + 16, v___x_1963_);
v___x_1966_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__1));
v___x_1967_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1965_);
lean_ctor_set(v___x_1967_, 1, v_a_1937_);
lean_ctor_set(v___x_1967_, 2, v___x_1966_);
lean_inc(v_ref_1935_);
v___x_1968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1968_, 0, v_ref_1935_);
lean_ctor_set(v___x_1968_, 1, v___x_1967_);
v___x_1969_ = l_Lean_PersistentArray_push___redArg(v_traces_1956_, v___x_1968_);
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 0, v___x_1969_);
v___x_1971_ = v___x_1958_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v___x_1969_);
lean_ctor_set_uint64(v_reuseFailAlloc_1979_, sizeof(void*)*1, v_tid_1955_);
v___x_1971_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
lean_object* v___x_1973_; 
if (v_isShared_1954_ == 0)
{
lean_ctor_set(v___x_1953_, 4, v___x_1971_);
v___x_1973_ = v___x_1953_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_env_1943_);
lean_ctor_set(v_reuseFailAlloc_1978_, 1, v_nextMacroScope_1944_);
lean_ctor_set(v_reuseFailAlloc_1978_, 2, v_ngen_1945_);
lean_ctor_set(v_reuseFailAlloc_1978_, 3, v_auxDeclNGen_1946_);
lean_ctor_set(v_reuseFailAlloc_1978_, 4, v___x_1971_);
lean_ctor_set(v_reuseFailAlloc_1978_, 5, v_cache_1947_);
lean_ctor_set(v_reuseFailAlloc_1978_, 6, v_recordedDeps_1948_);
lean_ctor_set(v_reuseFailAlloc_1978_, 7, v_messages_1949_);
lean_ctor_set(v_reuseFailAlloc_1978_, 8, v_infoState_1950_);
lean_ctor_set(v_reuseFailAlloc_1978_, 9, v_snapshotTasks_1951_);
v___x_1973_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
lean_object* v___x_1974_; lean_object* v___x_1976_; 
v___x_1974_ = lean_st_ref_put(v___y_1933_, v___x_1973_);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 0, v___x_1960_);
v___x_1976_ = v___x_1939_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v___x_1960_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1930_ = stack[0].m_obj;
lean_object* v_msg_1931_ = stack[1].m_obj;
lean_object* v___y_1932_ = stack[2].m_obj;
lean_object* v___y_1933_ = stack[3].m_obj;
lean_object* v_res_1983_;
v_res_1983_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__9(v_cls_1930_, v_msg_1931_, v___y_1932_, v___y_1933_);
stack->m_obj
 = v_res_1983_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__9___boxed(lean_object* v_cls_1984_, lean_object* v_msg_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__9(v_cls_1984_, v_msg_1985_, v___y_1986_, v___y_1987_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
return v_res_1989_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17___redArg(lean_object* v_keys_1990_, lean_object* v_i_1991_, lean_object* v_k_1992_){
_start:
{
lean_object* v___x_1993_; uint8_t v___x_1994_; 
v___x_1993_ = lean_array_get_size(v_keys_1990_);
v___x_1994_ = lean_nat_dec_lt(v_i_1991_, v___x_1993_);
if (v___x_1994_ == 0)
{
lean_dec(v_i_1991_);
return v___x_1994_;
}
else
{
lean_object* v_k_x27_1995_; uint8_t v___x_1996_; 
v_k_x27_1995_ = lean_array_fget_borrowed(v_keys_1990_, v_i_1991_);
v___x_1996_ = l_Lean_instBEqExtraModUse_beq(v_k_1992_, v_k_x27_1995_);
if (v___x_1996_ == 0)
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1997_ = lean_unsigned_to_nat(1u);
v___x_1998_ = lean_nat_add(v_i_1991_, v___x_1997_);
lean_dec(v_i_1991_);
v_i_1991_ = v___x_1998_;
goto _start;
}
else
{
lean_dec(v_i_1991_);
return v___x_1994_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_1990_ = stack[0].m_obj;
lean_object* v_i_1991_ = stack[1].m_obj;
lean_object* v_k_1992_ = stack[2].m_obj;
uint8_t v_res_2000_;
v_res_2000_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17___redArg(v_keys_1990_, v_i_1991_, v_k_1992_);
stack->m_num = v_res_2000_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17___redArg___boxed(lean_object* v_keys_2001_, lean_object* v_i_2002_, lean_object* v_k_2003_){
_start:
{
uint8_t v_res_2004_; lean_object* v_r_2005_; 
v_res_2004_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17___redArg(v_keys_2001_, v_i_2002_, v_k_2003_);
lean_dec_ref(v_k_2003_);
lean_dec_ref(v_keys_2001_);
v_r_2005_ = lean_box(v_res_2004_);
return v_r_2005_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12___redArg(lean_object* v_x_2006_, size_t v_x_2007_, lean_object* v_x_2008_){
_start:
{
if (lean_obj_tag(v_x_2006_) == 0)
{
lean_object* v_es_2009_; lean_object* v___x_2010_; size_t v___x_2011_; size_t v___x_2012_; lean_object* v_j_2013_; lean_object* v___x_2014_; 
v_es_2009_ = lean_ctor_get(v_x_2006_, 0);
v___x_2010_ = lean_box(2);
v___x_2011_ = ((size_t)31ULL);
v___x_2012_ = lean_usize_land(v_x_2007_, v___x_2011_);
v_j_2013_ = lean_usize_to_nat(v___x_2012_);
v___x_2014_ = lean_array_get_borrowed(v___x_2010_, v_es_2009_, v_j_2013_);
lean_dec(v_j_2013_);
switch(lean_obj_tag(v___x_2014_))
{
case 0:
{
lean_object* v_key_2015_; uint8_t v___x_2016_; 
v_key_2015_ = lean_ctor_get(v___x_2014_, 0);
v___x_2016_ = l_Lean_instBEqExtraModUse_beq(v_x_2008_, v_key_2015_);
return v___x_2016_;
}
case 1:
{
lean_object* v_node_2017_; size_t v___x_2018_; size_t v___x_2019_; 
v_node_2017_ = lean_ctor_get(v___x_2014_, 0);
v___x_2018_ = ((size_t)5ULL);
v___x_2019_ = lean_usize_shift_right(v_x_2007_, v___x_2018_);
v_x_2006_ = v_node_2017_;
v_x_2007_ = v___x_2019_;
goto _start;
}
default: 
{
uint8_t v___x_2021_; 
v___x_2021_ = 0;
return v___x_2021_;
}
}
}
else
{
lean_object* v_ks_2022_; lean_object* v___x_2023_; uint8_t v___x_2024_; 
v_ks_2022_ = lean_ctor_get(v_x_2006_, 0);
v___x_2023_ = lean_unsigned_to_nat(0u);
v___x_2024_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17___redArg(v_ks_2022_, v___x_2023_, v_x_2008_);
return v___x_2024_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2006_ = stack[0].m_obj;
size_t v_x_2007_ = stack[1].m_num;
lean_object* v_x_2008_ = stack[2].m_obj;
uint8_t v_res_2025_;
v_res_2025_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12___redArg(v_x_2006_, v_x_2007_, v_x_2008_);
stack->m_num = v_res_2025_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12___redArg___boxed(lean_object* v_x_2026_, lean_object* v_x_2027_, lean_object* v_x_2028_){
_start:
{
size_t v_x_47015__boxed_2029_; uint8_t v_res_2030_; lean_object* v_r_2031_; 
v_x_47015__boxed_2029_ = lean_unbox_usize(v_x_2027_);
lean_dec(v_x_2027_);
v_res_2030_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12___redArg(v_x_2026_, v_x_47015__boxed_2029_, v_x_2028_);
lean_dec_ref(v_x_2028_);
lean_dec_ref(v_x_2026_);
v_r_2031_ = lean_box(v_res_2030_);
return v_r_2031_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg(lean_object* v_x_2032_, lean_object* v_x_2033_){
_start:
{
uint64_t v___x_2034_; size_t v___x_2035_; uint8_t v___x_2036_; 
v___x_2034_ = l_Lean_instHashableExtraModUse_hash(v_x_2033_);
v___x_2035_ = lean_uint64_to_usize(v___x_2034_);
v___x_2036_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12___redArg(v_x_2032_, v___x_2035_, v_x_2033_);
return v___x_2036_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2032_ = stack[0].m_obj;
lean_object* v_x_2033_ = stack[1].m_obj;
uint8_t v_res_2037_;
v_res_2037_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg(v_x_2032_, v_x_2033_);
stack->m_num = v_res_2037_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_x_2038_, lean_object* v_x_2039_){
_start:
{
uint8_t v_res_2040_; lean_object* v_r_2041_; 
v_res_2040_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg(v_x_2038_, v_x_2039_);
lean_dec_ref(v_x_2039_);
lean_dec_ref(v_x_2038_);
v_r_2041_ = lean_box(v_res_2040_);
return v_r_2041_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__0(void){
_start:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2042_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_2043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2043_, 0, v___x_2042_);
return v___x_2043_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2044_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__0);
v___x_2045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2044_);
lean_ctor_set(v___x_2045_, 1, v___x_2044_);
return v___x_2045_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__2(void){
_start:
{
lean_object* v___x_2046_; 
v___x_2046_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_2046_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__6(void){
_start:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2051_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__5));
v___x_2052_ = l_Lean_stringToMessageData(v___x_2051_);
return v___x_2052_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__8(void){
_start:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2054_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__7));
v___x_2055_ = l_Lean_stringToMessageData(v___x_2054_);
return v___x_2055_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__9(void){
_start:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2056_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48___closed__0));
v___x_2057_ = l_Lean_stringToMessageData(v___x_2056_);
return v___x_2057_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__11(void){
_start:
{
lean_object* v_cls_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
v_cls_2060_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__4));
v___x_2061_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__10));
v___x_2062_ = l_Lean_Name_append(v___x_2061_, v_cls_2060_);
return v___x_2062_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__13(void){
_start:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2064_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__12));
v___x_2065_ = l_Lean_stringToMessageData(v___x_2064_);
return v___x_2065_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__14(void){
_start:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2066_ = ((lean_object*)(l_Lean_Linter_mkSinceHint___closed__5));
v___x_2067_ = l_Lean_stringToMessageData(v___x_2066_);
return v___x_2067_;
}
}
lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4(lean_object* v_mod_2072_, uint8_t v_isMeta_2073_, lean_object* v_hint_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_){
_start:
{
lean_object* v___y_2079_; lean_object* v___y_2080_; lean_object* v___y_2081_; lean_object* v___y_2082_; lean_object* v___y_2083_; lean_object* v___y_2084_; lean_object* v___y_2085_; lean_object* v___y_2086_; lean_object* v___y_2087_; lean_object* v___y_2088_; lean_object* v___y_2089_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v_env_2096_; uint8_t v_isExporting_2097_; lean_object* v_entry_2098_; lean_object* v___x_2099_; lean_object* v_env_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; uint8_t v___x_2105_; 
v___x_2094_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__2);
v___x_2095_ = lean_st_ref_get(v___y_2076_);
v_env_2096_ = lean_ctor_get(v___x_2095_, 0);
lean_inc_ref(v_env_2096_);
lean_dec(v___x_2095_);
v_isExporting_2097_ = lean_ctor_get_uint8(v_env_2096_, sizeof(void*)*13);
lean_dec_ref(v_env_2096_);
lean_inc(v_mod_2072_);
v_entry_2098_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2098_, 0, v_mod_2072_);
lean_ctor_set_uint8(v_entry_2098_, sizeof(void*)*1, v_isExporting_2097_);
lean_ctor_set_uint8(v_entry_2098_, sizeof(void*)*1 + 1, v_isMeta_2073_);
v___x_2099_ = lean_st_ref_get(v___y_2076_);
v_env_2100_ = lean_ctor_get(v___x_2099_, 0);
lean_inc_ref(v_env_2100_);
lean_dec(v___x_2099_);
v___x_2101_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2102_ = lean_box(1);
v___x_2103_ = lean_box(0);
v___x_2104_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2094_, v___x_2101_, v_env_2100_, v___x_2102_, v___x_2103_);
v___x_2105_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg(v___x_2104_, v_entry_2098_);
lean_dec(v___x_2104_);
if (v___x_2105_ == 0)
{
lean_object* v_toCold_2106_; lean_object* v_options_2107_; lean_object* v_inheritedTraceOptions_2108_; uint8_t v_hasTrace_2109_; lean_object* v___f_2110_; uint8_t v___x_2111_; lean_object* v___y_2113_; 
v_toCold_2106_ = lean_ctor_get(v___y_2075_, 0);
v_options_2107_ = lean_ctor_get(v_toCold_2106_, 2);
v_inheritedTraceOptions_2108_ = lean_ctor_get(v_toCold_2106_, 11);
v_hasTrace_2109_ = lean_ctor_get_uint8(v_options_2107_, sizeof(void*)*1);
v___f_2110_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___lam__0), 3, 2);
lean_closure_set(v___f_2110_, 0, v___x_2101_);
lean_closure_set(v___f_2110_, 1, v_entry_2098_);
v___x_2111_ = 1;
if (v_hasTrace_2109_ == 0)
{
lean_dec(v_hint_2074_);
lean_dec(v_mod_2072_);
v___y_2113_ = v___y_2076_;
goto v___jp_2112_;
}
else
{
lean_object* v_cls_2131_; lean_object* v___y_2133_; lean_object* v___y_2134_; lean_object* v___y_2138_; lean_object* v___y_2139_; lean_object* v___x_2151_; uint8_t v___x_2152_; 
v_cls_2131_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__4));
v___x_2151_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__11);
v___x_2152_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2108_, v_options_2107_, v___x_2151_);
if (v___x_2152_ == 0)
{
lean_dec(v_hint_2074_);
lean_dec(v_mod_2072_);
v___y_2113_ = v___y_2076_;
goto v___jp_2112_;
}
else
{
lean_object* v___x_2153_; lean_object* v___y_2155_; 
v___x_2153_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__13);
if (v_isExporting_2097_ == 0)
{
lean_object* v___x_2162_; 
v___x_2162_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__17));
v___y_2155_ = v___x_2162_;
goto v___jp_2154_;
}
else
{
lean_object* v___x_2163_; 
v___x_2163_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__18));
v___y_2155_ = v___x_2163_;
goto v___jp_2154_;
}
v___jp_2154_:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
lean_inc_ref(v___y_2155_);
v___x_2156_ = l_Lean_stringToMessageData(v___y_2155_);
v___x_2157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2153_);
lean_ctor_set(v___x_2157_, 1, v___x_2156_);
v___x_2158_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__14);
v___x_2159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2157_);
lean_ctor_set(v___x_2159_, 1, v___x_2158_);
if (v_isMeta_2073_ == 0)
{
lean_object* v___x_2160_; 
v___x_2160_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__15));
v___y_2138_ = v___x_2159_;
v___y_2139_ = v___x_2160_;
goto v___jp_2137_;
}
else
{
lean_object* v___x_2161_; 
v___x_2161_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__16));
v___y_2138_ = v___x_2159_;
v___y_2139_ = v___x_2161_;
goto v___jp_2137_;
}
}
}
v___jp_2132_:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2135_, 0, v___y_2133_);
lean_ctor_set(v___x_2135_, 1, v___y_2134_);
v___x_2136_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__9(v_cls_2131_, v___x_2135_, v___y_2075_, v___y_2076_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_dec_ref_known(v___x_2136_, 1);
v___y_2113_ = v___y_2076_;
goto v___jp_2112_;
}
else
{
lean_dec_ref(v___f_2110_);
return v___x_2136_;
}
}
v___jp_2137_:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; uint8_t v___x_2146_; 
lean_inc_ref(v___y_2139_);
v___x_2140_ = l_Lean_stringToMessageData(v___y_2139_);
v___x_2141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2141_, 0, v___y_2138_);
lean_ctor_set(v___x_2141_, 1, v___x_2140_);
v___x_2142_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__6);
v___x_2143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2141_);
lean_ctor_set(v___x_2143_, 1, v___x_2142_);
v___x_2144_ = l_Lean_MessageData_ofName(v_mod_2072_);
v___x_2145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2143_);
lean_ctor_set(v___x_2145_, 1, v___x_2144_);
v___x_2146_ = l_Lean_Name_isAnonymous(v_hint_2074_);
if (v___x_2146_ == 0)
{
lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2147_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__8);
v___x_2148_ = l_Lean_MessageData_ofName(v_hint_2074_);
v___x_2149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2147_);
lean_ctor_set(v___x_2149_, 1, v___x_2148_);
v___y_2133_ = v___x_2145_;
v___y_2134_ = v___x_2149_;
goto v___jp_2132_;
}
else
{
lean_object* v___x_2150_; 
lean_dec(v_hint_2074_);
v___x_2150_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__9);
v___y_2133_ = v___x_2145_;
v___y_2134_ = v___x_2150_;
goto v___jp_2132_;
}
}
}
v___jp_2112_:
{
lean_object* v___x_2114_; lean_object* v_toEnvExtension_2115_; lean_object* v_env_2116_; lean_object* v_nextMacroScope_2117_; lean_object* v_ngen_2118_; lean_object* v_auxDeclNGen_2119_; lean_object* v_traceState_2120_; lean_object* v_recordedDeps_2121_; lean_object* v_messages_2122_; lean_object* v_infoState_2123_; lean_object* v_snapshotTasks_2124_; lean_object* v_asyncMode_2125_; uint8_t v_logWrites_2126_; lean_object* v___x_2127_; 
v___x_2114_ = lean_st_ref_take(v___y_2113_);
v_toEnvExtension_2115_ = lean_ctor_get(v___x_2101_, 0);
v_env_2116_ = lean_ctor_get(v___x_2114_, 0);
lean_inc_ref(v_env_2116_);
v_nextMacroScope_2117_ = lean_ctor_get(v___x_2114_, 1);
lean_inc(v_nextMacroScope_2117_);
v_ngen_2118_ = lean_ctor_get(v___x_2114_, 2);
lean_inc_ref(v_ngen_2118_);
v_auxDeclNGen_2119_ = lean_ctor_get(v___x_2114_, 3);
lean_inc_ref(v_auxDeclNGen_2119_);
v_traceState_2120_ = lean_ctor_get(v___x_2114_, 4);
lean_inc_ref(v_traceState_2120_);
v_recordedDeps_2121_ = lean_ctor_get(v___x_2114_, 6);
lean_inc_ref(v_recordedDeps_2121_);
v_messages_2122_ = lean_ctor_get(v___x_2114_, 7);
lean_inc_ref(v_messages_2122_);
v_infoState_2123_ = lean_ctor_get(v___x_2114_, 8);
lean_inc_ref(v_infoState_2123_);
v_snapshotTasks_2124_ = lean_ctor_get(v___x_2114_, 9);
lean_inc_ref(v_snapshotTasks_2124_);
lean_dec(v___x_2114_);
v_asyncMode_2125_ = lean_ctor_get(v_toEnvExtension_2115_, 2);
v_logWrites_2126_ = lean_ctor_get_uint8(v_toEnvExtension_2115_, sizeof(void*)*6);
v___x_2127_ = lean_box(0);
if (v_logWrites_2126_ == 0)
{
lean_object* v___x_2128_; 
lean_inc_ref(v_toEnvExtension_2115_);
v___x_2128_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2115_, v_env_2116_, v___f_2110_, v_asyncMode_2125_, v___x_2103_, v___x_2111_);
v___y_2079_ = v_snapshotTasks_2124_;
v___y_2080_ = v_infoState_2123_;
v___y_2081_ = v___x_2127_;
v___y_2082_ = v___y_2113_;
v___y_2083_ = v_ngen_2118_;
v___y_2084_ = v_nextMacroScope_2117_;
v___y_2085_ = v_traceState_2120_;
v___y_2086_ = v_messages_2122_;
v___y_2087_ = v_recordedDeps_2121_;
v___y_2088_ = v_auxDeclNGen_2119_;
v___y_2089_ = v___x_2128_;
goto v___jp_2078_;
}
else
{
lean_object* v___x_2129_; lean_object* v___x_2130_; 
lean_inc_ref_n(v_toEnvExtension_2115_, 2);
v___x_2129_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2115_, v_env_2116_);
lean_dec_ref(v_env_2116_);
v___x_2130_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2115_, v___x_2129_, v___f_2110_, v_asyncMode_2125_, v___x_2103_, v___x_2111_);
v___y_2079_ = v_snapshotTasks_2124_;
v___y_2080_ = v_infoState_2123_;
v___y_2081_ = v___x_2127_;
v___y_2082_ = v___y_2113_;
v___y_2083_ = v_ngen_2118_;
v___y_2084_ = v_nextMacroScope_2117_;
v___y_2085_ = v_traceState_2120_;
v___y_2086_ = v_messages_2122_;
v___y_2087_ = v_recordedDeps_2121_;
v___y_2088_ = v_auxDeclNGen_2119_;
v___y_2089_ = v___x_2130_;
goto v___jp_2078_;
}
}
}
else
{
lean_object* v___x_2164_; lean_object* v___x_2165_; 
lean_dec_ref_known(v_entry_2098_, 1);
lean_dec(v_hint_2074_);
lean_dec(v_mod_2072_);
v___x_2164_ = lean_box(0);
v___x_2165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2164_);
return v___x_2165_;
}
v___jp_2078_:
{
lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2090_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__1);
v___x_2091_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2091_, 0, v___y_2089_);
lean_ctor_set(v___x_2091_, 1, v___y_2084_);
lean_ctor_set(v___x_2091_, 2, v___y_2083_);
lean_ctor_set(v___x_2091_, 3, v___y_2088_);
lean_ctor_set(v___x_2091_, 4, v___y_2085_);
lean_ctor_set(v___x_2091_, 5, v___x_2090_);
lean_ctor_set(v___x_2091_, 6, v___y_2087_);
lean_ctor_set(v___x_2091_, 7, v___y_2086_);
lean_ctor_set(v___x_2091_, 8, v___y_2080_);
lean_ctor_set(v___x_2091_, 9, v___y_2079_);
v___x_2092_ = lean_st_ref_put(v___y_2082_, v___x_2091_);
v___x_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2093_, 0, v___y_2081_);
return v___x_2093_;
}
}
}
LEAN_EXPORT void l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_mod_2072_ = stack[0].m_obj;
uint8_t v_isMeta_2073_ = stack[1].m_num;
lean_object* v_hint_2074_ = stack[2].m_obj;
lean_object* v___y_2075_ = stack[3].m_obj;
lean_object* v___y_2076_ = stack[4].m_obj;
lean_object* v_res_2166_;
v_res_2166_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4(v_mod_2072_, v_isMeta_2073_, v_hint_2074_, v___y_2075_, v___y_2076_);
stack->m_obj
 = v_res_2166_;
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___boxed(lean_object* v_mod_2167_, lean_object* v_isMeta_2168_, lean_object* v_hint_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_){
_start:
{
uint8_t v_isMeta_boxed_2173_; lean_object* v_res_2174_; 
v_isMeta_boxed_2173_ = lean_unbox(v_isMeta_2168_);
v_res_2174_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4(v_mod_2167_, v_isMeta_boxed_2173_, v_hint_2169_, v___y_2170_, v___y_2171_);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
return v_res_2174_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg(lean_object* v_a_2175_, lean_object* v_x_2176_){
_start:
{
if (lean_obj_tag(v_x_2176_) == 0)
{
lean_object* v___x_2177_; 
v___x_2177_ = lean_box(0);
return v___x_2177_;
}
else
{
lean_object* v_key_2178_; lean_object* v_value_2179_; lean_object* v_tail_2180_; uint8_t v___x_2181_; 
v_key_2178_ = lean_ctor_get(v_x_2176_, 0);
v_value_2179_ = lean_ctor_get(v_x_2176_, 1);
v_tail_2180_ = lean_ctor_get(v_x_2176_, 2);
v___x_2181_ = lean_name_eq(v_key_2178_, v_a_2175_);
if (v___x_2181_ == 0)
{
v_x_2176_ = v_tail_2180_;
goto _start;
}
else
{
lean_object* v___x_2183_; 
lean_inc(v_value_2179_);
v___x_2183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2183_, 0, v_value_2179_);
return v___x_2183_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg___boxed(lean_object* v_a_2184_, lean_object* v_x_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg(v_a_2184_, v_x_2185_);
lean_dec(v_x_2185_);
lean_dec(v_a_2184_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6___redArg(lean_object* v_m_2187_, lean_object* v_a_2188_){
_start:
{
lean_object* v_buckets_2189_; lean_object* v___x_2190_; uint64_t v___y_2192_; 
v_buckets_2189_ = lean_ctor_get(v_m_2187_, 1);
v___x_2190_ = lean_array_get_size(v_buckets_2189_);
if (lean_obj_tag(v_a_2188_) == 0)
{
uint64_t v___x_2206_; 
v___x_2206_ = 1723ULL;
v___y_2192_ = v___x_2206_;
goto v___jp_2191_;
}
else
{
uint64_t v_hash_2207_; 
v_hash_2207_ = lean_ctor_get_uint64(v_a_2188_, sizeof(void*)*2);
v___y_2192_ = v_hash_2207_;
goto v___jp_2191_;
}
v___jp_2191_:
{
uint64_t v___x_2193_; uint64_t v___x_2194_; uint64_t v_fold_2195_; uint64_t v___x_2196_; uint64_t v___x_2197_; uint64_t v___x_2198_; size_t v___x_2199_; size_t v___x_2200_; size_t v___x_2201_; size_t v___x_2202_; size_t v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2193_ = 32ULL;
v___x_2194_ = lean_uint64_shift_right(v___y_2192_, v___x_2193_);
v_fold_2195_ = lean_uint64_xor(v___y_2192_, v___x_2194_);
v___x_2196_ = 16ULL;
v___x_2197_ = lean_uint64_shift_right(v_fold_2195_, v___x_2196_);
v___x_2198_ = lean_uint64_xor(v_fold_2195_, v___x_2197_);
v___x_2199_ = lean_uint64_to_usize(v___x_2198_);
v___x_2200_ = lean_usize_of_nat(v___x_2190_);
v___x_2201_ = ((size_t)1ULL);
v___x_2202_ = lean_usize_sub(v___x_2200_, v___x_2201_);
v___x_2203_ = lean_usize_land(v___x_2199_, v___x_2202_);
v___x_2204_ = lean_array_uget_borrowed(v_buckets_2189_, v___x_2203_);
v___x_2205_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg(v_a_2188_, v___x_2204_);
return v___x_2205_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6___redArg___boxed(lean_object* v_m_2208_, lean_object* v_a_2209_){
_start:
{
lean_object* v_res_2210_; 
v_res_2210_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6___redArg(v_m_2208_, v_a_2209_);
lean_dec(v_a_2209_);
lean_dec_ref(v_m_2208_);
return v_res_2210_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__5(lean_object* v___x_2211_, lean_object* v_declName_2212_, lean_object* v_as_2213_, size_t v_sz_2214_, size_t v_i_2215_, lean_object* v_b_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_){
_start:
{
uint8_t v___x_2220_; 
v___x_2220_ = lean_usize_dec_lt(v_i_2215_, v_sz_2214_);
if (v___x_2220_ == 0)
{
lean_object* v___x_2221_; 
lean_dec(v_declName_2212_);
v___x_2221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2221_, 0, v_b_2216_);
return v___x_2221_;
}
else
{
lean_object* v___x_2222_; lean_object* v_modules_2223_; lean_object* v___x_2224_; lean_object* v_a_2225_; lean_object* v___x_2226_; lean_object* v_toImport_2227_; lean_object* v_module_2228_; lean_object* v___x_2229_; uint8_t v___x_2230_; lean_object* v___x_2231_; 
v___x_2222_ = l_Lean_Environment_header(v___x_2211_);
v_modules_2223_ = lean_ctor_get(v___x_2222_, 3);
lean_inc_ref(v_modules_2223_);
lean_dec_ref(v___x_2222_);
v___x_2224_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2225_ = lean_array_uget_borrowed(v_as_2213_, v_i_2215_);
v___x_2226_ = lean_array_get(v___x_2224_, v_modules_2223_, v_a_2225_);
lean_dec_ref(v_modules_2223_);
v_toImport_2227_ = lean_ctor_get(v___x_2226_, 0);
lean_inc_ref(v_toImport_2227_);
lean_dec(v___x_2226_);
v_module_2228_ = lean_ctor_get(v_toImport_2227_, 0);
lean_inc(v_module_2228_);
lean_dec_ref(v_toImport_2227_);
v___x_2229_ = lean_box(0);
v___x_2230_ = 0;
lean_inc(v_declName_2212_);
v___x_2231_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4(v_module_2228_, v___x_2230_, v_declName_2212_, v___y_2217_, v___y_2218_);
if (lean_obj_tag(v___x_2231_) == 0)
{
size_t v___x_2232_; size_t v___x_2233_; 
lean_dec_ref_known(v___x_2231_, 1);
v___x_2232_ = ((size_t)1ULL);
v___x_2233_ = lean_usize_add(v_i_2215_, v___x_2232_);
v_i_2215_ = v___x_2233_;
v_b_2216_ = v___x_2229_;
goto _start;
}
else
{
lean_dec(v_declName_2212_);
return v___x_2231_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2211_ = stack[0].m_obj;
lean_object* v_declName_2212_ = stack[1].m_obj;
lean_object* v_as_2213_ = stack[2].m_obj;
size_t v_sz_2214_ = stack[3].m_num;
size_t v_i_2215_ = stack[4].m_num;
lean_object* v_b_2216_ = stack[5].m_obj;
lean_object* v___y_2217_ = stack[6].m_obj;
lean_object* v___y_2218_ = stack[7].m_obj;
lean_object* v_res_2235_;
v_res_2235_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__5(v___x_2211_, v_declName_2212_, v_as_2213_, v_sz_2214_, v_i_2215_, v_b_2216_, v___y_2217_, v___y_2218_);
stack->m_obj
 = v_res_2235_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__5___boxed(lean_object* v___x_2236_, lean_object* v_declName_2237_, lean_object* v_as_2238_, lean_object* v_sz_2239_, lean_object* v_i_2240_, lean_object* v_b_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_){
_start:
{
size_t v_sz_boxed_2245_; size_t v_i_boxed_2246_; lean_object* v_res_2247_; 
v_sz_boxed_2245_ = lean_unbox_usize(v_sz_2239_);
lean_dec(v_sz_2239_);
v_i_boxed_2246_ = lean_unbox_usize(v_i_2240_);
lean_dec(v_i_2240_);
v_res_2247_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__5(v___x_2236_, v_declName_2237_, v_as_2238_, v_sz_boxed_2245_, v_i_boxed_2246_, v_b_2241_, v___y_2242_, v___y_2243_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec_ref(v_as_2238_);
lean_dec_ref(v___x_2236_);
return v_res_2247_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2___closed__0(void){
_start:
{
lean_object* v___x_2248_; 
v___x_2248_ = l_Std_HashMap_instInhabited___redArg();
return v___x_2248_;
}
}
lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2(lean_object* v_declName_2251_, uint8_t v_isMeta_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_){
_start:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v_env_2261_; lean_object* v___y_2263_; lean_object* v___x_2276_; 
v___x_2256_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2___closed__0);
v___x_2257_ = lean_st_ref_get(v___y_2254_);
v_env_2261_ = lean_ctor_get(v___x_2257_, 0);
lean_inc_ref(v_env_2261_);
lean_dec(v___x_2257_);
v___x_2276_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2261_, v_declName_2251_);
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_dec_ref(v_env_2261_);
lean_dec(v_declName_2251_);
goto v___jp_2258_;
}
else
{
lean_object* v_val_2277_; lean_object* v___x_2278_; lean_object* v_modules_2279_; lean_object* v___x_2280_; uint8_t v___x_2281_; 
v_val_2277_ = lean_ctor_get(v___x_2276_, 0);
lean_inc(v_val_2277_);
lean_dec_ref_known(v___x_2276_, 1);
v___x_2278_ = l_Lean_Environment_header(v_env_2261_);
v_modules_2279_ = lean_ctor_get(v___x_2278_, 3);
lean_inc_ref(v_modules_2279_);
lean_dec_ref(v___x_2278_);
v___x_2280_ = lean_array_get_size(v_modules_2279_);
v___x_2281_ = lean_nat_dec_lt(v_val_2277_, v___x_2280_);
if (v___x_2281_ == 0)
{
lean_dec_ref(v_modules_2279_);
lean_dec(v_val_2277_);
lean_dec_ref(v_env_2261_);
lean_dec(v_declName_2251_);
goto v___jp_2258_;
}
else
{
lean_object* v___x_2282_; lean_object* v___x_2283_; uint8_t v___y_2285_; 
v___x_2282_ = lean_array_fget(v_modules_2279_, v_val_2277_);
lean_dec(v_val_2277_);
lean_dec_ref(v_modules_2279_);
v___x_2283_ = lean_st_ref_get(v___y_2254_);
if (v_isMeta_2252_ == 0)
{
lean_dec(v___x_2283_);
v___y_2285_ = v_isMeta_2252_;
goto v___jp_2284_;
}
else
{
lean_object* v_env_2296_; uint8_t v___x_2297_; 
v_env_2296_ = lean_ctor_get(v___x_2283_, 0);
lean_inc_ref(v_env_2296_);
lean_dec(v___x_2283_);
lean_inc(v_declName_2251_);
v___x_2297_ = l_Lean_isMarkedMeta(v_env_2296_, v_declName_2251_);
if (v___x_2297_ == 0)
{
v___y_2285_ = v_isMeta_2252_;
goto v___jp_2284_;
}
else
{
uint8_t v___x_2298_; 
v___x_2298_ = 0;
v___y_2285_ = v___x_2298_;
goto v___jp_2284_;
}
}
v___jp_2284_:
{
lean_object* v_toImport_2286_; lean_object* v_module_2287_; lean_object* v___x_2288_; 
v_toImport_2286_ = lean_ctor_get(v___x_2282_, 0);
lean_inc_ref(v_toImport_2286_);
lean_dec(v___x_2282_);
v_module_2287_ = lean_ctor_get(v_toImport_2286_, 0);
lean_inc(v_module_2287_);
lean_dec_ref(v_toImport_2286_);
lean_inc(v_declName_2251_);
v___x_2288_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4(v_module_2287_, v___y_2285_, v_declName_2251_, v___y_2253_, v___y_2254_);
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
lean_dec_ref_known(v___x_2288_, 1);
v___x_2289_ = l_Lean_indirectModUseExt;
v___x_2290_ = lean_box(1);
v___x_2291_ = lean_box(0);
lean_inc_ref(v_env_2261_);
v___x_2292_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2256_, v___x_2289_, v_env_2261_, v___x_2290_, v___x_2291_);
v___x_2293_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6___redArg(v___x_2292_, v_declName_2251_);
lean_dec(v___x_2292_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v___x_2294_; 
v___x_2294_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2___closed__1));
v___y_2263_ = v___x_2294_;
goto v___jp_2262_;
}
else
{
lean_object* v_val_2295_; 
v_val_2295_ = lean_ctor_get(v___x_2293_, 0);
lean_inc(v_val_2295_);
lean_dec_ref_known(v___x_2293_, 1);
v___y_2263_ = v_val_2295_;
goto v___jp_2262_;
}
}
else
{
lean_dec_ref(v_env_2261_);
lean_dec(v_declName_2251_);
return v___x_2288_;
}
}
}
}
v___jp_2258_:
{
lean_object* v___x_2259_; lean_object* v___x_2260_; 
v___x_2259_ = lean_box(0);
v___x_2260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2259_);
return v___x_2260_;
}
v___jp_2262_:
{
lean_object* v___x_2264_; size_t v_sz_2265_; size_t v___x_2266_; lean_object* v___x_2267_; 
v___x_2264_ = lean_box(0);
v_sz_2265_ = lean_array_size(v___y_2263_);
v___x_2266_ = ((size_t)0ULL);
v___x_2267_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__5(v_env_2261_, v_declName_2251_, v___y_2263_, v_sz_2265_, v___x_2266_, v___x_2264_, v___y_2253_, v___y_2254_);
lean_dec_ref(v___y_2263_);
lean_dec_ref(v_env_2261_);
if (lean_obj_tag(v___x_2267_) == 0)
{
lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2274_; 
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2267_);
if (v_isSharedCheck_2274_ == 0)
{
lean_object* v_unused_2275_; 
v_unused_2275_ = lean_ctor_get(v___x_2267_, 0);
lean_dec(v_unused_2275_);
v___x_2269_ = v___x_2267_;
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
else
{
lean_dec(v___x_2267_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v___x_2272_; 
if (v_isShared_2270_ == 0)
{
lean_ctor_set(v___x_2269_, 0, v___x_2264_);
v___x_2272_ = v___x_2269_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v___x_2264_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
else
{
return v___x_2267_;
}
}
}
}
LEAN_EXPORT void l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2251_ = stack[0].m_obj;
uint8_t v_isMeta_2252_ = stack[1].m_num;
lean_object* v___y_2253_ = stack[2].m_obj;
lean_object* v___y_2254_ = stack[3].m_obj;
lean_object* v_res_2299_;
v_res_2299_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2(v_declName_2251_, v_isMeta_2252_, v___y_2253_, v___y_2254_);
stack->m_obj
 = v_res_2299_;
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2___boxed(lean_object* v_declName_2300_, lean_object* v_isMeta_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_){
_start:
{
uint8_t v_isMeta_boxed_2305_; lean_object* v_res_2306_; 
v_isMeta_boxed_2305_ = lean_unbox(v_isMeta_2301_);
v_res_2306_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2(v_declName_2300_, v_isMeta_boxed_2305_, v___y_2302_, v___y_2303_);
lean_dec(v___y_2303_);
lean_dec_ref(v___y_2302_);
return v_res_2306_;
}
}
lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5(lean_object* v_ref_2307_, lean_object* v_msgData_2308_, uint8_t v_severity_2309_, uint8_t v_isSilent_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_){
_start:
{
uint8_t v___y_2315_; lean_object* v___y_2316_; uint8_t v___y_2317_; lean_object* v___y_2318_; lean_object* v___y_2319_; lean_object* v___y_2320_; lean_object* v___y_2321_; lean_object* v_toCold_2322_; lean_object* v___y_2323_; lean_object* v___y_2352_; lean_object* v___y_2353_; uint8_t v___y_2354_; lean_object* v___y_2355_; uint8_t v___y_2356_; uint8_t v___y_2357_; lean_object* v___y_2358_; lean_object* v___y_2359_; lean_object* v___y_2379_; uint8_t v___y_2380_; lean_object* v___y_2381_; uint8_t v___y_2382_; uint8_t v___y_2383_; lean_object* v___y_2384_; lean_object* v___y_2385_; uint8_t v___y_2389_; uint8_t v___y_2390_; uint8_t v___y_2391_; uint8_t v___x_2402_; uint8_t v___y_2404_; uint8_t v___y_2405_; uint8_t v___y_2406_; uint8_t v___y_2408_; uint8_t v___x_2416_; 
v___x_2402_ = 2;
v___x_2416_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2309_, v___x_2402_);
if (v___x_2416_ == 0)
{
v___y_2408_ = v___x_2416_;
goto v___jp_2407_;
}
else
{
uint8_t v___x_2417_; 
lean_inc_ref(v_msgData_2308_);
v___x_2417_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2308_);
v___y_2408_ = v___x_2417_;
goto v___jp_2407_;
}
v___jp_2314_:
{
lean_object* v_currNamespace_2324_; lean_object* v_openDecls_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v_env_2330_; lean_object* v_nextMacroScope_2331_; lean_object* v_ngen_2332_; lean_object* v_auxDeclNGen_2333_; lean_object* v_traceState_2334_; lean_object* v_cache_2335_; lean_object* v_recordedDeps_2336_; lean_object* v_messages_2337_; lean_object* v_infoState_2338_; lean_object* v_snapshotTasks_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2350_; 
v_currNamespace_2324_ = lean_ctor_get(v_toCold_2322_, 4);
v_openDecls_2325_ = lean_ctor_get(v_toCold_2322_, 5);
lean_inc(v_openDecls_2325_);
lean_inc(v_currNamespace_2324_);
v___x_2326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2326_, 0, v_currNamespace_2324_);
lean_ctor_set(v___x_2326_, 1, v_openDecls_2325_);
v___x_2327_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2326_);
lean_ctor_set(v___x_2327_, 1, v___y_2320_);
lean_inc_ref(v___y_2318_);
lean_inc_ref(v___y_2321_);
v___x_2328_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2328_, 0, v___y_2321_);
lean_ctor_set(v___x_2328_, 1, v___y_2316_);
lean_ctor_set(v___x_2328_, 2, v___y_2319_);
lean_ctor_set(v___x_2328_, 3, v___y_2318_);
lean_ctor_set(v___x_2328_, 4, v___x_2327_);
lean_ctor_set_uint8(v___x_2328_, sizeof(void*)*5, v___y_2317_);
lean_ctor_set_uint8(v___x_2328_, sizeof(void*)*5 + 1, v___y_2315_);
lean_ctor_set_uint8(v___x_2328_, sizeof(void*)*5 + 2, v_isSilent_2310_);
v___x_2329_ = lean_st_ref_take(v___y_2323_);
v_env_2330_ = lean_ctor_get(v___x_2329_, 0);
v_nextMacroScope_2331_ = lean_ctor_get(v___x_2329_, 1);
v_ngen_2332_ = lean_ctor_get(v___x_2329_, 2);
v_auxDeclNGen_2333_ = lean_ctor_get(v___x_2329_, 3);
v_traceState_2334_ = lean_ctor_get(v___x_2329_, 4);
v_cache_2335_ = lean_ctor_get(v___x_2329_, 5);
v_recordedDeps_2336_ = lean_ctor_get(v___x_2329_, 6);
v_messages_2337_ = lean_ctor_get(v___x_2329_, 7);
v_infoState_2338_ = lean_ctor_get(v___x_2329_, 8);
v_snapshotTasks_2339_ = lean_ctor_get(v___x_2329_, 9);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2341_ = v___x_2329_;
v_isShared_2342_ = v_isSharedCheck_2350_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_snapshotTasks_2339_);
lean_inc(v_infoState_2338_);
lean_inc(v_messages_2337_);
lean_inc(v_recordedDeps_2336_);
lean_inc(v_cache_2335_);
lean_inc(v_traceState_2334_);
lean_inc(v_auxDeclNGen_2333_);
lean_inc(v_ngen_2332_);
lean_inc(v_nextMacroScope_2331_);
lean_inc(v_env_2330_);
lean_dec(v___x_2329_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2350_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2346_; 
v___x_2343_ = lean_box(0);
v___x_2344_ = l_Lean_MessageLog_add(v___x_2328_, v_messages_2337_);
if (v_isShared_2342_ == 0)
{
lean_ctor_set(v___x_2341_, 7, v___x_2344_);
v___x_2346_ = v___x_2341_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_env_2330_);
lean_ctor_set(v_reuseFailAlloc_2349_, 1, v_nextMacroScope_2331_);
lean_ctor_set(v_reuseFailAlloc_2349_, 2, v_ngen_2332_);
lean_ctor_set(v_reuseFailAlloc_2349_, 3, v_auxDeclNGen_2333_);
lean_ctor_set(v_reuseFailAlloc_2349_, 4, v_traceState_2334_);
lean_ctor_set(v_reuseFailAlloc_2349_, 5, v_cache_2335_);
lean_ctor_set(v_reuseFailAlloc_2349_, 6, v_recordedDeps_2336_);
lean_ctor_set(v_reuseFailAlloc_2349_, 7, v___x_2344_);
lean_ctor_set(v_reuseFailAlloc_2349_, 8, v_infoState_2338_);
lean_ctor_set(v_reuseFailAlloc_2349_, 9, v_snapshotTasks_2339_);
v___x_2346_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___x_2347_ = lean_st_ref_put(v___y_2323_, v___x_2346_);
v___x_2348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2343_);
return v___x_2348_;
}
}
}
v___jp_2351_:
{
lean_object* v_fileName_2360_; lean_object* v_fileMap_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2377_; 
v_fileName_2360_ = lean_ctor_get(v___y_2355_, 0);
v_fileMap_2361_ = lean_ctor_get(v___y_2355_, 1);
v___x_2362_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2308_);
v___x_2363_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0(v___x_2362_, v___y_2311_, v___y_2312_);
v_a_2364_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2377_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2377_ == 0)
{
v___x_2366_ = v___x_2363_;
v_isShared_2367_ = v_isSharedCheck_2377_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2363_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2377_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; 
lean_inc_ref_n(v_fileMap_2361_, 2);
v___x_2368_ = l_Lean_FileMap_toPosition(v_fileMap_2361_, v___y_2358_);
lean_dec(v___y_2358_);
v___x_2369_ = l_Lean_FileMap_toPosition(v_fileMap_2361_, v___y_2359_);
lean_dec(v___y_2359_);
v___x_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2369_);
v___x_2371_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48___closed__0));
if (v___y_2357_ == 0)
{
lean_del_object(v___x_2366_);
lean_dec_ref(v___y_2353_);
v___y_2315_ = v___y_2354_;
v___y_2316_ = v___x_2368_;
v___y_2317_ = v___y_2356_;
v___y_2318_ = v___x_2371_;
v___y_2319_ = v___x_2370_;
v___y_2320_ = v_a_2364_;
v___y_2321_ = v_fileName_2360_;
v_toCold_2322_ = v___y_2352_;
v___y_2323_ = v___y_2312_;
goto v___jp_2314_;
}
else
{
uint8_t v___x_2372_; 
lean_inc(v_a_2364_);
v___x_2372_ = l_Lean_MessageData_hasTag(v___y_2353_, v_a_2364_);
if (v___x_2372_ == 0)
{
lean_object* v___x_2373_; lean_object* v___x_2375_; 
lean_dec_ref_known(v___x_2370_, 1);
lean_dec_ref(v___x_2368_);
lean_dec(v_a_2364_);
v___x_2373_ = lean_box(0);
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 0, v___x_2373_);
v___x_2375_ = v___x_2366_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v___x_2373_);
v___x_2375_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
return v___x_2375_;
}
}
else
{
lean_del_object(v___x_2366_);
v___y_2315_ = v___y_2354_;
v___y_2316_ = v___x_2368_;
v___y_2317_ = v___y_2356_;
v___y_2318_ = v___x_2371_;
v___y_2319_ = v___x_2370_;
v___y_2320_ = v_a_2364_;
v___y_2321_ = v_fileName_2360_;
v_toCold_2322_ = v___y_2352_;
v___y_2323_ = v___y_2312_;
goto v___jp_2314_;
}
}
}
}
v___jp_2378_:
{
lean_object* v___x_2386_; 
v___x_2386_ = l_Lean_Syntax_getTailPos_x3f(v___y_2384_, v___y_2383_);
lean_dec(v___y_2384_);
if (lean_obj_tag(v___x_2386_) == 0)
{
lean_inc(v___y_2385_);
v___y_2352_ = v___y_2379_;
v___y_2353_ = v___y_2381_;
v___y_2354_ = v___y_2382_;
v___y_2355_ = v___y_2379_;
v___y_2356_ = v___y_2383_;
v___y_2357_ = v___y_2380_;
v___y_2358_ = v___y_2385_;
v___y_2359_ = v___y_2385_;
goto v___jp_2351_;
}
else
{
lean_object* v_val_2387_; 
v_val_2387_ = lean_ctor_get(v___x_2386_, 0);
lean_inc(v_val_2387_);
lean_dec_ref_known(v___x_2386_, 1);
v___y_2352_ = v___y_2379_;
v___y_2353_ = v___y_2381_;
v___y_2354_ = v___y_2382_;
v___y_2355_ = v___y_2379_;
v___y_2356_ = v___y_2383_;
v___y_2357_ = v___y_2380_;
v___y_2358_ = v___y_2385_;
v___y_2359_ = v_val_2387_;
goto v___jp_2351_;
}
}
v___jp_2388_:
{
lean_object* v_toCold_2392_; lean_object* v_ref_2393_; uint8_t v_suppressElabErrors_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___f_2397_; lean_object* v_ref_2398_; lean_object* v___x_2399_; 
v_toCold_2392_ = lean_ctor_get(v___y_2311_, 0);
v_ref_2393_ = lean_ctor_get(v___y_2311_, 2);
v_suppressElabErrors_2394_ = lean_ctor_get_uint8(v___y_2311_, sizeof(void*)*3 + 2);
v___x_2395_ = lean_box(v_suppressElabErrors_2394_);
v___x_2396_ = lean_box(v___y_2389_);
v___f_2397_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2397_, 0, v___x_2395_);
lean_closure_set(v___f_2397_, 1, v___x_2396_);
v_ref_2398_ = l_Lean_replaceRef(v_ref_2307_, v_ref_2393_);
v___x_2399_ = l_Lean_Syntax_getPos_x3f(v_ref_2398_, v___y_2390_);
if (lean_obj_tag(v___x_2399_) == 0)
{
lean_object* v___x_2400_; 
v___x_2400_ = lean_unsigned_to_nat(0u);
v___y_2379_ = v_toCold_2392_;
v___y_2380_ = v_suppressElabErrors_2394_;
v___y_2381_ = v___f_2397_;
v___y_2382_ = v___y_2391_;
v___y_2383_ = v___y_2390_;
v___y_2384_ = v_ref_2398_;
v___y_2385_ = v___x_2400_;
goto v___jp_2378_;
}
else
{
lean_object* v_val_2401_; 
v_val_2401_ = lean_ctor_get(v___x_2399_, 0);
lean_inc(v_val_2401_);
lean_dec_ref_known(v___x_2399_, 1);
v___y_2379_ = v_toCold_2392_;
v___y_2380_ = v_suppressElabErrors_2394_;
v___y_2381_ = v___f_2397_;
v___y_2382_ = v___y_2391_;
v___y_2383_ = v___y_2390_;
v___y_2384_ = v_ref_2398_;
v___y_2385_ = v_val_2401_;
goto v___jp_2378_;
}
}
v___jp_2403_:
{
if (v___y_2406_ == 0)
{
v___y_2389_ = v___y_2404_;
v___y_2390_ = v___y_2405_;
v___y_2391_ = v_severity_2309_;
goto v___jp_2388_;
}
else
{
v___y_2389_ = v___y_2404_;
v___y_2390_ = v___y_2405_;
v___y_2391_ = v___x_2402_;
goto v___jp_2388_;
}
}
v___jp_2407_:
{
if (v___y_2408_ == 0)
{
uint8_t v___x_2409_; uint8_t v___x_2410_; 
v___x_2409_ = 1;
v___x_2410_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2309_, v___x_2409_);
if (v___x_2410_ == 0)
{
v___y_2404_ = v___y_2408_;
v___y_2405_ = v___y_2408_;
v___y_2406_ = v___x_2410_;
goto v___jp_2403_;
}
else
{
lean_object* v___x_2411_; lean_object* v___x_2412_; uint8_t v___x_2413_; 
v___x_2411_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2311_);
v___x_2412_ = l_Lean_warningAsError;
v___x_2413_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4(v___x_2411_, v___x_2412_);
lean_dec_ref(v___x_2411_);
v___y_2404_ = v___y_2408_;
v___y_2405_ = v___y_2408_;
v___y_2406_ = v___x_2413_;
goto v___jp_2403_;
}
}
else
{
lean_object* v___x_2414_; lean_object* v___x_2415_; 
lean_dec_ref(v_msgData_2308_);
v___x_2414_ = lean_box(0);
v___x_2415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2414_);
return v___x_2415_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2307_ = stack[0].m_obj;
lean_object* v_msgData_2308_ = stack[1].m_obj;
uint8_t v_severity_2309_ = stack[2].m_num;
uint8_t v_isSilent_2310_ = stack[3].m_num;
lean_object* v___y_2311_ = stack[4].m_obj;
lean_object* v___y_2312_ = stack[5].m_obj;
lean_object* v_res_2418_;
v_res_2418_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5(v_ref_2307_, v_msgData_2308_, v_severity_2309_, v_isSilent_2310_, v___y_2311_, v___y_2312_);
stack->m_obj
 = v_res_2418_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___boxed(lean_object* v_ref_2419_, lean_object* v_msgData_2420_, lean_object* v_severity_2421_, lean_object* v_isSilent_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
uint8_t v_severity_boxed_2426_; uint8_t v_isSilent_boxed_2427_; lean_object* v_res_2428_; 
v_severity_boxed_2426_ = lean_unbox(v_severity_2421_);
v_isSilent_boxed_2427_ = lean_unbox(v_isSilent_2422_);
v_res_2428_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5(v_ref_2419_, v_msgData_2420_, v_severity_boxed_2426_, v_isSilent_boxed_2427_, v___y_2423_, v___y_2424_);
lean_dec(v___y_2424_);
lean_dec_ref(v___y_2423_);
lean_dec(v_ref_2419_);
return v_res_2428_;
}
}
lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_msgData_2429_, uint8_t v_severity_2430_, uint8_t v_isSilent_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_){
_start:
{
lean_object* v_ref_2435_; lean_object* v___x_2436_; 
v_ref_2435_ = lean_ctor_get(v___y_2432_, 2);
v___x_2436_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5(v_ref_2435_, v_msgData_2429_, v_severity_2430_, v_isSilent_2431_, v___y_2432_, v___y_2433_);
return v___x_2436_;
}
}
LEAN_EXPORT void l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_2429_ = stack[0].m_obj;
uint8_t v_severity_2430_ = stack[1].m_num;
uint8_t v_isSilent_2431_ = stack[2].m_num;
lean_object* v___y_2432_ = stack[3].m_obj;
lean_object* v___y_2433_ = stack[4].m_obj;
lean_object* v_res_2437_;
v_res_2437_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2(v_msgData_2429_, v_severity_2430_, v_isSilent_2431_, v___y_2432_, v___y_2433_);
stack->m_obj
 = v_res_2437_;
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_msgData_2438_, lean_object* v_severity_2439_, lean_object* v_isSilent_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_){
_start:
{
uint8_t v_severity_boxed_2444_; uint8_t v_isSilent_boxed_2445_; lean_object* v_res_2446_; 
v_severity_boxed_2444_ = lean_unbox(v_severity_2439_);
v_isSilent_boxed_2445_ = lean_unbox(v_isSilent_2440_);
v_res_2446_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2(v_msgData_2438_, v_severity_boxed_2444_, v_isSilent_boxed_2445_, v___y_2441_, v___y_2442_);
lean_dec(v___y_2442_);
lean_dec_ref(v___y_2441_);
return v_res_2446_;
}
}
lean_object* l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1(lean_object* v_msgData_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_){
_start:
{
uint8_t v___x_2451_; uint8_t v___x_2452_; lean_object* v___x_2453_; 
v___x_2451_ = 1;
v___x_2452_ = 0;
v___x_2453_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2(v_msgData_2447_, v___x_2451_, v___x_2452_, v___y_2448_, v___y_2449_);
return v___x_2453_;
}
}
LEAN_EXPORT void l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_2447_ = stack[0].m_obj;
lean_object* v___y_2448_ = stack[1].m_obj;
lean_object* v___y_2449_ = stack[2].m_obj;
lean_object* v_res_2454_;
v_res_2454_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1(v_msgData_2447_, v___y_2448_, v___y_2449_);
stack->m_obj
 = v_res_2454_;
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1___boxed(lean_object* v_msgData_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_){
_start:
{
lean_object* v_res_2459_; 
v_res_2459_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1(v_msgData_2455_, v___y_2456_, v___y_2457_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
return v_res_2459_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_){
_start:
{
lean_object* v_ref_2464_; lean_object* v___x_2465_; lean_object* v_a_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2474_; 
v_ref_2464_ = lean_ctor_get(v___y_2461_, 2);
v___x_2465_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0(v_msg_2460_, v___y_2461_, v___y_2462_);
v_a_2466_ = lean_ctor_get(v___x_2465_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2468_ = v___x_2465_;
v_isShared_2469_ = v_isSharedCheck_2474_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_a_2466_);
lean_dec(v___x_2465_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2474_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2470_; lean_object* v___x_2472_; 
lean_inc(v_ref_2464_);
v___x_2470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2470_, 0, v_ref_2464_);
lean_ctor_set(v___x_2470_, 1, v_a_2466_);
if (v_isShared_2469_ == 0)
{
lean_ctor_set_tag(v___x_2468_, 1);
lean_ctor_set(v___x_2468_, 0, v___x_2470_);
v___x_2472_ = v___x_2468_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v___x_2470_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2460_ = stack[0].m_obj;
lean_object* v___y_2461_ = stack[1].m_obj;
lean_object* v___y_2462_ = stack[2].m_obj;
lean_object* v_res_2475_;
v_res_2475_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0___redArg(v_msg_2460_, v___y_2461_, v___y_2462_);
stack->m_obj
 = v_res_2475_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0___redArg(v_msg_2476_, v___y_2477_, v___y_2478_);
lean_dec(v___y_2478_);
lean_dec_ref(v___y_2477_);
return v_res_2480_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__1_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2482_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__0_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2483_ = l_Lean_stringToMessageData(v___x_2482_);
return v___x_2483_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__4_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2487_; lean_object* v___x_2488_; 
v___x_2487_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__3_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2488_ = l_Lean_MessageData_ofFormat(v___x_2487_);
return v___x_2488_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2490_; lean_object* v___x_2491_; 
v___x_2490_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__5_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2491_ = l_Lean_stringToMessageData(v___x_2490_);
return v___x_2491_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2493_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2494_ = l_Lean_stringToMessageData(v___x_2493_);
return v___x_2494_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__10_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2496_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2497_ = l_Lean_stringToMessageData(v___x_2496_);
return v___x_2497_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__13_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2501_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__12_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2502_ = l_Lean_MessageData_ofFormat(v___x_2501_);
return v___x_2502_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__14_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2503_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__13_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__13_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__13_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2504_ = l_Lean_MessageData_hint_x27(v___x_2503_);
return v___x_2504_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2506_; lean_object* v___x_2507_; 
v___x_2506_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__15_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2507_ = l_Lean_stringToMessageData(v___x_2506_);
return v___x_2507_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__19_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2511_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__18_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2512_ = l_Lean_MessageData_ofFormat(v___x_2511_);
return v___x_2512_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__24_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2519_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__23_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2520_ = l_Lean_MessageData_ofFormat(v___x_2519_);
return v___x_2520_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__25_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2521_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__24_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__24_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__24_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2521_);
return v___x_2522_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__28_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2526_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__27_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2527_ = l_Lean_MessageData_ofFormat(v___x_2526_);
return v___x_2527_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2528_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_2529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2529_, 0, v___x_2528_);
return v___x_2529_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2530_ = lean_box(1);
v___x_2531_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_2532_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2533_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2533_, 0, v___x_2532_);
lean_ctor_set(v___x_2533_, 1, v___x_2531_);
lean_ctor_set(v___x_2533_, 2, v___x_2530_);
return v___x_2533_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2536_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_2537_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2538_ = lean_unsigned_to_nat(0u);
v___x_2539_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2539_, 0, v___x_2538_);
lean_ctor_set(v___x_2539_, 1, v___x_2538_);
lean_ctor_set(v___x_2539_, 2, v___x_2538_);
lean_ctor_set(v___x_2539_, 3, v___x_2538_);
lean_ctor_set(v___x_2539_, 4, v___x_2537_);
lean_ctor_set(v___x_2539_, 5, v___x_2537_);
lean_ctor_set(v___x_2539_, 6, v___x_2537_);
lean_ctor_set(v___x_2539_, 7, v___x_2537_);
lean_ctor_set(v___x_2539_, 8, v___x_2537_);
lean_ctor_set(v___x_2539_, 9, v___x_2537_);
lean_ctor_set(v___x_2539_, 10, v___x_2537_);
lean_ctor_set(v___x_2539_, 11, v___x_2536_);
return v___x_2539_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2540_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2541_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2540_);
lean_ctor_set(v___x_2541_, 1, v___x_2540_);
lean_ctor_set(v___x_2541_, 2, v___x_2540_);
lean_ctor_set(v___x_2541_, 3, v___x_2540_);
lean_ctor_set(v___x_2541_, 4, v___x_2540_);
lean_ctor_set(v___x_2541_, 5, v___x_2540_);
return v___x_2541_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2542_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2543_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2543_, 0, v___x_2542_);
lean_ctor_set(v___x_2543_, 1, v___x_2542_);
lean_ctor_set(v___x_2543_, 2, v___x_2542_);
lean_ctor_set(v___x_2543_, 3, v___x_2542_);
lean_ctor_set(v___x_2543_, 4, v___x_2542_);
return v___x_2543_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__36_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2545_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2546_ = l_Lean_stringToMessageData(v___x_2545_);
return v___x_2546_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__38_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2548_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__37_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2549_ = l_Lean_stringToMessageData(v___x_2548_);
return v___x_2549_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__40_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2551_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__39_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2552_ = l_Lean_stringToMessageData(v___x_2551_);
return v___x_2552_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2554_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2555_ = l_Lean_stringToMessageData(v___x_2554_);
return v___x_2555_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2557_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2558_ = l_Lean_stringToMessageData(v___x_2557_);
return v___x_2558_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2560_; lean_object* v___x_2561_; 
v___x_2560_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2561_ = l_Lean_stringToMessageData(v___x_2560_);
return v___x_2561_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__48_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___x_2563_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__47_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2564_ = l_Lean_stringToMessageData(v___x_2563_);
return v___x_2564_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__50_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2566_; lean_object* v___x_2567_; 
v___x_2566_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__49_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2567_ = l_Lean_stringToMessageData(v___x_2566_);
return v___x_2567_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__52_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; 
v___x_2569_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__51_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2570_ = l_Lean_stringToMessageData(v___x_2569_);
return v___x_2570_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__54_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; 
v___x_2572_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__53_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2573_ = l_Lean_stringToMessageData(v___x_2572_);
return v___x_2573_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__56_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2575_; lean_object* v___x_2576_; 
v___x_2575_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__55_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2576_ = l_Lean_stringToMessageData(v___x_2575_);
return v___x_2576_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__58_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; 
v___x_2578_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__57_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2579_ = l_Lean_stringToMessageData(v___x_2578_);
return v___x_2579_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__60_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; 
v___x_2581_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__59_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2582_ = l_Lean_stringToMessageData(v___x_2581_);
return v___x_2582_;
}
}
lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(lean_object* v___x_2583_, lean_object* v___x_2584_, lean_object* v___f_2585_, uint8_t v___x_2586_, lean_object* v___x_2587_, lean_object* v___x_2588_, lean_object* v_a_2589_, lean_object* v_declName_2590_, lean_object* v_stx_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_){
_start:
{
lean_object* v___y_2596_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v___x_2601_; uint8_t v___x_2602_; lean_object* v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2631_; lean_object* v___y_2632_; lean_object* v___y_2633_; lean_object* v___y_2634_; lean_object* v___y_2635_; lean_object* v___y_2636_; lean_object* v___y_2648_; lean_object* v___y_2649_; lean_object* v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; lean_object* v___y_2653_; lean_object* v___y_2665_; lean_object* v___y_2666_; lean_object* v___y_2667_; lean_object* v___y_2668_; lean_object* v___y_2669_; lean_object* v___y_2670_; lean_object* v___y_2682_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___y_2685_; lean_object* v___y_2686_; lean_object* v___y_2687_; lean_object* v_hint_2688_; lean_object* v___y_2689_; lean_object* v___y_2690_; lean_object* v___y_2713_; lean_object* v___y_2714_; lean_object* v___y_2715_; lean_object* v___y_2716_; lean_object* v___y_2717_; lean_object* v___y_2718_; lean_object* v___y_2719_; lean_object* v___y_2720_; 
v___x_2601_ = l_Lean_Name_mkStr2(v___x_2583_, v___x_2584_);
lean_inc(v_stx_2591_);
v___x_2602_ = l_Lean_Syntax_isOfKind(v_stx_2591_, v___x_2601_);
lean_dec(v___x_2601_);
if (v___x_2602_ == 0)
{
lean_object* v___x_2722_; lean_object* v___x_2723_; 
lean_dec(v_stx_2591_);
lean_dec(v_declName_2590_);
lean_dec_ref(v___x_2588_);
lean_dec(v___x_2587_);
lean_dec_ref(v___f_2585_);
v___x_2722_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2723_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0___redArg(v___x_2722_, v___y_2592_, v___y_2593_);
return v___x_2723_;
}
else
{
lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___y_2727_; lean_object* v___y_2728_; lean_object* v___y_2729_; lean_object* v___y_2730_; lean_object* v___y_2731_; lean_object* v___y_2732_; lean_object* v___y_2733_; lean_object* v___y_2734_; lean_object* v_val_2735_; lean_object* v___y_2760_; lean_object* v___y_2761_; lean_object* v___y_2762_; lean_object* v___y_2763_; lean_object* v___y_2764_; lean_object* v___y_2765_; lean_object* v___y_2766_; lean_object* v___y_2767_; lean_object* v___y_2772_; lean_object* v___y_2773_; lean_object* v___y_2774_; lean_object* v___y_2775_; lean_object* v___y_2776_; lean_object* v___y_2777_; lean_object* v___y_2778_; lean_object* v___y_2779_; uint8_t v___y_2780_; lean_object* v___y_2781_; uint8_t v_a_2782_; lean_object* v___y_2797_; lean_object* v___y_2798_; lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v___y_2802_; uint8_t v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2842_; lean_object* v___y_2843_; lean_object* v___y_2844_; lean_object* v___y_2845_; lean_object* v___y_2846_; lean_object* v___y_2847_; uint8_t v___y_2848_; lean_object* v___y_2849_; lean_object* v_msg_2850_; lean_object* v___y_2851_; lean_object* v___y_2852_; lean_object* v___y_2863_; lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2868_; lean_object* v___y_2869_; lean_object* v___y_2870_; lean_object* v___y_2871_; lean_object* v___y_2872_; lean_object* v___y_2873_; uint8_t v___y_2874_; lean_object* v___y_2875_; lean_object* v_a_2876_; lean_object* v___y_2909_; lean_object* v___y_2910_; lean_object* v___y_2911_; lean_object* v___y_2912_; lean_object* v___y_2913_; lean_object* v___y_2914_; lean_object* v___y_2915_; lean_object* v___y_3014_; lean_object* v___y_3015_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v_a_3020_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v_since_x3f_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v_typeChanged_x3f_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3076_; lean_object* v_text_x3f_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v_id_x3f_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___x_3102_; uint8_t v___x_3103_; 
v___x_2724_ = lean_unsigned_to_nat(0u);
v___x_2725_ = lean_unsigned_to_nat(1u);
v___x_3102_ = l_Lean_Syntax_getArg(v_stx_2591_, v___x_2725_);
v___x_3103_ = l_Lean_Syntax_isNone(v___x_3102_);
if (v___x_3103_ == 0)
{
uint8_t v___x_3104_; 
lean_inc(v___x_3102_);
v___x_3104_ = l_Lean_Syntax_matchesNull(v___x_3102_, v___x_2725_);
if (v___x_3104_ == 0)
{
lean_object* v___x_3105_; lean_object* v___x_3106_; 
lean_dec(v___x_3102_);
lean_dec(v_stx_2591_);
lean_dec(v_declName_2590_);
lean_dec_ref(v___x_2588_);
lean_dec(v___x_2587_);
lean_dec_ref(v___f_2585_);
v___x_3105_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_3106_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0___redArg(v___x_3105_, v___y_2592_, v___y_2593_);
return v___x_3106_;
}
else
{
lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3107_ = l_Lean_Syntax_getArg(v___x_3102_, v___x_2724_);
lean_dec(v___x_3102_);
v___x_3108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3107_);
v_id_x3f_3090_ = v___x_3108_;
v___y_3091_ = v___y_2592_;
v___y_3092_ = v___y_2593_;
goto v___jp_3089_;
}
}
else
{
lean_object* v___x_3109_; 
lean_dec(v___x_3102_);
v___x_3109_ = lean_box(0);
v_id_x3f_3090_ = v___x_3109_;
v___y_3091_ = v___y_2592_;
v___y_3092_ = v___y_2593_;
goto v___jp_3089_;
}
v___jp_2726_:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; uint8_t v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2736_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__19_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__19_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__19_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2737_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__21_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2738_ = lean_box(0);
v___x_2739_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__25_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__25_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__25_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2740_, 0, v___f_2585_);
v___x_2741_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2741_, 0, v___x_2737_);
lean_ctor_set(v___x_2741_, 1, v___x_2738_);
lean_ctor_set(v___x_2741_, 2, v___x_2738_);
lean_ctor_set(v___x_2741_, 3, v___x_2738_);
lean_ctor_set(v___x_2741_, 4, v___x_2739_);
lean_ctor_set(v___x_2741_, 5, v___x_2740_);
lean_inc(v_val_2735_);
v___x_2742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2742_, 0, v_val_2735_);
lean_ctor_set(v___x_2742_, 1, v_val_2735_);
v___x_2743_ = l_Lean_Syntax_ofRange(v___x_2742_, v___x_2602_);
v___x_2744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2744_, 0, v___x_2743_);
v___x_2745_ = 4;
v___x_2746_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2746_, 0, v___x_2741_);
lean_ctor_set(v___x_2746_, 1, v___x_2744_);
lean_ctor_set(v___x_2746_, 2, v___x_2738_);
lean_ctor_set_uint8(v___x_2746_, sizeof(void*)*3, v___x_2745_);
v___x_2747_ = lean_mk_empty_array_with_capacity(v___x_2725_);
v___x_2748_ = lean_array_push(v___x_2747_, v___x_2746_);
v___x_2749_ = l_Lean_MessageData_hint(v___x_2736_, v___x_2748_, v___x_2738_, v___x_2738_, v___x_2586_, v___y_2730_, v___y_2728_);
lean_dec_ref(v___x_2748_);
if (lean_obj_tag(v___x_2749_) == 0)
{
lean_object* v_a_2750_; 
v_a_2750_ = lean_ctor_get(v___x_2749_, 0);
lean_inc(v_a_2750_);
lean_dec_ref_known(v___x_2749_, 1);
v___y_2682_ = v___y_2727_;
v___y_2683_ = v___y_2729_;
v___y_2684_ = v___y_2731_;
v___y_2685_ = v___y_2732_;
v___y_2686_ = v___y_2733_;
v___y_2687_ = v___y_2734_;
v_hint_2688_ = v_a_2750_;
v___y_2689_ = v___y_2730_;
v___y_2690_ = v___y_2728_;
goto v___jp_2681_;
}
else
{
lean_object* v_a_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2758_; 
lean_dec_ref(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec(v___y_2729_);
lean_dec(v___y_2727_);
lean_dec(v_stx_2591_);
v_a_2751_ = lean_ctor_get(v___x_2749_, 0);
v_isSharedCheck_2758_ = !lean_is_exclusive(v___x_2749_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2753_ = v___x_2749_;
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_a_2751_);
lean_dec(v___x_2749_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2756_; 
if (v_isShared_2754_ == 0)
{
v___x_2756_ = v___x_2753_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_a_2751_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
}
}
}
}
v___jp_2759_:
{
if (lean_obj_tag(v___y_2765_) == 0)
{
lean_dec_ref(v___f_2585_);
v___y_2713_ = v___y_2761_;
v___y_2714_ = v___y_2760_;
v___y_2715_ = v___y_2762_;
v___y_2716_ = v___y_2763_;
v___y_2717_ = v___y_2764_;
v___y_2718_ = v___y_2765_;
v___y_2719_ = v___y_2766_;
v___y_2720_ = v___y_2767_;
goto v___jp_2712_;
}
else
{
lean_object* v_val_2768_; lean_object* v___x_2769_; 
v_val_2768_ = lean_ctor_get(v___y_2765_, 0);
v___x_2769_ = l_Lean_Syntax_getTailPos_x3f(v_val_2768_, v___x_2602_);
if (lean_obj_tag(v___x_2769_) == 1)
{
lean_object* v_val_2770_; 
v_val_2770_ = lean_ctor_get(v___x_2769_, 0);
lean_inc(v_val_2770_);
lean_dec_ref_known(v___x_2769_, 1);
v___y_2727_ = v___y_2761_;
v___y_2728_ = v___y_2760_;
v___y_2729_ = v___y_2762_;
v___y_2730_ = v___y_2763_;
v___y_2731_ = v___y_2764_;
v___y_2732_ = v___y_2765_;
v___y_2733_ = v___y_2766_;
v___y_2734_ = v___y_2767_;
v_val_2735_ = v_val_2770_;
goto v___jp_2726_;
}
else
{
lean_dec(v___x_2769_);
lean_dec_ref(v___f_2585_);
v___y_2713_ = v___y_2761_;
v___y_2714_ = v___y_2760_;
v___y_2715_ = v___y_2762_;
v___y_2716_ = v___y_2763_;
v___y_2717_ = v___y_2764_;
v___y_2718_ = v___y_2765_;
v___y_2719_ = v___y_2766_;
v___y_2720_ = v___y_2767_;
goto v___jp_2712_;
}
}
}
v___jp_2771_:
{
if (v_a_2782_ == 0)
{
if (lean_obj_tag(v___y_2778_) == 0)
{
if (v___y_2780_ == 0)
{
lean_dec_ref(v___y_2781_);
lean_dec_ref(v___y_2779_);
lean_dec_ref(v___f_2585_);
v___y_2665_ = v___y_2773_;
v___y_2666_ = v___y_2774_;
v___y_2667_ = v___y_2776_;
v___y_2668_ = v___y_2777_;
v___y_2669_ = v___y_2775_;
v___y_2670_ = v___y_2772_;
goto v___jp_2664_;
}
else
{
if (lean_obj_tag(v___y_2776_) == 0)
{
v___y_2760_ = v___y_2772_;
v___y_2761_ = v___y_2773_;
v___y_2762_ = v___y_2774_;
v___y_2763_ = v___y_2775_;
v___y_2764_ = v___y_2776_;
v___y_2765_ = v___y_2777_;
v___y_2766_ = v___y_2779_;
v___y_2767_ = v___y_2781_;
goto v___jp_2759_;
}
else
{
lean_object* v_val_2783_; lean_object* v___x_2784_; 
v_val_2783_ = lean_ctor_get(v___y_2776_, 0);
v___x_2784_ = l_Lean_Syntax_getTailPos_x3f(v_val_2783_, v___x_2602_);
if (lean_obj_tag(v___x_2784_) == 0)
{
v___y_2760_ = v___y_2772_;
v___y_2761_ = v___y_2773_;
v___y_2762_ = v___y_2774_;
v___y_2763_ = v___y_2775_;
v___y_2764_ = v___y_2776_;
v___y_2765_ = v___y_2777_;
v___y_2766_ = v___y_2779_;
v___y_2767_ = v___y_2781_;
goto v___jp_2759_;
}
else
{
lean_object* v_val_2785_; 
v_val_2785_ = lean_ctor_get(v___x_2784_, 0);
lean_inc(v_val_2785_);
lean_dec_ref_known(v___x_2784_, 1);
v___y_2727_ = v___y_2773_;
v___y_2728_ = v___y_2772_;
v___y_2729_ = v___y_2774_;
v___y_2730_ = v___y_2775_;
v___y_2731_ = v___y_2776_;
v___y_2732_ = v___y_2777_;
v___y_2733_ = v___y_2779_;
v___y_2734_ = v___y_2781_;
v_val_2735_ = v_val_2785_;
goto v___jp_2726_;
}
}
}
}
else
{
lean_dec_ref_known(v___y_2778_, 1);
lean_dec_ref(v___y_2781_);
lean_dec_ref(v___y_2779_);
lean_dec_ref(v___f_2585_);
v___y_2665_ = v___y_2773_;
v___y_2666_ = v___y_2774_;
v___y_2667_ = v___y_2776_;
v___y_2668_ = v___y_2777_;
v___y_2669_ = v___y_2775_;
v___y_2670_ = v___y_2772_;
goto v___jp_2664_;
}
}
else
{
lean_dec_ref(v___y_2781_);
lean_dec_ref(v___y_2779_);
lean_dec_ref(v___f_2585_);
if (lean_obj_tag(v___y_2778_) == 0)
{
v___y_2665_ = v___y_2773_;
v___y_2666_ = v___y_2774_;
v___y_2667_ = v___y_2776_;
v___y_2668_ = v___y_2777_;
v___y_2669_ = v___y_2775_;
v___y_2670_ = v___y_2772_;
goto v___jp_2664_;
}
else
{
lean_object* v___x_2786_; lean_object* v___x_2787_; 
lean_dec_ref_known(v___y_2778_, 1);
v___x_2786_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__28_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__28_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__28_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2787_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1(v___x_2786_, v___y_2775_, v___y_2772_);
if (lean_obj_tag(v___x_2787_) == 0)
{
lean_dec_ref_known(v___x_2787_, 1);
v___y_2665_ = v___y_2773_;
v___y_2666_ = v___y_2774_;
v___y_2667_ = v___y_2776_;
v___y_2668_ = v___y_2777_;
v___y_2669_ = v___y_2775_;
v___y_2670_ = v___y_2772_;
goto v___jp_2664_;
}
else
{
lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2795_; 
lean_dec(v___y_2777_);
lean_dec(v___y_2776_);
lean_dec(v___y_2774_);
lean_dec(v___y_2773_);
lean_dec(v_stx_2591_);
v_a_2788_ = lean_ctor_get(v___x_2787_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2787_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2790_ = v___x_2787_;
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_dec(v___x_2787_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2793_; 
if (v_isShared_2791_ == 0)
{
v___x_2793_ = v___x_2790_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_a_2788_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
}
}
}
}
v___jp_2796_:
{
lean_object* v___x_2807_; 
lean_inc_ref(v___y_2797_);
v___x_2807_ = l_Lean_Environment_find_x3f(v___y_2797_, v_declName_2590_, v___x_2586_);
if (lean_obj_tag(v___x_2807_) == 1)
{
lean_object* v_val_2808_; lean_object* v___x_2809_; 
v_val_2808_ = lean_ctor_get(v___x_2807_, 0);
lean_inc(v_val_2808_);
lean_dec_ref_known(v___x_2807_, 1);
v___x_2809_ = l_Lean_Environment_find_x3f(v___y_2797_, v___y_2804_, v___x_2586_);
if (lean_obj_tag(v___x_2809_) == 1)
{
lean_object* v_val_2810_; uint8_t v___x_2811_; uint8_t v___x_2812_; uint8_t v___x_2813_; lean_object* v___x_2814_; uint64_t v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
v_val_2810_ = lean_ctor_get(v___x_2809_, 0);
lean_inc(v_val_2810_);
lean_dec_ref_known(v___x_2809_, 1);
v___x_2811_ = 1;
v___x_2812_ = 0;
v___x_2813_ = 2;
v___x_2814_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_2814_, 0, v___x_2586_);
lean_ctor_set_uint8(v___x_2814_, 1, v___x_2586_);
lean_ctor_set_uint8(v___x_2814_, 2, v___x_2586_);
lean_ctor_set_uint8(v___x_2814_, 3, v___x_2586_);
lean_ctor_set_uint8(v___x_2814_, 4, v___x_2586_);
lean_ctor_set_uint8(v___x_2814_, 5, v___y_2803_);
lean_ctor_set_uint8(v___x_2814_, 6, v___y_2803_);
lean_ctor_set_uint8(v___x_2814_, 7, v___x_2586_);
lean_ctor_set_uint8(v___x_2814_, 8, v___y_2803_);
lean_ctor_set_uint8(v___x_2814_, 9, v___x_2811_);
lean_ctor_set_uint8(v___x_2814_, 10, v___x_2812_);
lean_ctor_set_uint8(v___x_2814_, 11, v___y_2803_);
lean_ctor_set_uint8(v___x_2814_, 12, v___y_2803_);
lean_ctor_set_uint8(v___x_2814_, 13, v___y_2803_);
lean_ctor_set_uint8(v___x_2814_, 14, v___x_2813_);
lean_ctor_set_uint8(v___x_2814_, 15, v___y_2803_);
lean_ctor_set_uint8(v___x_2814_, 16, v___y_2803_);
lean_ctor_set_uint8(v___x_2814_, 17, v___y_2803_);
lean_ctor_set_uint8(v___x_2814_, 18, v___y_2803_);
lean_ctor_set_uint8(v___x_2814_, 19, v___x_2586_);
v___x_2815_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2814_);
v___x_2816_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2816_, 0, v___x_2814_);
lean_ctor_set_uint64(v___x_2816_, sizeof(void*)*1, v___x_2815_);
v___x_2817_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_2818_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2819_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2820_ = lean_box(0);
lean_inc(v___x_2587_);
v___x_2821_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2821_, 0, v___x_2816_);
lean_ctor_set(v___x_2821_, 1, v___x_2587_);
lean_ctor_set(v___x_2821_, 2, v___x_2818_);
lean_ctor_set(v___x_2821_, 3, v___x_2819_);
lean_ctor_set(v___x_2821_, 4, v___x_2820_);
lean_ctor_set(v___x_2821_, 5, v___x_2724_);
lean_ctor_set(v___x_2821_, 6, v___x_2820_);
lean_ctor_set_uint8(v___x_2821_, sizeof(void*)*7, v___x_2586_);
lean_ctor_set_uint8(v___x_2821_, sizeof(void*)*7 + 1, v___x_2586_);
lean_ctor_set_uint8(v___x_2821_, sizeof(void*)*7 + 2, v___x_2586_);
lean_ctor_set_uint8(v___x_2821_, sizeof(void*)*7 + 3, v___x_2602_);
v___x_2822_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2823_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2824_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2825_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2825_, 0, v___x_2822_);
lean_ctor_set(v___x_2825_, 1, v___x_2823_);
lean_ctor_set(v___x_2825_, 2, v___x_2587_);
lean_ctor_set(v___x_2825_, 3, v___x_2817_);
lean_ctor_set(v___x_2825_, 4, v___x_2824_);
v___x_2826_ = lean_st_mk_ref(v___x_2825_);
v___x_2827_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq(v_val_2808_, v_val_2810_, v___x_2821_, v___x_2826_, v___y_2805_, v___y_2806_);
lean_dec_ref_known(v___x_2821_, 7);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v_a_2828_; lean_object* v___x_2829_; uint8_t v___x_2830_; 
v_a_2828_ = lean_ctor_get(v___x_2827_, 0);
lean_inc(v_a_2828_);
lean_dec_ref_known(v___x_2827_, 1);
v___x_2829_ = lean_st_ref_get(v___x_2826_);
lean_dec(v___x_2826_);
lean_dec(v___x_2829_);
v___x_2830_ = lean_unbox(v_a_2828_);
lean_dec(v_a_2828_);
v___y_2772_ = v___y_2806_;
v___y_2773_ = v___y_2798_;
v___y_2774_ = v___y_2799_;
v___y_2775_ = v___y_2805_;
v___y_2776_ = v___y_2800_;
v___y_2777_ = v___y_2801_;
v___y_2778_ = v___y_2802_;
v___y_2779_ = v_val_2810_;
v___y_2780_ = v___y_2803_;
v___y_2781_ = v_val_2808_;
v_a_2782_ = v___x_2830_;
goto v___jp_2771_;
}
else
{
lean_dec(v___x_2826_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v_a_2831_; uint8_t v___x_2832_; 
v_a_2831_ = lean_ctor_get(v___x_2827_, 0);
lean_inc(v_a_2831_);
lean_dec_ref_known(v___x_2827_, 1);
v___x_2832_ = lean_unbox(v_a_2831_);
lean_dec(v_a_2831_);
v___y_2772_ = v___y_2806_;
v___y_2773_ = v___y_2798_;
v___y_2774_ = v___y_2799_;
v___y_2775_ = v___y_2805_;
v___y_2776_ = v___y_2800_;
v___y_2777_ = v___y_2801_;
v___y_2778_ = v___y_2802_;
v___y_2779_ = v_val_2810_;
v___y_2780_ = v___y_2803_;
v___y_2781_ = v_val_2808_;
v_a_2782_ = v___x_2832_;
goto v___jp_2771_;
}
else
{
lean_object* v_a_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2840_; 
lean_dec(v_val_2810_);
lean_dec(v_val_2808_);
lean_dec(v___y_2802_);
lean_dec(v___y_2801_);
lean_dec(v___y_2800_);
lean_dec(v___y_2799_);
lean_dec(v___y_2798_);
lean_dec(v_stx_2591_);
lean_dec_ref(v___f_2585_);
v_a_2833_ = lean_ctor_get(v___x_2827_, 0);
v_isSharedCheck_2840_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2840_ == 0)
{
v___x_2835_ = v___x_2827_;
v_isShared_2836_ = v_isSharedCheck_2840_;
goto v_resetjp_2834_;
}
else
{
lean_inc(v_a_2833_);
lean_dec(v___x_2827_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2840_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
lean_object* v___x_2838_; 
if (v_isShared_2836_ == 0)
{
v___x_2838_ = v___x_2835_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v_a_2833_);
v___x_2838_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
return v___x_2838_;
}
}
}
}
}
else
{
lean_dec(v___x_2809_);
lean_dec(v_val_2808_);
lean_dec(v___y_2802_);
lean_dec(v___x_2587_);
lean_dec_ref(v___f_2585_);
v___y_2665_ = v___y_2798_;
v___y_2666_ = v___y_2799_;
v___y_2667_ = v___y_2800_;
v___y_2668_ = v___y_2801_;
v___y_2669_ = v___y_2805_;
v___y_2670_ = v___y_2806_;
goto v___jp_2664_;
}
}
else
{
lean_dec(v___x_2807_);
lean_dec(v___y_2804_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2797_);
lean_dec(v___x_2587_);
lean_dec_ref(v___f_2585_);
v___y_2665_ = v___y_2798_;
v___y_2666_ = v___y_2799_;
v___y_2667_ = v___y_2800_;
v___y_2668_ = v___y_2801_;
v___y_2669_ = v___y_2805_;
v___y_2670_ = v___y_2806_;
goto v___jp_2664_;
}
}
v___jp_2841_:
{
lean_object* v___x_2853_; 
v___x_2853_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1(v_msg_2850_, v___y_2851_, v___y_2852_);
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_dec_ref_known(v___x_2853_, 1);
v___y_2797_ = v___y_2842_;
v___y_2798_ = v___y_2843_;
v___y_2799_ = v___y_2844_;
v___y_2800_ = v___y_2845_;
v___y_2801_ = v___y_2846_;
v___y_2802_ = v___y_2847_;
v___y_2803_ = v___y_2848_;
v___y_2804_ = v___y_2849_;
v___y_2805_ = v___y_2851_;
v___y_2806_ = v___y_2852_;
goto v___jp_2796_;
}
else
{
lean_object* v_a_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2861_; 
lean_dec(v___y_2849_);
lean_dec(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v_stx_2591_);
lean_dec(v_declName_2590_);
lean_dec(v___x_2587_);
lean_dec_ref(v___f_2585_);
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
v___jp_2862_:
{
if (lean_obj_tag(v_a_2876_) == 1)
{
lean_object* v_val_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2907_; 
v_val_2877_ = lean_ctor_get(v_a_2876_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v_a_2876_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2879_ = v_a_2876_;
v_isShared_2880_ = v_isSharedCheck_2907_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_val_2877_);
lean_dec(v_a_2876_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_2907_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; uint8_t v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2894_; 
v___x_2881_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__36_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__36_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__36_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2881_);
lean_ctor_set(v___x_2882_, 1, v___y_2873_);
v___x_2883_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__38_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__38_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__38_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2884_, 0, v___x_2882_);
lean_ctor_set(v___x_2884_, 1, v___x_2883_);
v___x_2885_ = l_Lean_Name_toString(v_val_2877_, v___x_2602_);
v___x_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2886_, 0, v___x_2885_);
v___x_2887_ = lean_box(0);
v___x_2888_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2888_, 0, v___x_2886_);
lean_ctor_set(v___x_2888_, 1, v___x_2887_);
lean_ctor_set(v___x_2888_, 2, v___x_2887_);
lean_ctor_set(v___x_2888_, 3, v___x_2887_);
lean_ctor_set(v___x_2888_, 4, v___x_2887_);
lean_ctor_set(v___x_2888_, 5, v___x_2887_);
v___x_2889_ = 0;
v___x_2890_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2890_, 0, v___x_2888_);
lean_ctor_set(v___x_2890_, 1, v___x_2887_);
lean_ctor_set(v___x_2890_, 2, v___x_2887_);
lean_ctor_set_uint8(v___x_2890_, sizeof(void*)*3, v___x_2889_);
v___x_2891_ = lean_mk_empty_array_with_capacity(v___x_2725_);
v___x_2892_ = lean_array_push(v___x_2891_, v___x_2890_);
if (v_isShared_2880_ == 0)
{
lean_ctor_set(v___x_2879_, 0, v___y_2866_);
v___x_2894_ = v___x_2879_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v___y_2866_);
v___x_2894_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
lean_object* v___x_2895_; 
v___x_2895_ = l_Lean_MessageData_hint(v___x_2884_, v___x_2892_, v___x_2894_, v___x_2887_, v___x_2586_, v___y_2871_, v___y_2868_);
lean_dec_ref(v___x_2892_);
if (lean_obj_tag(v___x_2895_) == 0)
{
lean_object* v_a_2896_; lean_object* v___x_2897_; 
v_a_2896_ = lean_ctor_get(v___x_2895_, 0);
lean_inc(v_a_2896_);
lean_dec_ref_known(v___x_2895_, 1);
v___x_2897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2897_, 0, v___y_2867_);
lean_ctor_set(v___x_2897_, 1, v_a_2896_);
v___y_2842_ = v___y_2869_;
v___y_2843_ = v___y_2863_;
v___y_2844_ = v___y_2870_;
v___y_2845_ = v___y_2864_;
v___y_2846_ = v___y_2872_;
v___y_2847_ = v___y_2865_;
v___y_2848_ = v___y_2874_;
v___y_2849_ = v___y_2875_;
v_msg_2850_ = v___x_2897_;
v___y_2851_ = v___y_2871_;
v___y_2852_ = v___y_2868_;
goto v___jp_2841_;
}
else
{
lean_object* v_a_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2905_; 
lean_dec(v___y_2875_);
lean_dec(v___y_2872_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
lean_dec_ref(v___y_2867_);
lean_dec(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec(v___y_2863_);
lean_dec(v_stx_2591_);
lean_dec(v_declName_2590_);
lean_dec(v___x_2587_);
lean_dec_ref(v___f_2585_);
v_a_2898_ = lean_ctor_get(v___x_2895_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2900_ = v___x_2895_;
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_a_2898_);
lean_dec(v___x_2895_);
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
}
else
{
lean_dec(v_a_2876_);
lean_dec_ref(v___y_2873_);
lean_dec(v___y_2866_);
v___y_2842_ = v___y_2869_;
v___y_2843_ = v___y_2863_;
v___y_2844_ = v___y_2870_;
v___y_2845_ = v___y_2864_;
v___y_2846_ = v___y_2872_;
v___y_2847_ = v___y_2865_;
v___y_2848_ = v___y_2874_;
v___y_2849_ = v___y_2875_;
v_msg_2850_ = v___y_2867_;
v___y_2851_ = v___y_2871_;
v___y_2852_ = v___y_2868_;
goto v___jp_2841_;
}
}
v___jp_2908_:
{
if (lean_obj_tag(v___y_2909_) == 1)
{
lean_object* v_val_2916_; lean_object* v___x_2917_; 
v_val_2916_ = lean_ctor_get(v___y_2909_, 0);
lean_inc(v_val_2916_);
v___x_2917_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2(v_val_2916_, v___x_2586_, v___y_2914_, v___y_2915_);
if (lean_obj_tag(v___x_2917_) == 0)
{
lean_object* v___x_2918_; lean_object* v_a_2919_; lean_object* v___x_2920_; uint8_t v___x_2921_; 
lean_dec_ref_known(v___x_2917_, 1);
v___x_2918_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3(v___y_2914_, v___y_2915_);
v_a_2919_ = lean_ctor_get(v___x_2918_, 0);
lean_inc(v_a_2919_);
lean_dec_ref(v___x_2918_);
v___x_2920_ = l_Lean_Linter_linter_deprecated;
v___x_2921_ = l_Lean_Linter_getLinterValue(v___x_2920_, v_a_2919_);
lean_dec(v_a_2919_);
if (v___x_2921_ == 0)
{
lean_dec(v___y_2913_);
lean_dec(v_declName_2590_);
lean_dec_ref(v___x_2588_);
lean_dec(v___x_2587_);
lean_dec_ref(v___f_2585_);
v___y_2665_ = v___y_2909_;
v___y_2666_ = v___y_2910_;
v___y_2667_ = v___y_2911_;
v___y_2668_ = v___y_2912_;
v___y_2669_ = v___y_2914_;
v___y_2670_ = v___y_2915_;
goto v___jp_2664_;
}
else
{
lean_object* v___x_2922_; lean_object* v_env_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; uint8_t v___x_2926_; 
lean_inc(v_val_2916_);
v___x_2922_ = lean_st_ref_get(v___y_2915_);
v_env_2923_ = lean_ctor_get(v___x_2922_, 0);
lean_inc_ref(v_env_2923_);
lean_dec(v___x_2922_);
v___x_2924_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2914_);
v___x_2925_ = l_Lean_Linter_linter_deprecated_deprecatedTarget;
v___x_2926_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4(v___x_2924_, v___x_2925_);
lean_dec_ref(v___x_2924_);
if (v___x_2926_ == 0)
{
lean_dec_ref(v___x_2588_);
v___y_2797_ = v_env_2923_;
v___y_2798_ = v___y_2909_;
v___y_2799_ = v___y_2910_;
v___y_2800_ = v___y_2911_;
v___y_2801_ = v___y_2912_;
v___y_2802_ = v___y_2913_;
v___y_2803_ = v___x_2921_;
v___y_2804_ = v_val_2916_;
v___y_2805_ = v___y_2914_;
v___y_2806_ = v___y_2915_;
goto v___jp_2796_;
}
else
{
lean_object* v___x_2927_; 
lean_inc(v_val_2916_);
lean_inc_ref(v_env_2923_);
v___x_2927_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v___x_2588_, v_a_2589_, v___x_2586_, v_env_2923_, v_val_2916_);
if (lean_obj_tag(v___x_2927_) == 1)
{
lean_object* v_val_2928_; lean_object* v_name_2929_; lean_object* v_newName_x3f_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; 
v_val_2928_ = lean_ctor_get(v___x_2927_, 0);
lean_inc(v_val_2928_);
lean_dec_ref_known(v___x_2927_, 1);
v_name_2929_ = lean_ctor_get(v___x_2925_, 0);
v_newName_x3f_2930_ = lean_ctor_get(v_val_2928_, 0);
lean_inc(v_newName_x3f_2930_);
lean_dec(v_val_2928_);
v___x_2931_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__40_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__40_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__40_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
lean_inc(v_name_2929_);
v___x_2932_ = l_Lean_MessageData_ofName(v_name_2929_);
v___x_2933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2933_, 0, v___x_2931_);
lean_ctor_set(v___x_2933_, 1, v___x_2932_);
v___x_2934_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2935_, 0, v___x_2933_);
lean_ctor_set(v___x_2935_, 1, v___x_2934_);
v___x_2936_ = l_Lean_MessageData_note(v___x_2935_);
if (lean_obj_tag(v_newName_x3f_2930_) == 0)
{
lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; 
v___x_2937_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
lean_inc(v_val_2916_);
v___x_2938_ = l_Lean_MessageData_ofConstName(v_val_2916_, v___x_2602_);
v___x_2939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2939_, 0, v___x_2937_);
lean_ctor_set(v___x_2939_, 1, v___x_2938_);
v___x_2940_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2941_, 0, v___x_2939_);
lean_ctor_set(v___x_2941_, 1, v___x_2940_);
lean_inc(v_declName_2590_);
v___x_2942_ = l_Lean_MessageData_ofConstName(v_declName_2590_, v___x_2602_);
v___x_2943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2943_, 0, v___x_2941_);
lean_ctor_set(v___x_2943_, 1, v___x_2942_);
v___x_2944_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__48_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__48_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__48_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2945_, 0, v___x_2943_);
lean_ctor_set(v___x_2945_, 1, v___x_2944_);
v___x_2946_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2946_, 0, v___x_2945_);
lean_ctor_set(v___x_2946_, 1, v___x_2936_);
v___x_2947_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1(v___x_2946_, v___y_2914_, v___y_2915_);
if (lean_obj_tag(v___x_2947_) == 0)
{
lean_dec_ref_known(v___x_2947_, 1);
v___y_2797_ = v_env_2923_;
v___y_2798_ = v___y_2909_;
v___y_2799_ = v___y_2910_;
v___y_2800_ = v___y_2911_;
v___y_2801_ = v___y_2912_;
v___y_2802_ = v___y_2913_;
v___y_2803_ = v___x_2921_;
v___y_2804_ = v_val_2916_;
v___y_2805_ = v___y_2914_;
v___y_2806_ = v___y_2915_;
goto v___jp_2796_;
}
else
{
lean_object* v_a_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2955_; 
lean_dec_ref(v_env_2923_);
lean_dec(v_val_2916_);
lean_dec_ref_known(v___y_2909_, 1);
lean_dec(v___y_2913_);
lean_dec(v___y_2912_);
lean_dec(v___y_2911_);
lean_dec(v___y_2910_);
lean_dec(v_stx_2591_);
lean_dec(v_declName_2590_);
lean_dec(v___x_2587_);
lean_dec_ref(v___f_2585_);
v_a_2948_ = lean_ctor_get(v___x_2947_, 0);
v_isSharedCheck_2955_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2950_ = v___x_2947_;
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_a_2948_);
lean_dec(v___x_2947_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2953_; 
if (v_isShared_2951_ == 0)
{
v___x_2953_ = v___x_2950_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v_a_2948_);
v___x_2953_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
return v___x_2953_;
}
}
}
}
else
{
lean_object* v_val_2956_; uint8_t v___x_2957_; 
v_val_2956_ = lean_ctor_get(v_newName_x3f_2930_, 0);
lean_inc(v_val_2956_);
lean_dec_ref_known(v_newName_x3f_2930_, 1);
v___x_2957_ = lean_name_eq(v_val_2956_, v_val_2916_);
if (v___x_2957_ == 0)
{
if (v___x_2926_ == 0)
{
lean_dec(v_val_2956_);
lean_dec_ref(v___x_2936_);
v___y_2797_ = v_env_2923_;
v___y_2798_ = v___y_2909_;
v___y_2799_ = v___y_2910_;
v___y_2800_ = v___y_2911_;
v___y_2801_ = v___y_2912_;
v___y_2802_ = v___y_2913_;
v___y_2803_ = v___x_2921_;
v___y_2804_ = v_val_2916_;
v___y_2805_ = v___y_2914_;
v___y_2806_ = v___y_2915_;
goto v___jp_2796_;
}
else
{
lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; 
v___x_2958_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
lean_inc(v_val_2916_);
v___x_2959_ = l_Lean_MessageData_ofConstName(v_val_2916_, v___x_2602_);
v___x_2960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2958_);
lean_ctor_set(v___x_2960_, 1, v___x_2959_);
v___x_2961_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__50_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__50_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__50_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2962_, 0, v___x_2960_);
lean_ctor_set(v___x_2962_, 1, v___x_2961_);
lean_inc(v_val_2956_);
v___x_2963_ = l_Lean_MessageData_ofConstName(v_val_2956_, v___x_2602_);
lean_inc_ref_n(v___x_2963_, 2);
v___x_2964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2964_, 0, v___x_2962_);
lean_ctor_set(v___x_2964_, 1, v___x_2963_);
v___x_2965_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__52_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__52_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__52_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2966_, 0, v___x_2964_);
lean_ctor_set(v___x_2966_, 1, v___x_2965_);
lean_inc(v_declName_2590_);
v___x_2967_ = l_Lean_MessageData_ofConstName(v_declName_2590_, v___x_2602_);
v___x_2968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2968_, 0, v___x_2966_);
lean_ctor_set(v___x_2968_, 1, v___x_2967_);
v___x_2969_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__54_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__54_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__54_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2970_, 0, v___x_2968_);
lean_ctor_set(v___x_2970_, 1, v___x_2969_);
v___x_2971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2971_, 0, v___x_2970_);
lean_ctor_set(v___x_2971_, 1, v___x_2963_);
v___x_2972_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__56_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__56_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__56_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2971_);
lean_ctor_set(v___x_2973_, 1, v___x_2972_);
v___x_2974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2974_, 0, v___x_2973_);
lean_ctor_set(v___x_2974_, 1, v___x_2936_);
if (lean_obj_tag(v___y_2912_) == 1)
{
lean_object* v_val_2975_; lean_object* v___x_2976_; 
v_val_2975_ = lean_ctor_get(v___y_2912_, 0);
v___x_2976_ = l_Lean_Syntax_getRange_x3f(v_val_2975_, v___x_2602_);
if (lean_obj_tag(v___x_2976_) == 0)
{
lean_dec_ref(v___x_2963_);
lean_dec(v_val_2956_);
v___y_2842_ = v_env_2923_;
v___y_2843_ = v___y_2909_;
v___y_2844_ = v___y_2910_;
v___y_2845_ = v___y_2911_;
v___y_2846_ = v___y_2912_;
v___y_2847_ = v___y_2913_;
v___y_2848_ = v___x_2921_;
v___y_2849_ = v_val_2916_;
v_msg_2850_ = v___x_2974_;
v___y_2851_ = v___y_2914_;
v___y_2852_ = v___y_2915_;
goto v___jp_2841_;
}
else
{
uint8_t v___x_2977_; uint8_t v___x_2978_; uint8_t v___x_2979_; lean_object* v___x_2980_; uint64_t v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; 
lean_inc(v_val_2975_);
lean_dec_ref_known(v___x_2976_, 1);
v___x_2977_ = 1;
v___x_2978_ = 0;
v___x_2979_ = 2;
v___x_2980_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_2980_, 0, v___x_2957_);
lean_ctor_set_uint8(v___x_2980_, 1, v___x_2957_);
lean_ctor_set_uint8(v___x_2980_, 2, v___x_2957_);
lean_ctor_set_uint8(v___x_2980_, 3, v___x_2957_);
lean_ctor_set_uint8(v___x_2980_, 4, v___x_2957_);
lean_ctor_set_uint8(v___x_2980_, 5, v___x_2926_);
lean_ctor_set_uint8(v___x_2980_, 6, v___x_2926_);
lean_ctor_set_uint8(v___x_2980_, 7, v___x_2957_);
lean_ctor_set_uint8(v___x_2980_, 8, v___x_2926_);
lean_ctor_set_uint8(v___x_2980_, 9, v___x_2977_);
lean_ctor_set_uint8(v___x_2980_, 10, v___x_2978_);
lean_ctor_set_uint8(v___x_2980_, 11, v___x_2926_);
lean_ctor_set_uint8(v___x_2980_, 12, v___x_2926_);
lean_ctor_set_uint8(v___x_2980_, 13, v___x_2926_);
lean_ctor_set_uint8(v___x_2980_, 14, v___x_2979_);
lean_ctor_set_uint8(v___x_2980_, 15, v___x_2926_);
lean_ctor_set_uint8(v___x_2980_, 16, v___x_2926_);
lean_ctor_set_uint8(v___x_2980_, 17, v___x_2926_);
lean_ctor_set_uint8(v___x_2980_, 18, v___x_2926_);
lean_ctor_set_uint8(v___x_2980_, 19, v___x_2957_);
v___x_2981_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2980_);
v___x_2982_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2982_, 0, v___x_2980_);
lean_ctor_set_uint64(v___x_2982_, sizeof(void*)*1, v___x_2981_);
v___x_2983_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_2984_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2985_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2986_ = lean_box(0);
lean_inc_n(v___x_2587_, 2);
v___x_2987_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2987_, 0, v___x_2982_);
lean_ctor_set(v___x_2987_, 1, v___x_2587_);
lean_ctor_set(v___x_2987_, 2, v___x_2984_);
lean_ctor_set(v___x_2987_, 3, v___x_2985_);
lean_ctor_set(v___x_2987_, 4, v___x_2986_);
lean_ctor_set(v___x_2987_, 5, v___x_2724_);
lean_ctor_set(v___x_2987_, 6, v___x_2986_);
lean_ctor_set_uint8(v___x_2987_, sizeof(void*)*7, v___x_2586_);
lean_ctor_set_uint8(v___x_2987_, sizeof(void*)*7 + 1, v___x_2586_);
lean_ctor_set_uint8(v___x_2987_, sizeof(void*)*7 + 2, v___x_2586_);
lean_ctor_set_uint8(v___x_2987_, sizeof(void*)*7 + 3, v___x_2602_);
v___x_2988_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2989_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2990_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2991_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2991_, 0, v___x_2988_);
lean_ctor_set(v___x_2991_, 1, v___x_2989_);
lean_ctor_set(v___x_2991_, 2, v___x_2587_);
lean_ctor_set(v___x_2991_, 3, v___x_2983_);
lean_ctor_set(v___x_2991_, 4, v___x_2990_);
v___x_2992_ = lean_st_mk_ref(v___x_2991_);
v___x_2993_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5(v_val_2956_, v___x_2586_, v___x_2987_, v___x_2992_, v___y_2914_, v___y_2915_);
lean_dec_ref_known(v___x_2987_, 7);
if (lean_obj_tag(v___x_2993_) == 0)
{
lean_object* v_a_2994_; lean_object* v___x_2995_; 
v_a_2994_ = lean_ctor_get(v___x_2993_, 0);
lean_inc(v_a_2994_);
lean_dec_ref_known(v___x_2993_, 1);
v___x_2995_ = lean_st_ref_get(v___x_2992_);
lean_dec(v___x_2992_);
lean_dec(v___x_2995_);
v___y_2863_ = v___y_2909_;
v___y_2864_ = v___y_2911_;
v___y_2865_ = v___y_2913_;
v___y_2866_ = v_val_2975_;
v___y_2867_ = v___x_2974_;
v___y_2868_ = v___y_2915_;
v___y_2869_ = v_env_2923_;
v___y_2870_ = v___y_2910_;
v___y_2871_ = v___y_2914_;
v___y_2872_ = v___y_2912_;
v___y_2873_ = v___x_2963_;
v___y_2874_ = v___x_2921_;
v___y_2875_ = v_val_2916_;
v_a_2876_ = v_a_2994_;
goto v___jp_2862_;
}
else
{
lean_dec(v___x_2992_);
if (lean_obj_tag(v___x_2993_) == 0)
{
lean_object* v_a_2996_; 
v_a_2996_ = lean_ctor_get(v___x_2993_, 0);
lean_inc(v_a_2996_);
lean_dec_ref_known(v___x_2993_, 1);
v___y_2863_ = v___y_2909_;
v___y_2864_ = v___y_2911_;
v___y_2865_ = v___y_2913_;
v___y_2866_ = v_val_2975_;
v___y_2867_ = v___x_2974_;
v___y_2868_ = v___y_2915_;
v___y_2869_ = v_env_2923_;
v___y_2870_ = v___y_2910_;
v___y_2871_ = v___y_2914_;
v___y_2872_ = v___y_2912_;
v___y_2873_ = v___x_2963_;
v___y_2874_ = v___x_2921_;
v___y_2875_ = v_val_2916_;
v_a_2876_ = v_a_2996_;
goto v___jp_2862_;
}
else
{
lean_object* v_a_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3004_; 
lean_dec_ref_known(v___y_2912_, 1);
lean_dec(v_val_2975_);
lean_dec_ref_known(v___x_2974_, 2);
lean_dec_ref(v___x_2963_);
lean_dec_ref(v_env_2923_);
lean_dec(v_val_2916_);
lean_dec_ref_known(v___y_2909_, 1);
lean_dec(v___y_2913_);
lean_dec(v___y_2911_);
lean_dec(v___y_2910_);
lean_dec(v_stx_2591_);
lean_dec(v_declName_2590_);
lean_dec(v___x_2587_);
lean_dec_ref(v___f_2585_);
v_a_2997_ = lean_ctor_get(v___x_2993_, 0);
v_isSharedCheck_3004_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3004_ == 0)
{
v___x_2999_ = v___x_2993_;
v_isShared_3000_ = v_isSharedCheck_3004_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_a_2997_);
lean_dec(v___x_2993_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3004_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
lean_object* v___x_3002_; 
if (v_isShared_3000_ == 0)
{
v___x_3002_ = v___x_2999_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v_a_2997_);
v___x_3002_ = v_reuseFailAlloc_3003_;
goto v_reusejp_3001_;
}
v_reusejp_3001_:
{
return v___x_3002_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_2963_);
lean_dec(v_val_2956_);
v___y_2842_ = v_env_2923_;
v___y_2843_ = v___y_2909_;
v___y_2844_ = v___y_2910_;
v___y_2845_ = v___y_2911_;
v___y_2846_ = v___y_2912_;
v___y_2847_ = v___y_2913_;
v___y_2848_ = v___x_2921_;
v___y_2849_ = v_val_2916_;
v_msg_2850_ = v___x_2974_;
v___y_2851_ = v___y_2914_;
v___y_2852_ = v___y_2915_;
goto v___jp_2841_;
}
}
}
else
{
lean_dec(v_val_2956_);
lean_dec_ref(v___x_2936_);
v___y_2797_ = v_env_2923_;
v___y_2798_ = v___y_2909_;
v___y_2799_ = v___y_2910_;
v___y_2800_ = v___y_2911_;
v___y_2801_ = v___y_2912_;
v___y_2802_ = v___y_2913_;
v___y_2803_ = v___x_2921_;
v___y_2804_ = v_val_2916_;
v___y_2805_ = v___y_2914_;
v___y_2806_ = v___y_2915_;
goto v___jp_2796_;
}
}
}
else
{
lean_dec(v___x_2927_);
v___y_2797_ = v_env_2923_;
v___y_2798_ = v___y_2909_;
v___y_2799_ = v___y_2910_;
v___y_2800_ = v___y_2911_;
v___y_2801_ = v___y_2912_;
v___y_2802_ = v___y_2913_;
v___y_2803_ = v___x_2921_;
v___y_2804_ = v_val_2916_;
v___y_2805_ = v___y_2914_;
v___y_2806_ = v___y_2915_;
goto v___jp_2796_;
}
}
}
}
else
{
lean_object* v_a_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3012_; 
lean_dec_ref_known(v___y_2909_, 1);
lean_dec(v___y_2913_);
lean_dec(v___y_2912_);
lean_dec(v___y_2911_);
lean_dec(v___y_2910_);
lean_dec(v_stx_2591_);
lean_dec(v_declName_2590_);
lean_dec_ref(v___x_2588_);
lean_dec(v___x_2587_);
lean_dec_ref(v___f_2585_);
v_a_3005_ = lean_ctor_get(v___x_2917_, 0);
v_isSharedCheck_3012_ = !lean_is_exclusive(v___x_2917_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_3007_ = v___x_2917_;
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_a_3005_);
lean_dec(v___x_2917_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v___x_3010_; 
if (v_isShared_3008_ == 0)
{
v___x_3010_ = v___x_3007_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v_a_3005_);
v___x_3010_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
return v___x_3010_;
}
}
}
}
else
{
lean_dec(v___y_2913_);
lean_dec(v_declName_2590_);
lean_dec_ref(v___x_2588_);
lean_dec(v___x_2587_);
lean_dec_ref(v___f_2585_);
v___y_2665_ = v___y_2909_;
v___y_2666_ = v___y_2910_;
v___y_2667_ = v___y_2911_;
v___y_2668_ = v___y_2912_;
v___y_2669_ = v___y_2914_;
v___y_2670_ = v___y_2915_;
goto v___jp_2664_;
}
}
v___jp_3013_:
{
lean_object* v___x_3021_; uint8_t v___x_3022_; 
lean_inc(v_declName_2590_);
v___x_3021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3021_, 0, v_declName_2590_);
v___x_3022_ = l_instBEqOption_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6(v_a_3020_, v___x_3021_);
lean_dec_ref_known(v___x_3021_, 1);
if (v___x_3022_ == 0)
{
v___y_2909_ = v_a_3020_;
v___y_2910_ = v___y_3015_;
v___y_2911_ = v___y_3016_;
v___y_2912_ = v___y_3017_;
v___y_2913_ = v___y_3019_;
v___y_2914_ = v___y_3014_;
v___y_2915_ = v___y_3018_;
goto v___jp_2908_;
}
else
{
lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v_a_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3036_; 
lean_dec(v_a_3020_);
lean_dec(v___y_3019_);
lean_dec(v___y_3017_);
lean_dec(v___y_3016_);
lean_dec(v___y_3015_);
lean_dec(v_stx_2591_);
lean_dec_ref(v___x_2588_);
lean_dec(v___x_2587_);
lean_dec_ref(v___f_2585_);
v___x_3023_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__58_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__58_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__58_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_3024_ = l_Lean_MessageData_ofConstName(v_declName_2590_, v___x_2602_);
v___x_3025_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3025_, 0, v___x_3023_);
lean_ctor_set(v___x_3025_, 1, v___x_3024_);
v___x_3026_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__60_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__60_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__60_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_3027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3027_, 0, v___x_3025_);
lean_ctor_set(v___x_3027_, 1, v___x_3026_);
v___x_3028_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0___redArg(v___x_3027_, v___y_3014_, v___y_3018_);
v_a_3029_ = lean_ctor_get(v___x_3028_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3031_ = v___x_3028_;
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_a_3029_);
lean_dec(v___x_3028_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v___x_3034_; 
if (v_isShared_3032_ == 0)
{
v___x_3034_ = v___x_3031_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_a_3029_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
return v___x_3034_;
}
}
}
}
v___jp_3037_:
{
if (lean_obj_tag(v___y_3039_) == 0)
{
lean_object* v___x_3044_; 
v___x_3044_ = lean_box(0);
v___y_3014_ = v___y_3042_;
v___y_3015_ = v_since_x3f_3041_;
v___y_3016_ = v___y_3038_;
v___y_3017_ = v___y_3039_;
v___y_3018_ = v___y_3043_;
v___y_3019_ = v___y_3040_;
v_a_3020_ = v___x_3044_;
goto v___jp_3013_;
}
else
{
lean_object* v_val_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
v_val_3045_ = lean_ctor_get(v___y_3039_, 0);
v___x_3046_ = lean_box(0);
lean_inc(v_val_3045_);
v___x_3047_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_val_3045_, v___x_3046_, v___y_3042_, v___y_3043_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_object* v_a_3048_; lean_object* v___x_3049_; 
v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
lean_inc(v_a_3048_);
lean_dec_ref_known(v___x_3047_, 1);
v___x_3049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3049_, 0, v_a_3048_);
v___y_3014_ = v___y_3042_;
v___y_3015_ = v_since_x3f_3041_;
v___y_3016_ = v___y_3038_;
v___y_3017_ = v___y_3039_;
v___y_3018_ = v___y_3043_;
v___y_3019_ = v___y_3040_;
v_a_3020_ = v___x_3049_;
goto v___jp_3013_;
}
else
{
lean_object* v_a_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3057_; 
lean_dec_ref_known(v___y_3039_, 1);
lean_dec(v_since_x3f_3041_);
lean_dec(v___y_3040_);
lean_dec(v___y_3038_);
lean_dec(v_stx_2591_);
lean_dec(v_declName_2590_);
lean_dec_ref(v___x_2588_);
lean_dec(v___x_2587_);
lean_dec_ref(v___f_2585_);
v_a_3050_ = lean_ctor_get(v___x_3047_, 0);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3052_ = v___x_3047_;
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_a_3050_);
lean_dec(v___x_3047_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3055_; 
if (v_isShared_3053_ == 0)
{
v___x_3055_ = v___x_3052_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_a_3050_);
v___x_3055_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
return v___x_3055_;
}
}
}
}
}
v___jp_3058_:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; uint8_t v___x_3067_; 
v___x_3065_ = lean_unsigned_to_nat(4u);
v___x_3066_ = l_Lean_Syntax_getArg(v_stx_2591_, v___x_3065_);
v___x_3067_ = l_Lean_Syntax_isNone(v___x_3066_);
if (v___x_3067_ == 0)
{
lean_object* v___x_3068_; uint8_t v___x_3069_; 
v___x_3068_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_3066_);
v___x_3069_ = l_Lean_Syntax_matchesNull(v___x_3066_, v___x_3068_);
if (v___x_3069_ == 0)
{
lean_object* v___x_3070_; lean_object* v___x_3071_; 
lean_dec(v___x_3066_);
lean_dec(v_typeChanged_x3f_3062_);
lean_dec(v___y_3061_);
lean_dec(v___y_3060_);
lean_dec(v_stx_2591_);
lean_dec(v_declName_2590_);
lean_dec_ref(v___x_2588_);
lean_dec(v___x_2587_);
lean_dec_ref(v___f_2585_);
v___x_3070_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_3071_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0___redArg(v___x_3070_, v___y_3063_, v___y_3064_);
return v___x_3071_;
}
else
{
lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___x_3072_ = l_Lean_Syntax_getArg(v___x_3066_, v___y_3059_);
lean_dec(v___x_3066_);
v___x_3073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3073_, 0, v___x_3072_);
v___y_3038_ = v___y_3060_;
v___y_3039_ = v___y_3061_;
v___y_3040_ = v_typeChanged_x3f_3062_;
v_since_x3f_3041_ = v___x_3073_;
v___y_3042_ = v___y_3063_;
v___y_3043_ = v___y_3064_;
goto v___jp_3037_;
}
}
else
{
lean_object* v___x_3074_; 
lean_dec(v___x_3066_);
v___x_3074_ = lean_box(0);
v___y_3038_ = v___y_3060_;
v___y_3039_ = v___y_3061_;
v___y_3040_ = v_typeChanged_x3f_3062_;
v_since_x3f_3041_ = v___x_3074_;
v___y_3042_ = v___y_3063_;
v___y_3043_ = v___y_3064_;
goto v___jp_3037_;
}
}
v___jp_3075_:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; uint8_t v___x_3082_; 
v___x_3080_ = lean_unsigned_to_nat(3u);
v___x_3081_ = l_Lean_Syntax_getArg(v_stx_2591_, v___x_3080_);
v___x_3082_ = l_Lean_Syntax_isNone(v___x_3081_);
if (v___x_3082_ == 0)
{
uint8_t v___x_3083_; 
lean_inc(v___x_3081_);
v___x_3083_ = l_Lean_Syntax_matchesNull(v___x_3081_, v___x_2725_);
if (v___x_3083_ == 0)
{
lean_object* v___x_3084_; lean_object* v___x_3085_; 
lean_dec(v___x_3081_);
lean_dec(v_text_x3f_3077_);
lean_dec(v___y_3076_);
lean_dec(v_stx_2591_);
lean_dec(v_declName_2590_);
lean_dec_ref(v___x_2588_);
lean_dec(v___x_2587_);
lean_dec_ref(v___f_2585_);
v___x_3084_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_3085_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0___redArg(v___x_3084_, v___y_3078_, v___y_3079_);
return v___x_3085_;
}
else
{
lean_object* v___x_3086_; lean_object* v___x_3087_; 
v___x_3086_ = l_Lean_Syntax_getArg(v___x_3081_, v___x_2724_);
lean_dec(v___x_3081_);
v___x_3087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3087_, 0, v___x_3086_);
v___y_3059_ = v___x_3080_;
v___y_3060_ = v_text_x3f_3077_;
v___y_3061_ = v___y_3076_;
v_typeChanged_x3f_3062_ = v___x_3087_;
v___y_3063_ = v___y_3078_;
v___y_3064_ = v___y_3079_;
goto v___jp_3058_;
}
}
else
{
lean_object* v___x_3088_; 
lean_dec(v___x_3081_);
v___x_3088_ = lean_box(0);
v___y_3059_ = v___x_3080_;
v___y_3060_ = v_text_x3f_3077_;
v___y_3061_ = v___y_3076_;
v_typeChanged_x3f_3062_ = v___x_3088_;
v___y_3063_ = v___y_3078_;
v___y_3064_ = v___y_3079_;
goto v___jp_3058_;
}
}
v___jp_3089_:
{
lean_object* v___x_3093_; lean_object* v___x_3094_; uint8_t v___x_3095_; 
v___x_3093_ = lean_unsigned_to_nat(2u);
v___x_3094_ = l_Lean_Syntax_getArg(v_stx_2591_, v___x_3093_);
v___x_3095_ = l_Lean_Syntax_isNone(v___x_3094_);
if (v___x_3095_ == 0)
{
uint8_t v___x_3096_; 
lean_inc(v___x_3094_);
v___x_3096_ = l_Lean_Syntax_matchesNull(v___x_3094_, v___x_2725_);
if (v___x_3096_ == 0)
{
lean_object* v___x_3097_; lean_object* v___x_3098_; 
lean_dec(v___x_3094_);
lean_dec(v_id_x3f_3090_);
lean_dec(v_stx_2591_);
lean_dec(v_declName_2590_);
lean_dec_ref(v___x_2588_);
lean_dec(v___x_2587_);
lean_dec_ref(v___f_2585_);
v___x_3097_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_3098_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0___redArg(v___x_3097_, v___y_3091_, v___y_3092_);
return v___x_3098_;
}
else
{
lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3099_ = l_Lean_Syntax_getArg(v___x_3094_, v___x_2724_);
lean_dec(v___x_3094_);
v___x_3100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3100_, 0, v___x_3099_);
v___y_3076_ = v_id_x3f_3090_;
v_text_x3f_3077_ = v___x_3100_;
v___y_3078_ = v___y_3091_;
v___y_3079_ = v___y_3092_;
goto v___jp_3075_;
}
}
else
{
lean_object* v___x_3101_; 
lean_dec(v___x_3094_);
v___x_3101_ = lean_box(0);
v___y_3076_ = v_id_x3f_3090_;
v_text_x3f_3077_ = v___x_3101_;
v___y_3078_ = v___y_3091_;
v___y_3079_ = v___y_3092_;
goto v___jp_3075_;
}
}
}
v___jp_2595_:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; 
v___x_2599_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2599_, 0, v___y_2596_);
lean_ctor_set(v___x_2599_, 1, v___y_2598_);
lean_ctor_set(v___x_2599_, 2, v___y_2597_);
v___x_2600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2599_);
return v___x_2600_;
}
v___jp_2603_:
{
if (lean_obj_tag(v___y_2605_) == 0)
{
if (v___x_2602_ == 0)
{
lean_dec(v_stx_2591_);
v___y_2596_ = v___y_2604_;
v___y_2597_ = v___y_2605_;
v___y_2598_ = v___y_2606_;
goto v___jp_2595_;
}
else
{
lean_object* v___x_2609_; 
v___x_2609_ = l_Lean_Linter_mkSinceHint(v_stx_2591_, v___y_2607_, v___y_2608_);
if (lean_obj_tag(v___x_2609_) == 0)
{
lean_object* v_a_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; 
v_a_2610_ = lean_ctor_get(v___x_2609_, 0);
lean_inc(v_a_2610_);
lean_dec_ref_known(v___x_2609_, 1);
v___x_2611_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__1_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__1_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__1_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2611_);
lean_ctor_set(v___x_2612_, 1, v_a_2610_);
v___x_2613_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1(v___x_2612_, v___y_2607_, v___y_2608_);
if (lean_obj_tag(v___x_2613_) == 0)
{
lean_dec_ref_known(v___x_2613_, 1);
v___y_2596_ = v___y_2604_;
v___y_2597_ = v___y_2605_;
v___y_2598_ = v___y_2606_;
goto v___jp_2595_;
}
else
{
lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2621_; 
lean_dec(v___y_2606_);
lean_dec(v___y_2604_);
v_a_2614_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2616_ = v___x_2613_;
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2613_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2619_; 
if (v_isShared_2617_ == 0)
{
v___x_2619_ = v___x_2616_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_a_2614_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
}
else
{
lean_object* v_a_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2629_; 
lean_dec(v___y_2606_);
lean_dec(v___y_2604_);
v_a_2622_ = lean_ctor_get(v___x_2609_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2609_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2624_ = v___x_2609_;
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_a_2622_);
lean_dec(v___x_2609_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2627_; 
if (v_isShared_2625_ == 0)
{
v___x_2627_ = v___x_2624_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v_a_2622_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
}
}
}
else
{
lean_dec(v_stx_2591_);
v___y_2596_ = v___y_2604_;
v___y_2597_ = v___y_2605_;
v___y_2598_ = v___y_2606_;
goto v___jp_2595_;
}
}
v___jp_2630_:
{
if (lean_obj_tag(v___y_2632_) == 0)
{
if (v___x_2602_ == 0)
{
v___y_2604_ = v___y_2631_;
v___y_2605_ = v___y_2636_;
v___y_2606_ = v___y_2635_;
v___y_2607_ = v___y_2634_;
v___y_2608_ = v___y_2633_;
goto v___jp_2603_;
}
else
{
if (lean_obj_tag(v___y_2635_) == 0)
{
if (v___x_2602_ == 0)
{
v___y_2604_ = v___y_2631_;
v___y_2605_ = v___y_2636_;
v___y_2606_ = v___y_2635_;
v___y_2607_ = v___y_2634_;
v___y_2608_ = v___y_2633_;
goto v___jp_2603_;
}
else
{
lean_object* v___x_2637_; lean_object* v___x_2638_; 
v___x_2637_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__4_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__4_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__4_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2638_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1(v___x_2637_, v___y_2634_, v___y_2633_);
if (lean_obj_tag(v___x_2638_) == 0)
{
lean_dec_ref_known(v___x_2638_, 1);
v___y_2604_ = v___y_2631_;
v___y_2605_ = v___y_2636_;
v___y_2606_ = v___y_2635_;
v___y_2607_ = v___y_2634_;
v___y_2608_ = v___y_2633_;
goto v___jp_2603_;
}
else
{
lean_object* v_a_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2646_; 
lean_dec(v___y_2636_);
lean_dec(v___y_2631_);
lean_dec(v_stx_2591_);
v_a_2639_ = lean_ctor_get(v___x_2638_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2638_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2641_ = v___x_2638_;
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_a_2639_);
lean_dec(v___x_2638_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2644_; 
if (v_isShared_2642_ == 0)
{
v___x_2644_ = v___x_2641_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v_a_2639_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
}
}
}
else
{
v___y_2604_ = v___y_2631_;
v___y_2605_ = v___y_2636_;
v___y_2606_ = v___y_2635_;
v___y_2607_ = v___y_2634_;
v___y_2608_ = v___y_2633_;
goto v___jp_2603_;
}
}
}
else
{
lean_dec_ref_known(v___y_2632_, 1);
v___y_2604_ = v___y_2631_;
v___y_2605_ = v___y_2636_;
v___y_2606_ = v___y_2635_;
v___y_2607_ = v___y_2634_;
v___y_2608_ = v___y_2633_;
goto v___jp_2603_;
}
}
v___jp_2647_:
{
if (lean_obj_tag(v___y_2649_) == 0)
{
lean_object* v___x_2654_; 
v___x_2654_ = lean_box(0);
v___y_2631_ = v___y_2648_;
v___y_2632_ = v___y_2650_;
v___y_2633_ = v___y_2651_;
v___y_2634_ = v___y_2652_;
v___y_2635_ = v___y_2653_;
v___y_2636_ = v___x_2654_;
goto v___jp_2630_;
}
else
{
lean_object* v_val_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2663_; 
v_val_2655_ = lean_ctor_get(v___y_2649_, 0);
v_isSharedCheck_2663_ = !lean_is_exclusive(v___y_2649_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2657_ = v___y_2649_;
v_isShared_2658_ = v_isSharedCheck_2663_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_val_2655_);
lean_dec(v___y_2649_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2663_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v___x_2659_; lean_object* v___x_2661_; 
v___x_2659_ = l_Lean_TSyntax_getString(v_val_2655_);
lean_dec(v_val_2655_);
if (v_isShared_2658_ == 0)
{
lean_ctor_set(v___x_2657_, 0, v___x_2659_);
v___x_2661_ = v___x_2657_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v___x_2659_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
v___y_2631_ = v___y_2648_;
v___y_2632_ = v___y_2650_;
v___y_2633_ = v___y_2651_;
v___y_2634_ = v___y_2652_;
v___y_2635_ = v___y_2653_;
v___y_2636_ = v___x_2661_;
goto v___jp_2630_;
}
}
}
}
v___jp_2664_:
{
if (lean_obj_tag(v___y_2667_) == 0)
{
lean_object* v___x_2671_; 
v___x_2671_ = lean_box(0);
v___y_2648_ = v___y_2665_;
v___y_2649_ = v___y_2666_;
v___y_2650_ = v___y_2668_;
v___y_2651_ = v___y_2670_;
v___y_2652_ = v___y_2669_;
v___y_2653_ = v___x_2671_;
goto v___jp_2647_;
}
else
{
lean_object* v_val_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2680_; 
v_val_2672_ = lean_ctor_get(v___y_2667_, 0);
v_isSharedCheck_2680_ = !lean_is_exclusive(v___y_2667_);
if (v_isSharedCheck_2680_ == 0)
{
v___x_2674_ = v___y_2667_;
v_isShared_2675_ = v_isSharedCheck_2680_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_val_2672_);
lean_dec(v___y_2667_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2680_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v___x_2676_; lean_object* v___x_2678_; 
v___x_2676_ = l_Lean_TSyntax_getString(v_val_2672_);
lean_dec(v_val_2672_);
if (v_isShared_2675_ == 0)
{
lean_ctor_set(v___x_2674_, 0, v___x_2676_);
v___x_2678_ = v___x_2674_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v___x_2676_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
v___y_2648_ = v___y_2665_;
v___y_2649_ = v___y_2666_;
v___y_2650_ = v___y_2668_;
v___y_2651_ = v___y_2670_;
v___y_2652_ = v___y_2669_;
v___y_2653_ = v___x_2678_;
goto v___jp_2647_;
}
}
}
}
v___jp_2681_:
{
lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2691_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2692_ = l_Lean_ConstantInfo_type(v___y_2686_);
lean_dec_ref(v___y_2686_);
v___x_2693_ = l_Lean_indentExpr(v___x_2692_);
v___x_2694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2694_, 0, v___x_2691_);
lean_ctor_set(v___x_2694_, 1, v___x_2693_);
v___x_2695_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2694_);
lean_ctor_set(v___x_2696_, 1, v___x_2695_);
v___x_2697_ = l_Lean_ConstantInfo_type(v___y_2687_);
lean_dec_ref(v___y_2687_);
v___x_2698_ = l_Lean_indentExpr(v___x_2697_);
v___x_2699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2699_, 0, v___x_2696_);
lean_ctor_set(v___x_2699_, 1, v___x_2698_);
v___x_2700_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__10_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__10_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__10_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2699_);
lean_ctor_set(v___x_2701_, 1, v___x_2700_);
v___x_2702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2701_);
lean_ctor_set(v___x_2702_, 1, v_hint_2688_);
v___x_2703_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1(v___x_2702_, v___y_2689_, v___y_2690_);
if (lean_obj_tag(v___x_2703_) == 0)
{
lean_dec_ref_known(v___x_2703_, 1);
v___y_2665_ = v___y_2682_;
v___y_2666_ = v___y_2683_;
v___y_2667_ = v___y_2684_;
v___y_2668_ = v___y_2685_;
v___y_2669_ = v___y_2689_;
v___y_2670_ = v___y_2690_;
goto v___jp_2664_;
}
else
{
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2711_; 
lean_dec(v___y_2685_);
lean_dec(v___y_2684_);
lean_dec(v___y_2683_);
lean_dec(v___y_2682_);
lean_dec(v_stx_2591_);
v_a_2704_ = lean_ctor_get(v___x_2703_, 0);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2706_ = v___x_2703_;
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2703_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2709_; 
if (v_isShared_2707_ == 0)
{
v___x_2709_ = v___x_2706_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_a_2704_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
}
}
v___jp_2712_:
{
lean_object* v___x_2721_; 
v___x_2721_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__14_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__14_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__14_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___y_2682_ = v___y_2713_;
v___y_2683_ = v___y_2715_;
v___y_2684_ = v___y_2717_;
v___y_2685_ = v___y_2718_;
v___y_2686_ = v___y_2719_;
v___y_2687_ = v___y_2720_;
v_hint_2688_ = v___x_2721_;
v___y_2689_ = v___y_2716_;
v___y_2690_ = v___y_2714_;
goto v___jp_2681_;
}
}
}
LEAN_EXPORT void l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2583_ = stack[0].m_obj;
lean_object* v___x_2584_ = stack[1].m_obj;
lean_object* v___f_2585_ = stack[2].m_obj;
uint8_t v___x_2586_ = stack[3].m_num;
lean_object* v___x_2587_ = stack[4].m_obj;
lean_object* v___x_2588_ = stack[5].m_obj;
lean_object* v_a_2589_ = stack[6].m_obj;
lean_object* v_declName_2590_ = stack[7].m_obj;
lean_object* v_stx_2591_ = stack[8].m_obj;
lean_object* v___y_2592_ = stack[9].m_obj;
lean_object* v___y_2593_ = stack[10].m_obj;
lean_object* v_res_3110_;
v_res_3110_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(v___x_2583_, v___x_2584_, v___f_2585_, v___x_2586_, v___x_2587_, v___x_2588_, v_a_2589_, v_declName_2590_, v_stx_2591_, v___y_2592_, v___y_2593_);
stack->m_obj
 = v_res_3110_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2____boxed(lean_object* v___x_3111_, lean_object* v___x_3112_, lean_object* v___f_3113_, lean_object* v___x_3114_, lean_object* v___x_3115_, lean_object* v___x_3116_, lean_object* v_a_3117_, lean_object* v_declName_3118_, lean_object* v_stx_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_){
_start:
{
uint8_t v___x_48398__boxed_3123_; lean_object* v_res_3124_; 
v___x_48398__boxed_3123_ = lean_unbox(v___x_3114_);
v_res_3124_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(v___x_3111_, v___x_3112_, v___f_3113_, v___x_48398__boxed_3123_, v___x_3115_, v___x_3116_, v_a_3117_, v_declName_3118_, v_stx_3119_, v___y_3120_, v___y_3121_);
lean_dec(v___y_3121_);
lean_dec_ref(v___y_3120_);
lean_dec_ref(v_a_3117_);
return v_res_3124_;
}
}
lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3142_; lean_object* v___f_3143_; lean_object* v___f_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; uint8_t v___x_3149_; lean_object* v___x_3150_; 
v___f_3142_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___f_3143_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___f_3144_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_3145_ = lean_box(1);
v___x_3146_ = ((lean_object*)(l_Lean_Linter_instInhabitedDeprecationEntry_default));
v___x_3147_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_));
v___x_3148_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_3149_ = 0;
v___x_3150_ = l_Lean_registerParametricAttributeExt___redArg(v___x_3148_, v___x_3149_, v___f_3142_, v___x_3149_);
if (lean_obj_tag(v___x_3150_) == 0)
{
lean_object* v_a_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___f_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; 
v_a_3151_ = lean_ctor_get(v___x_3150_, 0);
lean_inc_n(v_a_3151_, 2);
lean_dec_ref_known(v___x_3150_, 1);
v___x_3152_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_));
v___x_3153_ = lean_box(v___x_3149_);
v___f_3154_ = lean_alloc_closure((void*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2____boxed), 12, 7);
lean_closure_set(v___f_3154_, 0, v___x_3147_);
lean_closure_set(v___f_3154_, 1, v___x_3152_);
lean_closure_set(v___f_3154_, 2, v___f_3143_);
lean_closure_set(v___f_3154_, 3, v___x_3153_);
lean_closure_set(v___f_3154_, 4, v___x_3145_);
lean_closure_set(v___f_3154_, 5, v___x_3146_);
lean_closure_set(v___f_3154_, 6, v_a_3151_);
v___x_3155_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_3156_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3156_, 0, v___x_3155_);
lean_ctor_set(v___x_3156_, 1, v___f_3154_);
lean_ctor_set(v___x_3156_, 2, v___f_3144_);
lean_ctor_set(v___x_3156_, 3, v___f_3142_);
lean_ctor_set_uint8(v___x_3156_, sizeof(void*)*4, v___x_3149_);
v___x_3157_ = l_Lean_registerParametricAttributeForExt___redArg(v___x_3156_, v_a_3151_);
return v___x_3157_;
}
else
{
lean_object* v_a_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3165_; 
v_a_3158_ = lean_ctor_get(v___x_3150_, 0);
v_isSharedCheck_3165_ = !lean_is_exclusive(v___x_3150_);
if (v_isSharedCheck_3165_ == 0)
{
v___x_3160_ = v___x_3150_;
v_isShared_3161_ = v_isSharedCheck_3165_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_a_3158_);
lean_dec(v___x_3150_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3165_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v___x_3163_; 
if (v_isShared_3161_ == 0)
{
v___x_3163_ = v___x_3160_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v_a_3158_);
v___x_3163_ = v_reuseFailAlloc_3164_;
goto v_reusejp_3162_;
}
v_reusejp_3162_:
{
return v___x_3163_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3166_;
v_res_3166_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_();
stack->m_obj
 = v_res_3166_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2____boxed(lean_object* v_a_3167_){
_start:
{
lean_object* v_res_3168_; 
v_res_3168_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_();
return v_res_3168_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_3169_, lean_object* v_msg_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_){
_start:
{
lean_object* v___x_3174_; 
v___x_3174_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0___redArg(v_msg_3170_, v___y_3171_, v___y_3172_);
return v___x_3174_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3170_ = stack[1].m_obj;
lean_object* v___y_3171_ = stack[2].m_obj;
lean_object* v___y_3172_ = stack[3].m_obj;
lean_object* v_res_3175_;
v_res_3175_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0(lean_box(0), v_msg_3170_, v___y_3171_, v___y_3172_);
stack->m_obj
 = v_res_3175_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_3176_, lean_object* v_msg_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_){
_start:
{
lean_object* v_res_3181_; 
v_res_3181_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0(v_00_u03b1_3176_, v_msg_3177_, v___y_3178_, v___y_3179_);
lean_dec(v___y_3179_);
lean_dec_ref(v___y_3178_);
return v_res_3181_;
}
}
lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3_spec__8(lean_object* v_o_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_){
_start:
{
lean_object* v___x_3186_; 
v___x_3186_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3_spec__8___redArg(v_o_3182_, v___y_3184_);
return v___x_3186_;
}
}
LEAN_EXPORT void l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_3182_ = stack[0].m_obj;
lean_object* v___y_3183_ = stack[1].m_obj;
lean_object* v___y_3184_ = stack[2].m_obj;
lean_object* v_res_3187_;
v_res_3187_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3_spec__8(v_o_3182_, v___y_3183_, v___y_3184_);
stack->m_obj
 = v_res_3187_;
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3_spec__8___boxed(lean_object* v_o_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_){
_start:
{
lean_object* v_res_3192_; 
v_res_3192_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3_spec__8(v_o_3188_, v___y_3189_, v___y_3190_);
lean_dec(v___y_3190_);
lean_dec_ref(v___y_3189_);
return v_res_3192_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6(lean_object* v_00_u03b2_3193_, lean_object* v_m_3194_, lean_object* v_a_3195_){
_start:
{
lean_object* v___x_3196_; 
v___x_3196_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6___redArg(v_m_3194_, v_a_3195_);
return v___x_3196_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6___boxed(lean_object* v_00_u03b2_3197_, lean_object* v_m_3198_, lean_object* v_a_3199_){
_start:
{
lean_object* v_res_3200_; 
v_res_3200_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6(v_00_u03b2_3197_, v_m_3198_, v_a_3199_);
lean_dec(v_a_3199_);
lean_dec_ref(v_m_3198_);
return v_res_3200_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8(lean_object* v_00_u03b2_3201_, lean_object* v_x_3202_, lean_object* v_x_3203_){
_start:
{
uint8_t v___x_3204_; 
v___x_3204_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg(v_x_3202_, v_x_3203_);
return v___x_3204_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3202_ = stack[1].m_obj;
lean_object* v_x_3203_ = stack[2].m_obj;
uint8_t v_res_3205_;
v_res_3205_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8(lean_box(0), v_x_3202_, v_x_3203_);
stack->m_num = v_res_3205_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_3206_, lean_object* v_x_3207_, lean_object* v_x_3208_){
_start:
{
uint8_t v_res_3209_; lean_object* v_r_3210_; 
v_res_3209_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8(v_00_u03b2_3206_, v_x_3207_, v_x_3208_);
lean_dec_ref(v_x_3208_);
lean_dec_ref(v_x_3207_);
v_r_3210_ = lean_box(v_res_3209_);
return v_r_3210_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6_spec__12(lean_object* v_00_u03b2_3211_, lean_object* v_a_3212_, lean_object* v_x_3213_){
_start:
{
lean_object* v___x_3214_; 
v___x_3214_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg(v_a_3212_, v_x_3213_);
return v___x_3214_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6_spec__12___boxed(lean_object* v_00_u03b2_3215_, lean_object* v_a_3216_, lean_object* v_x_3217_){
_start:
{
lean_object* v_res_3218_; 
v_res_3218_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6_spec__12(v_00_u03b2_3215_, v_a_3216_, v_x_3217_);
lean_dec(v_x_3217_);
lean_dec(v_a_3216_);
return v_res_3218_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__17(lean_object* v_00_u03b4_3219_, lean_object* v_t_3220_, lean_object* v_k_3221_){
_start:
{
lean_object* v___x_3222_; 
v___x_3222_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__17___redArg(v_t_3220_, v_k_3221_);
return v___x_3222_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__17___boxed(lean_object* v_00_u03b4_3223_, lean_object* v_t_3224_, lean_object* v_k_3225_){
_start:
{
lean_object* v_res_3226_; 
v_res_3226_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__17(v_00_u03b4_3223_, v_t_3224_, v_k_3225_);
lean_dec(v_k_3225_);
lean_dec(v_t_3224_);
return v_res_3226_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12(lean_object* v_00_u03b2_3227_, lean_object* v_x_3228_, size_t v_x_3229_, lean_object* v_x_3230_){
_start:
{
uint8_t v___x_3231_; 
v___x_3231_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12___redArg(v_x_3228_, v_x_3229_, v_x_3230_);
return v___x_3231_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3228_ = stack[1].m_obj;
size_t v_x_3229_ = stack[2].m_num;
lean_object* v_x_3230_ = stack[3].m_obj;
uint8_t v_res_3232_;
v_res_3232_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12(lean_box(0), v_x_3228_, v_x_3229_, v_x_3230_);
stack->m_num = v_res_3232_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12___boxed(lean_object* v_00_u03b2_3233_, lean_object* v_x_3234_, lean_object* v_x_3235_, lean_object* v_x_3236_){
_start:
{
size_t v_x_50390__boxed_3237_; uint8_t v_res_3238_; lean_object* v_r_3239_; 
v_x_50390__boxed_3237_ = lean_unbox_usize(v_x_3235_);
lean_dec(v_x_3235_);
v_res_3238_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12(v_00_u03b2_3233_, v_x_3234_, v_x_50390__boxed_3237_, v_x_3236_);
lean_dec_ref(v_x_3236_);
lean_dec_ref(v_x_3234_);
v_r_3239_ = lean_box(v_res_3238_);
return v_r_3239_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20(lean_object* v_givenName_3240_, uint8_t v_skipAuxDecl_3241_, lean_object* v_auxDeclToFullName_3242_, lean_object* v___x_3243_, lean_object* v_givenNameView_3244_, lean_object* v_as_3245_, lean_object* v_i_3246_, lean_object* v_a_3247_){
_start:
{
lean_object* v___x_3248_; 
v___x_3248_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg(v_givenName_3240_, v_skipAuxDecl_3241_, v_auxDeclToFullName_3242_, v___x_3243_, v_givenNameView_3244_, v_as_3245_, v_i_3246_);
return v___x_3248_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20_0interp(lean_interpreter_value* stack)
{
lean_object* v_givenName_3240_ = stack[0].m_obj;
uint8_t v_skipAuxDecl_3241_ = stack[1].m_num;
lean_object* v_auxDeclToFullName_3242_ = stack[2].m_obj;
lean_object* v___x_3243_ = stack[3].m_obj;
lean_object* v_givenNameView_3244_ = stack[4].m_obj;
lean_object* v_as_3245_ = stack[5].m_obj;
lean_object* v_i_3246_ = stack[6].m_obj;
lean_object* v_res_3249_;
v_res_3249_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20(v_givenName_3240_, v_skipAuxDecl_3241_, v_auxDeclToFullName_3242_, v___x_3243_, v_givenNameView_3244_, v_as_3245_, v_i_3246_, lean_box(0));
stack->m_obj
 = v_res_3249_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___boxed(lean_object* v_givenName_3250_, lean_object* v_skipAuxDecl_3251_, lean_object* v_auxDeclToFullName_3252_, lean_object* v___x_3253_, lean_object* v_givenNameView_3254_, lean_object* v_as_3255_, lean_object* v_i_3256_, lean_object* v_a_3257_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3258_; lean_object* v_res_3259_; 
v_skipAuxDecl_boxed_3258_ = lean_unbox(v_skipAuxDecl_3251_);
v_res_3259_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20(v_givenName_3250_, v_skipAuxDecl_boxed_3258_, v_auxDeclToFullName_3252_, v___x_3253_, v_givenNameView_3254_, v_as_3255_, v_i_3256_, v_a_3257_);
lean_dec_ref(v_as_3255_);
lean_dec(v_auxDeclToFullName_3252_);
lean_dec(v_givenName_3250_);
return v_res_3259_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23(lean_object* v_localDecl_x3f_3260_, lean_object* v_givenName_3261_, lean_object* v_as_3262_, lean_object* v_i_3263_, lean_object* v_a_3264_){
_start:
{
lean_object* v___x_3265_; 
v___x_3265_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___redArg(v_localDecl_x3f_3260_, v_givenName_3261_, v_as_3262_, v_i_3263_);
return v___x_3265_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___boxed(lean_object* v_localDecl_x3f_3266_, lean_object* v_givenName_3267_, lean_object* v_as_3268_, lean_object* v_i_3269_, lean_object* v_a_3270_){
_start:
{
lean_object* v_res_3271_; 
v_res_3271_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23(v_localDecl_x3f_3266_, v_givenName_3267_, v_as_3268_, v_i_3269_, v_a_3270_);
lean_dec_ref(v_as_3268_);
lean_dec(v_givenName_3267_);
lean_dec(v_localDecl_x3f_3266_);
return v_res_3271_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30(lean_object* v_n_u2080_3272_, lean_object* v_filter_3273_, lean_object* v_view_x3f_3274_, lean_object* v_as_3275_, lean_object* v_as_x27_3276_, lean_object* v_b_3277_, lean_object* v_a_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_){
_start:
{
lean_object* v___x_3284_; 
v___x_3284_ = l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30___redArg(v_n_u2080_3272_, v_filter_3273_, v_view_x3f_3274_, v_as_x27_3276_, v_b_3277_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_);
return v___x_3284_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_u2080_3272_ = stack[0].m_obj;
lean_object* v_filter_3273_ = stack[1].m_obj;
lean_object* v_view_x3f_3274_ = stack[2].m_obj;
lean_object* v_as_3275_ = stack[3].m_obj;
lean_object* v_as_x27_3276_ = stack[4].m_obj;
lean_object* v_b_3277_ = stack[5].m_obj;
lean_object* v___y_3279_ = stack[7].m_obj;
lean_object* v___y_3280_ = stack[8].m_obj;
lean_object* v___y_3281_ = stack[9].m_obj;
lean_object* v___y_3282_ = stack[10].m_obj;
lean_object* v_res_3285_;
v_res_3285_ = l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30(v_n_u2080_3272_, v_filter_3273_, v_view_x3f_3274_, v_as_3275_, v_as_x27_3276_, v_b_3277_, lean_box(0), v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_);
stack->m_obj
 = v_res_3285_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30___boxed(lean_object* v_n_u2080_3286_, lean_object* v_filter_3287_, lean_object* v_view_x3f_3288_, lean_object* v_as_3289_, lean_object* v_as_x27_3290_, lean_object* v_b_3291_, lean_object* v_a_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_){
_start:
{
lean_object* v_res_3298_; 
v_res_3298_ = l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30(v_n_u2080_3286_, v_filter_3287_, v_view_x3f_3288_, v_as_3289_, v_as_x27_3290_, v_b_3291_, v_a_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3295_);
lean_dec(v___y_3294_);
lean_dec_ref(v___y_3293_);
lean_dec(v_as_x27_3290_);
lean_dec(v_as_3289_);
lean_dec(v_n_u2080_3286_);
return v_res_3298_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17(lean_object* v_00_u03b2_3299_, lean_object* v_keys_3300_, lean_object* v_vals_3301_, lean_object* v_heq_3302_, lean_object* v_i_3303_, lean_object* v_k_3304_){
_start:
{
uint8_t v___x_3305_; 
v___x_3305_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17___redArg(v_keys_3300_, v_i_3303_, v_k_3304_);
return v___x_3305_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_3300_ = stack[1].m_obj;
lean_object* v_vals_3301_ = stack[2].m_obj;
lean_object* v_i_3303_ = stack[4].m_obj;
lean_object* v_k_3304_ = stack[5].m_obj;
uint8_t v_res_3306_;
v_res_3306_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17(lean_box(0), v_keys_3300_, v_vals_3301_, lean_box(0), v_i_3303_, v_k_3304_);
stack->m_num = v_res_3306_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17___boxed(lean_object* v_00_u03b2_3307_, lean_object* v_keys_3308_, lean_object* v_vals_3309_, lean_object* v_heq_3310_, lean_object* v_i_3311_, lean_object* v_k_3312_){
_start:
{
uint8_t v_res_3313_; lean_object* v_r_3314_; 
v_res_3313_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17(v_00_u03b2_3307_, v_keys_3308_, v_vals_3309_, v_heq_3310_, v_i_3311_, v_k_3312_);
lean_dec_ref(v_k_3312_);
lean_dec_ref(v_vals_3309_);
lean_dec_ref(v_keys_3308_);
v_r_3314_ = lean_box(v_res_3313_);
return v_r_3314_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24(lean_object* v_givenName_3315_, uint8_t v_skipAuxDecl_3316_, lean_object* v_auxDeclToFullName_3317_, lean_object* v___x_3318_, lean_object* v_givenNameView_3319_, lean_object* v_as_3320_, lean_object* v_i_3321_, lean_object* v_a_3322_){
_start:
{
lean_object* v___x_3323_; 
v___x_3323_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24___redArg(v_givenName_3315_, v_skipAuxDecl_3316_, v_auxDeclToFullName_3317_, v___x_3318_, v_givenNameView_3319_, v_as_3320_, v_i_3321_);
return v___x_3323_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24_0interp(lean_interpreter_value* stack)
{
lean_object* v_givenName_3315_ = stack[0].m_obj;
uint8_t v_skipAuxDecl_3316_ = stack[1].m_num;
lean_object* v_auxDeclToFullName_3317_ = stack[2].m_obj;
lean_object* v___x_3318_ = stack[3].m_obj;
lean_object* v_givenNameView_3319_ = stack[4].m_obj;
lean_object* v_as_3320_ = stack[5].m_obj;
lean_object* v_i_3321_ = stack[6].m_obj;
lean_object* v_res_3324_;
v_res_3324_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24(v_givenName_3315_, v_skipAuxDecl_3316_, v_auxDeclToFullName_3317_, v___x_3318_, v_givenNameView_3319_, v_as_3320_, v_i_3321_, lean_box(0));
stack->m_obj
 = v_res_3324_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24___boxed(lean_object* v_givenName_3325_, lean_object* v_skipAuxDecl_3326_, lean_object* v_auxDeclToFullName_3327_, lean_object* v___x_3328_, lean_object* v_givenNameView_3329_, lean_object* v_as_3330_, lean_object* v_i_3331_, lean_object* v_a_3332_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3333_; lean_object* v_res_3334_; 
v_skipAuxDecl_boxed_3333_ = lean_unbox(v_skipAuxDecl_3326_);
v_res_3334_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24(v_givenName_3325_, v_skipAuxDecl_boxed_3333_, v_auxDeclToFullName_3327_, v___x_3328_, v_givenNameView_3329_, v_as_3330_, v_i_3331_, v_a_3332_);
lean_dec_ref(v_as_3330_);
lean_dec(v_auxDeclToFullName_3327_);
lean_dec(v_givenName_3325_);
return v_res_3334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28(lean_object* v_localDecl_x3f_3335_, lean_object* v_givenName_3336_, lean_object* v_as_3337_, lean_object* v_i_3338_, lean_object* v_a_3339_){
_start:
{
lean_object* v___x_3340_; 
v___x_3340_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28___redArg(v_localDecl_x3f_3335_, v_givenName_3336_, v_as_3337_, v_i_3338_);
return v___x_3340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28___boxed(lean_object* v_localDecl_x3f_3341_, lean_object* v_givenName_3342_, lean_object* v_as_3343_, lean_object* v_i_3344_, lean_object* v_a_3345_){
_start:
{
lean_object* v_res_3346_; 
v_res_3346_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28(v_localDecl_x3f_3341_, v_givenName_3342_, v_as_3343_, v_i_3344_, v_a_3345_);
lean_dec_ref(v_as_3343_);
lean_dec(v_givenName_3342_);
lean_dec(v_localDecl_x3f_3341_);
return v_res_3346_;
}
}
lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37(lean_object* v_opt_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_){
_start:
{
lean_object* v___x_3353_; 
v___x_3353_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37___redArg(v_opt_3347_, v___y_3350_);
return v___x_3353_;
}
}
LEAN_EXPORT void l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37_0interp(lean_interpreter_value* stack)
{
lean_object* v_opt_3347_ = stack[0].m_obj;
lean_object* v___y_3348_ = stack[1].m_obj;
lean_object* v___y_3349_ = stack[2].m_obj;
lean_object* v___y_3350_ = stack[3].m_obj;
lean_object* v___y_3351_ = stack[4].m_obj;
lean_object* v_res_3354_;
v_res_3354_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37(v_opt_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
stack->m_obj
 = v_res_3354_;
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37___boxed(lean_object* v_opt_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_){
_start:
{
lean_object* v_res_3361_; 
v_res_3361_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37(v_opt_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_);
lean_dec(v___y_3359_);
lean_dec_ref(v___y_3358_);
lean_dec(v___y_3357_);
lean_dec_ref(v___y_3356_);
lean_dec_ref(v_opt_3355_);
return v_res_3361_;
}
}
lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43(lean_object* v_opt_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_){
_start:
{
lean_object* v___x_3368_; 
v___x_3368_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43___redArg(v_opt_3362_, v___y_3365_);
return v___x_3368_;
}
}
LEAN_EXPORT void l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43_0interp(lean_interpreter_value* stack)
{
lean_object* v_opt_3362_ = stack[0].m_obj;
lean_object* v___y_3363_ = stack[1].m_obj;
lean_object* v___y_3364_ = stack[2].m_obj;
lean_object* v___y_3365_ = stack[3].m_obj;
lean_object* v___y_3366_ = stack[4].m_obj;
lean_object* v_res_3369_;
v_res_3369_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43(v_opt_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_);
stack->m_obj
 = v_res_3369_;
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43___boxed(lean_object* v_opt_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_){
_start:
{
lean_object* v_res_3376_; 
v_res_3376_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43(v_opt_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_);
lean_dec(v___y_3374_);
lean_dec_ref(v___y_3373_);
lean_dec(v___y_3372_);
lean_dec_ref(v___y_3371_);
lean_dec_ref(v_opt_3370_);
return v_res_3376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___redArg___lam__0(lean_object* v_declName_3377_, lean_object* v_entry_3378_, lean_object* v_inst_3379_, lean_object* v_inst_3380_, lean_object* v_inst_3381_, lean_object* v_env_3382_){
_start:
{
lean_object* v___x_3383_; lean_object* v___x_3384_; 
v___x_3383_ = l_Lean_Linter_deprecatedAttr;
v___x_3384_ = l_Lean_ParametricAttribute_setParam___redArg(v___x_3383_, v_env_3382_, v_declName_3377_, v_entry_3378_);
if (lean_obj_tag(v___x_3384_) == 0)
{
lean_object* v_a_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3394_; 
lean_dec_ref(v_inst_3381_);
v_a_3385_ = lean_ctor_get(v___x_3384_, 0);
v_isSharedCheck_3394_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3387_ = v___x_3384_;
v_isShared_3388_ = v_isSharedCheck_3394_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_a_3385_);
lean_dec(v___x_3384_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3394_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
lean_object* v___x_3390_; 
if (v_isShared_3388_ == 0)
{
lean_ctor_set_tag(v___x_3387_, 3);
v___x_3390_ = v___x_3387_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v_a_3385_);
v___x_3390_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
lean_object* v___x_3391_; lean_object* v___x_3392_; 
v___x_3391_ = l_Lean_MessageData_ofFormat(v___x_3390_);
v___x_3392_ = l_Lean_throwError___redArg(v_inst_3379_, v_inst_3380_, v___x_3391_);
return v___x_3392_;
}
}
}
else
{
lean_object* v_a_3395_; lean_object* v___x_3396_; 
lean_dec_ref(v_inst_3380_);
lean_dec_ref(v_inst_3379_);
v_a_3395_ = lean_ctor_get(v___x_3384_, 0);
lean_inc(v_a_3395_);
lean_dec_ref_known(v___x_3384_, 1);
v___x_3396_ = l_Lean_setEnv___redArg(v_inst_3381_, v_a_3395_);
return v___x_3396_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___redArg(lean_object* v_inst_3397_, lean_object* v_inst_3398_, lean_object* v_inst_3399_, lean_object* v_declName_3400_, lean_object* v_entry_3401_){
_start:
{
lean_object* v_toBind_3402_; lean_object* v_getEnv_3403_; lean_object* v___f_3404_; lean_object* v___x_3405_; 
v_toBind_3402_ = lean_ctor_get(v_inst_3397_, 1);
lean_inc(v_toBind_3402_);
v_getEnv_3403_ = lean_ctor_get(v_inst_3398_, 0);
lean_inc(v_getEnv_3403_);
v___f_3404_ = lean_alloc_closure((void*)(l_Lean_Linter_setDeprecated___redArg___lam__0), 6, 5);
lean_closure_set(v___f_3404_, 0, v_declName_3400_);
lean_closure_set(v___f_3404_, 1, v_entry_3401_);
lean_closure_set(v___f_3404_, 2, v_inst_3397_);
lean_closure_set(v___f_3404_, 3, v_inst_3399_);
lean_closure_set(v___f_3404_, 4, v_inst_3398_);
v___x_3405_ = lean_apply_4(v_toBind_3402_, lean_box(0), lean_box(0), v_getEnv_3403_, v___f_3404_);
return v___x_3405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated(lean_object* v_m_3406_, lean_object* v_inst_3407_, lean_object* v_inst_3408_, lean_object* v_inst_3409_, lean_object* v_declName_3410_, lean_object* v_entry_3411_){
_start:
{
lean_object* v___x_3412_; 
v___x_3412_ = l_Lean_Linter_setDeprecated___redArg(v_inst_3407_, v_inst_3408_, v_inst_3409_, v_declName_3410_, v_entry_3411_);
return v___x_3412_;
}
}
uint8_t l_Lean_Linter_isDeprecated(lean_object* v_env_3413_, lean_object* v_declName_3414_){
_start:
{
lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; 
v___x_3415_ = ((lean_object*)(l_Lean_Linter_instInhabitedDeprecationEntry_default));
v___x_3416_ = l_Lean_Linter_deprecatedAttr;
v___x_3417_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_3415_, v___x_3416_, v_env_3413_, v_declName_3414_);
if (lean_obj_tag(v___x_3417_) == 0)
{
uint8_t v___x_3418_; 
v___x_3418_ = 0;
return v___x_3418_;
}
else
{
uint8_t v___x_3419_; 
lean_dec_ref_known(v___x_3417_, 1);
v___x_3419_ = 1;
return v___x_3419_;
}
}
}
LEAN_EXPORT void l_Lean_Linter_isDeprecated_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_3413_ = stack[0].m_obj;
lean_object* v_declName_3414_ = stack[1].m_obj;
uint8_t v_res_3420_;
v_res_3420_ = l_Lean_Linter_isDeprecated(v_env_3413_, v_declName_3414_);
stack->m_num = v_res_3420_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_isDeprecated___boxed(lean_object* v_env_3421_, lean_object* v_declName_3422_){
_start:
{
uint8_t v_res_3423_; lean_object* v_r_3424_; 
v_res_3423_ = l_Lean_Linter_isDeprecated(v_env_3421_, v_declName_3422_);
v_r_3424_ = lean_box(v_res_3423_);
return v_r_3424_;
}
}
uint8_t l_Lean_MessageData_isDeprecationWarning___lam__0(lean_object* v_x_3425_){
_start:
{
lean_object* v___x_3426_; uint8_t v___x_3427_; 
v___x_3426_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_3427_ = lean_name_eq(v_x_3425_, v___x_3426_);
return v___x_3427_;
}
}
LEAN_EXPORT void l_Lean_MessageData_isDeprecationWarning___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3425_ = stack[0].m_obj;
uint8_t v_res_3428_;
v_res_3428_ = l_Lean_MessageData_isDeprecationWarning___lam__0(v_x_3425_);
stack->m_num = v_res_3428_;
}
LEAN_EXPORT lean_object* l_Lean_MessageData_isDeprecationWarning___lam__0___boxed(lean_object* v_x_3429_){
_start:
{
uint8_t v_res_3430_; lean_object* v_r_3431_; 
v_res_3430_ = l_Lean_MessageData_isDeprecationWarning___lam__0(v_x_3429_);
lean_dec(v_x_3429_);
v_r_3431_ = lean_box(v_res_3430_);
return v_r_3431_;
}
}
uint8_t l_Lean_MessageData_isDeprecationWarning(lean_object* v_msg_3433_){
_start:
{
lean_object* v___f_3434_; uint8_t v___x_3435_; 
v___f_3434_ = ((lean_object*)(l_Lean_MessageData_isDeprecationWarning___closed__0));
v___x_3435_ = l_Lean_MessageData_hasTag(v___f_3434_, v_msg_3433_);
return v___x_3435_;
}
}
LEAN_EXPORT void l_Lean_MessageData_isDeprecationWarning_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3433_ = stack[0].m_obj;
uint8_t v_res_3436_;
v_res_3436_ = l_Lean_MessageData_isDeprecationWarning(v_msg_3433_);
stack->m_num = v_res_3436_;
}
LEAN_EXPORT lean_object* l_Lean_MessageData_isDeprecationWarning___boxed(lean_object* v_msg_3437_){
_start:
{
uint8_t v_res_3438_; lean_object* v_r_3439_; 
v_res_3438_ = l_Lean_MessageData_isDeprecationWarning(v_msg_3437_);
v_r_3439_ = lean_box(v_res_3438_);
return v_r_3439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getDeprecatedNewName(lean_object* v_env_3440_, lean_object* v_declName_3441_){
_start:
{
lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; 
v___x_3442_ = ((lean_object*)(l_Lean_Linter_instInhabitedDeprecationEntry_default));
v___x_3443_ = l_Lean_Linter_deprecatedAttr;
v___x_3444_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_3442_, v___x_3443_, v_env_3440_, v_declName_3441_);
if (lean_obj_tag(v___x_3444_) == 0)
{
lean_object* v___x_3445_; 
v___x_3445_ = lean_box(0);
return v___x_3445_;
}
else
{
lean_object* v_val_3446_; lean_object* v_newName_x3f_3447_; 
v_val_3446_ = lean_ctor_get(v___x_3444_, 0);
lean_inc(v_val_3446_);
lean_dec_ref_known(v___x_3444_, 1);
v_newName_x3f_3447_ = lean_ctor_get(v_val_3446_, 0);
lean_inc(v_newName_x3f_3447_);
lean_dec(v_val_3446_);
return v_newName_x3f_3447_;
}
}
}
uint8_t l_List_beq___at___00List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0(lean_object* v_x_3448_, lean_object* v_x_3449_){
_start:
{
if (lean_obj_tag(v_x_3448_) == 0)
{
if (lean_obj_tag(v_x_3449_) == 0)
{
uint8_t v___x_3450_; 
v___x_3450_ = 1;
return v___x_3450_;
}
else
{
uint8_t v___x_3451_; 
v___x_3451_ = 0;
return v___x_3451_;
}
}
else
{
if (lean_obj_tag(v_x_3449_) == 0)
{
uint8_t v___x_3452_; 
v___x_3452_ = 0;
return v___x_3452_;
}
else
{
lean_object* v_head_3453_; lean_object* v_tail_3454_; lean_object* v_head_3455_; lean_object* v_tail_3456_; uint8_t v___x_3457_; 
v_head_3453_ = lean_ctor_get(v_x_3448_, 0);
v_tail_3454_ = lean_ctor_get(v_x_3448_, 1);
v_head_3455_ = lean_ctor_get(v_x_3449_, 0);
v_tail_3456_ = lean_ctor_get(v_x_3449_, 1);
v___x_3457_ = lean_string_dec_eq(v_head_3453_, v_head_3455_);
if (v___x_3457_ == 0)
{
return v___x_3457_;
}
else
{
v_x_3448_ = v_tail_3454_;
v_x_3449_ = v_tail_3456_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_List_beq___at___00List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3448_ = stack[0].m_obj;
lean_object* v_x_3449_ = stack[1].m_obj;
uint8_t v_res_3459_;
v_res_3459_ = l_List_beq___at___00List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0(v_x_3448_, v_x_3449_);
stack->m_num = v_res_3459_;
}
LEAN_EXPORT lean_object* l_List_beq___at___00List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0___boxed(lean_object* v_x_3460_, lean_object* v_x_3461_){
_start:
{
uint8_t v_res_3462_; lean_object* v_r_3463_; 
v_res_3462_ = l_List_beq___at___00List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0(v_x_3460_, v_x_3461_);
lean_dec(v_x_3461_);
lean_dec(v_x_3460_);
v_r_3463_ = lean_box(v_res_3462_);
return v_r_3463_;
}
}
uint8_t l_List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0(lean_object* v_x_3464_, lean_object* v_x_3465_){
_start:
{
if (lean_obj_tag(v_x_3464_) == 0)
{
if (lean_obj_tag(v_x_3465_) == 0)
{
uint8_t v___x_3466_; 
v___x_3466_ = 1;
return v___x_3466_;
}
else
{
uint8_t v___x_3467_; 
v___x_3467_ = 0;
return v___x_3467_;
}
}
else
{
if (lean_obj_tag(v_x_3465_) == 0)
{
uint8_t v___x_3468_; 
v___x_3468_ = 0;
return v___x_3468_;
}
else
{
lean_object* v_head_3469_; lean_object* v_tail_3470_; lean_object* v_head_3471_; lean_object* v_tail_3472_; uint8_t v___y_3474_; lean_object* v_fst_3476_; lean_object* v_snd_3477_; lean_object* v_fst_3478_; lean_object* v_snd_3479_; uint8_t v___x_3480_; 
v_head_3469_ = lean_ctor_get(v_x_3464_, 0);
v_tail_3470_ = lean_ctor_get(v_x_3464_, 1);
v_head_3471_ = lean_ctor_get(v_x_3465_, 0);
v_tail_3472_ = lean_ctor_get(v_x_3465_, 1);
v_fst_3476_ = lean_ctor_get(v_head_3469_, 0);
v_snd_3477_ = lean_ctor_get(v_head_3469_, 1);
v_fst_3478_ = lean_ctor_get(v_head_3471_, 0);
v_snd_3479_ = lean_ctor_get(v_head_3471_, 1);
v___x_3480_ = lean_name_eq(v_fst_3476_, v_fst_3478_);
if (v___x_3480_ == 0)
{
v___y_3474_ = v___x_3480_;
goto v___jp_3473_;
}
else
{
uint8_t v___x_3481_; 
v___x_3481_ = l_List_beq___at___00List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0(v_snd_3477_, v_snd_3479_);
v___y_3474_ = v___x_3481_;
goto v___jp_3473_;
}
v___jp_3473_:
{
if (v___y_3474_ == 0)
{
return v___y_3474_;
}
else
{
v_x_3464_ = v_tail_3470_;
v_x_3465_ = v_tail_3472_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l_List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3464_ = stack[0].m_obj;
lean_object* v_x_3465_ = stack[1].m_obj;
uint8_t v_res_3482_;
v_res_3482_ = l_List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0(v_x_3464_, v_x_3465_);
stack->m_num = v_res_3482_;
}
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0___boxed(lean_object* v_x_3483_, lean_object* v_x_3484_){
_start:
{
uint8_t v_res_3485_; lean_object* v_r_3486_; 
v_res_3485_ = l_List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0(v_x_3483_, v_x_3484_);
lean_dec(v_x_3484_);
lean_dec(v_x_3483_);
v_r_3486_ = lean_box(v_res_3485_);
return v_r_3486_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__1(void){
_start:
{
lean_object* v___x_3488_; lean_object* v___x_3489_; 
v___x_3488_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__0));
v___x_3489_ = l_Lean_stringToMessageData(v___x_3488_);
return v___x_3489_;
}
}
lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f(lean_object* v_declName_3490_, lean_object* v_newName_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_){
_start:
{
lean_object* v_ref_3497_; 
v_ref_3497_ = lean_ctor_get(v_a_3494_, 2);
if (lean_obj_tag(v_ref_3497_) == 3)
{
lean_object* v_val_3498_; uint8_t v___x_3499_; 
v_val_3498_ = lean_ctor_get(v_ref_3497_, 2);
v___x_3499_ = l_Lean_Name_hasMacroScopes(v_val_3498_);
if (v___x_3499_ == 0)
{
uint8_t v___x_3500_; lean_object* v___x_3578_; 
v___x_3500_ = 1;
v___x_3578_ = l_Lean_Syntax_getRange_x3f(v_ref_3497_, v___x_3500_);
if (lean_obj_tag(v___x_3578_) == 0)
{
if (v___x_3499_ == 0)
{
lean_object* v___x_3579_; lean_object* v___x_3580_; 
lean_dec(v_newName_3491_);
lean_dec(v_declName_3490_);
v___x_3579_ = lean_box(0);
v___x_3580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3580_, 0, v___x_3579_);
return v___x_3580_;
}
else
{
goto v___jp_3501_;
}
}
else
{
lean_dec_ref_known(v___x_3578_, 1);
goto v___jp_3501_;
}
v___jp_3501_:
{
lean_object* v___x_3502_; 
lean_inc(v_val_3498_);
v___x_3502_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26(v_val_3498_, v___x_3500_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_);
if (lean_obj_tag(v___x_3502_) == 0)
{
lean_object* v_a_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3569_; 
v_a_3503_ = lean_ctor_get(v___x_3502_, 0);
v_isSharedCheck_3569_ = !lean_is_exclusive(v___x_3502_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3505_ = v___x_3502_;
v_isShared_3506_ = v_isSharedCheck_3569_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_a_3503_);
lean_dec(v___x_3502_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3569_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; uint8_t v___x_3510_; 
v___x_3507_ = lean_box(0);
v___x_3508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3508_, 0, v_declName_3490_);
lean_ctor_set(v___x_3508_, 1, v___x_3507_);
v___x_3509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3509_, 0, v___x_3508_);
lean_ctor_set(v___x_3509_, 1, v___x_3507_);
v___x_3510_ = l_List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0(v_a_3503_, v___x_3509_);
lean_dec_ref_known(v___x_3509_, 2);
lean_dec(v_a_3503_);
if (v___x_3510_ == 0)
{
lean_object* v___x_3511_; lean_object* v___x_3513_; 
lean_dec(v_newName_3491_);
v___x_3511_ = lean_box(0);
if (v_isShared_3506_ == 0)
{
lean_ctor_set(v___x_3505_, 0, v___x_3511_);
v___x_3513_ = v___x_3505_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v___x_3511_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
}
}
else
{
lean_object* v___x_3515_; 
lean_del_object(v___x_3505_);
v___x_3515_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5(v_newName_3491_, v___x_3499_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_object* v_a_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3560_; 
v_a_3516_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3560_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3518_ = v___x_3515_;
v_isShared_3519_ = v_isSharedCheck_3560_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_a_3516_);
lean_dec(v___x_3515_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3560_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
if (lean_obj_tag(v_a_3516_) == 1)
{
lean_object* v_val_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3555_; 
lean_del_object(v___x_3518_);
v_val_3520_ = lean_ctor_get(v_a_3516_, 0);
v_isSharedCheck_3555_ = !lean_is_exclusive(v_a_3516_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3522_ = v_a_3516_;
v_isShared_3523_ = v_isSharedCheck_3555_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_val_3520_);
lean_dec(v_a_3516_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3555_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; uint8_t v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3535_; 
v___x_3524_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__1, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__1_once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__1);
v___x_3525_ = l_Lean_Name_toString(v_val_3520_, v___x_3500_);
v___x_3526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3526_, 0, v___x_3525_);
v___x_3527_ = lean_box(0);
v___x_3528_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3528_, 0, v___x_3526_);
lean_ctor_set(v___x_3528_, 1, v___x_3527_);
lean_ctor_set(v___x_3528_, 2, v___x_3527_);
lean_ctor_set(v___x_3528_, 3, v___x_3527_);
lean_ctor_set(v___x_3528_, 4, v___x_3527_);
lean_ctor_set(v___x_3528_, 5, v___x_3527_);
v___x_3529_ = 0;
v___x_3530_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3530_, 0, v___x_3528_);
lean_ctor_set(v___x_3530_, 1, v___x_3527_);
lean_ctor_set(v___x_3530_, 2, v___x_3527_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*3, v___x_3529_);
v___x_3531_ = lean_unsigned_to_nat(1u);
v___x_3532_ = lean_mk_empty_array_with_capacity(v___x_3531_);
v___x_3533_ = lean_array_push(v___x_3532_, v___x_3530_);
lean_inc_ref(v_ref_3497_);
if (v_isShared_3523_ == 0)
{
lean_ctor_set(v___x_3522_, 0, v_ref_3497_);
v___x_3535_ = v___x_3522_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v_ref_3497_);
v___x_3535_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3534_;
}
v_reusejp_3534_:
{
lean_object* v___x_3536_; 
v___x_3536_ = l_Lean_MessageData_hint(v___x_3524_, v___x_3533_, v___x_3535_, v___x_3527_, v___x_3499_, v_a_3494_, v_a_3495_);
lean_dec_ref(v___x_3533_);
if (lean_obj_tag(v___x_3536_) == 0)
{
lean_object* v_a_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3545_; 
v_a_3537_ = lean_ctor_get(v___x_3536_, 0);
v_isSharedCheck_3545_ = !lean_is_exclusive(v___x_3536_);
if (v_isSharedCheck_3545_ == 0)
{
v___x_3539_ = v___x_3536_;
v_isShared_3540_ = v_isSharedCheck_3545_;
goto v_resetjp_3538_;
}
else
{
lean_inc(v_a_3537_);
lean_dec(v___x_3536_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3545_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
lean_object* v___x_3541_; lean_object* v___x_3543_; 
v___x_3541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3541_, 0, v_a_3537_);
if (v_isShared_3540_ == 0)
{
lean_ctor_set(v___x_3539_, 0, v___x_3541_);
v___x_3543_ = v___x_3539_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v___x_3541_);
v___x_3543_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
return v___x_3543_;
}
}
}
else
{
lean_object* v_a_3546_; lean_object* v___x_3548_; uint8_t v_isShared_3549_; uint8_t v_isSharedCheck_3553_; 
v_a_3546_ = lean_ctor_get(v___x_3536_, 0);
v_isSharedCheck_3553_ = !lean_is_exclusive(v___x_3536_);
if (v_isSharedCheck_3553_ == 0)
{
v___x_3548_ = v___x_3536_;
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
else
{
lean_inc(v_a_3546_);
lean_dec(v___x_3536_);
v___x_3548_ = lean_box(0);
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
v_resetjp_3547_:
{
lean_object* v___x_3551_; 
if (v_isShared_3549_ == 0)
{
v___x_3551_ = v___x_3548_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v_a_3546_);
v___x_3551_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
return v___x_3551_;
}
}
}
}
}
}
else
{
lean_object* v___x_3556_; lean_object* v___x_3558_; 
lean_dec(v_a_3516_);
v___x_3556_ = lean_box(0);
if (v_isShared_3519_ == 0)
{
lean_ctor_set(v___x_3518_, 0, v___x_3556_);
v___x_3558_ = v___x_3518_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v___x_3556_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
}
}
}
}
else
{
lean_object* v_a_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3568_; 
v_a_3561_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3568_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3563_ = v___x_3515_;
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_a_3561_);
lean_dec(v___x_3515_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v___x_3566_; 
if (v_isShared_3564_ == 0)
{
v___x_3566_ = v___x_3563_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_a_3561_);
v___x_3566_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
return v___x_3566_;
}
}
}
}
}
}
else
{
lean_object* v_a_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3577_; 
lean_dec(v_newName_3491_);
lean_dec(v_declName_3490_);
v_a_3570_ = lean_ctor_get(v___x_3502_, 0);
v_isSharedCheck_3577_ = !lean_is_exclusive(v___x_3502_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3572_ = v___x_3502_;
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_a_3570_);
lean_dec(v___x_3502_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
lean_object* v___x_3575_; 
if (v_isShared_3573_ == 0)
{
v___x_3575_ = v___x_3572_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_a_3570_);
v___x_3575_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
return v___x_3575_;
}
}
}
}
}
else
{
lean_object* v___x_3581_; lean_object* v___x_3582_; 
lean_dec(v_newName_3491_);
lean_dec(v_declName_3490_);
v___x_3581_ = lean_box(0);
v___x_3582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3582_, 0, v___x_3581_);
return v___x_3582_;
}
}
else
{
lean_object* v___x_3583_; lean_object* v___x_3584_; 
lean_dec(v_newName_3491_);
lean_dec(v_declName_3490_);
v___x_3583_ = lean_box(0);
v___x_3584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3584_, 0, v___x_3583_);
return v___x_3584_;
}
}
}
LEAN_EXPORT void l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_3490_ = stack[0].m_obj;
lean_object* v_newName_3491_ = stack[1].m_obj;
lean_object* v_a_3492_ = stack[2].m_obj;
lean_object* v_a_3493_ = stack[3].m_obj;
lean_object* v_a_3494_ = stack[4].m_obj;
lean_object* v_a_3495_ = stack[5].m_obj;
lean_object* v_res_3585_;
v_res_3585_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f(v_declName_3490_, v_newName_3491_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_);
stack->m_obj
 = v_res_3585_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___boxed(lean_object* v_declName_3586_, lean_object* v_newName_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_){
_start:
{
lean_object* v_res_3593_; 
v_res_3593_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f(v_declName_3586_, v_newName_3587_, v_a_3588_, v_a_3589_, v_a_3590_, v_a_3591_);
lean_dec(v_a_3591_);
lean_dec_ref(v_a_3590_);
lean_dec(v_a_3589_);
lean_dec_ref(v_a_3588_);
return v_res_3593_;
}
}
lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(lean_object* v_o_3594_, lean_object* v___y_3595_){
_start:
{
lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v_env_3599_; lean_object* v___x_3600_; lean_object* v_toEnvExtension_3601_; lean_object* v_asyncMode_3602_; lean_object* v___x_3603_; uint8_t v___x_3604_; lean_object* v___x_3605_; lean_object* v_merged_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3614_; 
v___x_3597_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_3598_ = lean_st_ref_get(v___y_3595_);
v_env_3599_ = lean_ctor_get(v___x_3598_, 0);
lean_inc_ref(v_env_3599_);
lean_dec(v___x_3598_);
v___x_3600_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_3601_ = lean_ctor_get(v___x_3600_, 0);
v_asyncMode_3602_ = lean_ctor_get(v_toEnvExtension_3601_, 2);
v___x_3603_ = lean_box(0);
v___x_3604_ = 0;
v___x_3605_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3597_, v___x_3600_, v_env_3599_, v_asyncMode_3602_, v___x_3603_, v___x_3604_);
v_merged_3606_ = lean_ctor_get(v___x_3605_, 0);
v_isSharedCheck_3614_ = !lean_is_exclusive(v___x_3605_);
if (v_isSharedCheck_3614_ == 0)
{
lean_object* v_unused_3615_; 
v_unused_3615_ = lean_ctor_get(v___x_3605_, 1);
lean_dec(v_unused_3615_);
v___x_3608_ = v___x_3605_;
v_isShared_3609_ = v_isSharedCheck_3614_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_merged_3606_);
lean_dec(v___x_3605_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3614_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v___x_3611_; 
if (v_isShared_3609_ == 0)
{
lean_ctor_set(v___x_3608_, 1, v_merged_3606_);
lean_ctor_set(v___x_3608_, 0, v_o_3594_);
v___x_3611_ = v___x_3608_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v_o_3594_);
lean_ctor_set(v_reuseFailAlloc_3613_, 1, v_merged_3606_);
v___x_3611_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
lean_object* v___x_3612_; 
v___x_3612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3612_, 0, v___x_3611_);
return v___x_3612_;
}
}
}
}
LEAN_EXPORT void l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_3594_ = stack[0].m_obj;
lean_object* v___y_3595_ = stack[1].m_obj;
lean_object* v_res_3616_;
v_res_3616_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(v_o_3594_, v___y_3595_);
stack->m_obj
 = v_res_3616_;
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg___boxed(lean_object* v_o_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_){
_start:
{
lean_object* v_res_3620_; 
v_res_3620_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(v_o_3617_, v___y_3618_);
lean_dec(v___y_3618_);
return v_res_3620_;
}
}
lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0(lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_){
_start:
{
lean_object* v___x_3626_; lean_object* v___x_3627_; 
v___x_3626_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3623_);
v___x_3627_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(v___x_3626_, v___y_3624_);
return v___x_3627_;
}
}
LEAN_EXPORT void l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3621_ = stack[0].m_obj;
lean_object* v___y_3622_ = stack[1].m_obj;
lean_object* v___y_3623_ = stack[2].m_obj;
lean_object* v___y_3624_ = stack[3].m_obj;
lean_object* v_res_3628_;
v_res_3628_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0(v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
stack->m_obj
 = v_res_3628_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0___boxed(lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_){
_start:
{
lean_object* v_res_3634_; 
v_res_3634_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0(v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_);
lean_dec(v___y_3632_);
lean_dec_ref(v___y_3631_);
lean_dec(v___y_3630_);
lean_dec_ref(v___y_3629_);
return v_res_3634_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__1(void){
_start:
{
lean_object* v___x_3636_; lean_object* v___x_3637_; 
v___x_3636_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__0));
v___x_3637_ = l_Lean_stringToMessageData(v___x_3636_);
return v___x_3637_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__3(void){
_start:
{
lean_object* v___x_3639_; lean_object* v___x_3640_; 
v___x_3639_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__2));
v___x_3640_ = l_Lean_stringToMessageData(v___x_3639_);
return v___x_3640_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__5(void){
_start:
{
lean_object* v___x_3642_; lean_object* v___x_3643_; 
v___x_3642_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__4));
v___x_3643_ = l_Lean_stringToMessageData(v___x_3642_);
return v___x_3643_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__7(void){
_start:
{
lean_object* v___x_3645_; lean_object* v___x_3646_; 
v___x_3645_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__6));
v___x_3646_ = l_Lean_stringToMessageData(v___x_3645_);
return v___x_3646_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__9(void){
_start:
{
lean_object* v___x_3648_; lean_object* v___x_3649_; 
v___x_3648_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__8));
v___x_3649_ = l_Lean_stringToMessageData(v___x_3648_);
return v___x_3649_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__11(void){
_start:
{
lean_object* v___x_3651_; lean_object* v___x_3652_; 
v___x_3651_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__10));
v___x_3652_ = l_Lean_stringToMessageData(v___x_3651_);
return v___x_3652_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__13(void){
_start:
{
lean_object* v___x_3654_; lean_object* v___x_3655_; 
v___x_3654_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__12));
v___x_3655_ = l_Lean_stringToMessageData(v___x_3654_);
return v___x_3655_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__15(void){
_start:
{
lean_object* v___x_3658_; lean_object* v___x_3659_; 
v___x_3658_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__14));
v___x_3659_ = l_Lean_MessageData_ofFormat(v___x_3658_);
return v___x_3659_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__17(void){
_start:
{
lean_object* v___x_3661_; lean_object* v___x_3662_; 
v___x_3661_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__16));
v___x_3662_ = l_Lean_stringToMessageData(v___x_3661_);
return v___x_3662_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__19(void){
_start:
{
lean_object* v___x_3664_; lean_object* v___x_3665_; 
v___x_3664_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__18));
v___x_3665_ = l_Lean_stringToMessageData(v___x_3664_);
return v___x_3665_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__21(void){
_start:
{
lean_object* v___x_3667_; lean_object* v___x_3668_; 
v___x_3667_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__20));
v___x_3668_ = l_Lean_stringToMessageData(v___x_3667_);
return v___x_3668_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__23(void){
_start:
{
lean_object* v___x_3670_; lean_object* v___x_3671_; 
v___x_3670_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__22));
v___x_3671_ = l_Lean_stringToMessageData(v___x_3670_);
return v___x_3671_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__25(void){
_start:
{
lean_object* v___x_3673_; lean_object* v___x_3674_; 
v___x_3673_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__24));
v___x_3674_ = l_Lean_stringToMessageData(v___x_3673_);
return v___x_3674_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__27(void){
_start:
{
lean_object* v___x_3676_; lean_object* v___x_3677_; 
v___x_3676_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__26));
v___x_3677_ = l_Lean_stringToMessageData(v___x_3676_);
return v___x_3677_;
}
}
lean_object* l_Lean_Linter_checkDeprecated(lean_object* v_declName_3678_, uint8_t v_allowSuggestion_3679_, lean_object* v_a_3680_, lean_object* v_a_3681_, lean_object* v_a_3682_, lean_object* v_a_3683_){
_start:
{
lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v_a_3687_; lean_object* v___x_3689_; uint8_t v_isShared_3690_; uint8_t v_isSharedCheck_3858_; 
v___x_3685_ = ((lean_object*)(l_Lean_Linter_instInhabitedDeprecationEntry_default));
v___x_3686_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0(v_a_3680_, v_a_3681_, v_a_3682_, v_a_3683_);
v_a_3687_ = lean_ctor_get(v___x_3686_, 0);
v_isSharedCheck_3858_ = !lean_is_exclusive(v___x_3686_);
if (v_isSharedCheck_3858_ == 0)
{
v___x_3689_ = v___x_3686_;
v_isShared_3690_ = v_isSharedCheck_3858_;
goto v_resetjp_3688_;
}
else
{
lean_inc(v_a_3687_);
lean_dec(v___x_3686_);
v___x_3689_ = lean_box(0);
v_isShared_3690_ = v_isSharedCheck_3858_;
goto v_resetjp_3688_;
}
v_resetjp_3688_:
{
lean_object* v___x_3691_; uint8_t v___x_3692_; lean_object* v_extraMsg_3694_; lean_object* v___y_3695_; lean_object* v___y_3696_; lean_object* v___y_3697_; lean_object* v___y_3698_; 
v___x_3691_ = l_Lean_Linter_linter_deprecated;
v___x_3692_ = l_Lean_Linter_getLinterValue(v___x_3691_, v_a_3687_);
lean_dec(v_a_3687_);
if (v___x_3692_ == 0)
{
lean_object* v___x_3708_; lean_object* v___x_3710_; 
lean_dec(v_declName_3678_);
v___x_3708_ = lean_box(0);
if (v_isShared_3690_ == 0)
{
lean_ctor_set(v___x_3689_, 0, v___x_3708_);
v___x_3710_ = v___x_3689_;
goto v_reusejp_3709_;
}
else
{
lean_object* v_reuseFailAlloc_3711_; 
v_reuseFailAlloc_3711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3711_, 0, v___x_3708_);
v___x_3710_ = v_reuseFailAlloc_3711_;
goto v_reusejp_3709_;
}
v_reusejp_3709_:
{
return v___x_3710_;
}
}
else
{
lean_object* v___x_3712_; lean_object* v_env_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; 
v___x_3712_ = lean_st_ref_get(v_a_3683_);
v_env_3713_ = lean_ctor_get(v___x_3712_, 0);
lean_inc_ref(v_env_3713_);
lean_dec(v___x_3712_);
v___x_3714_ = l_Lean_Linter_deprecatedAttr;
lean_inc(v_declName_3678_);
v___x_3715_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_3685_, v___x_3714_, v_env_3713_, v_declName_3678_);
if (lean_obj_tag(v___x_3715_) == 1)
{
lean_object* v_val_3716_; lean_object* v_text_x3f_3717_; 
lean_del_object(v___x_3689_);
v_val_3716_ = lean_ctor_get(v___x_3715_, 0);
lean_inc(v_val_3716_);
lean_dec_ref_known(v___x_3715_, 1);
v_text_x3f_3717_ = lean_ctor_get(v_val_3716_, 1);
if (lean_obj_tag(v_text_x3f_3717_) == 0)
{
lean_object* v_newName_x3f_3718_; 
v_newName_x3f_3718_ = lean_ctor_get(v_val_3716_, 0);
lean_inc(v_newName_x3f_3718_);
lean_dec(v_val_3716_);
if (lean_obj_tag(v_newName_x3f_3718_) == 0)
{
lean_object* v___x_3719_; 
v___x_3719_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__9);
v_extraMsg_3694_ = v___x_3719_;
v___y_3695_ = v_a_3680_;
v___y_3696_ = v_a_3681_;
v___y_3697_ = v_a_3682_;
v___y_3698_ = v_a_3683_;
goto v___jp_3693_;
}
else
{
lean_object* v_val_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v_env_3727_; lean_object* v___x_3728_; uint8_t v___x_3729_; lean_object* v___x_3730_; 
v_val_3720_ = lean_ctor_get(v_newName_x3f_3718_, 0);
lean_inc_n(v_val_3720_, 2);
lean_dec_ref_known(v_newName_x3f_3718_, 1);
v___x_3721_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__3, &l_Lean_Linter_checkDeprecated___closed__3_once, _init_l_Lean_Linter_checkDeprecated___closed__3);
v___x_3722_ = l_Lean_MessageData_ofConstName(v_val_3720_, v___x_3692_);
lean_inc_ref(v___x_3722_);
v___x_3723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3723_, 0, v___x_3721_);
lean_ctor_set(v___x_3723_, 1, v___x_3722_);
v___x_3724_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__56_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__56_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__56_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_3725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3725_, 0, v___x_3723_);
lean_ctor_set(v___x_3725_, 1, v___x_3724_);
v___x_3726_ = lean_st_ref_get(v_a_3683_);
v_env_3727_ = lean_ctor_get(v___x_3726_, 0);
lean_inc_ref_n(v_env_3727_, 2);
lean_dec(v___x_3726_);
v___x_3728_ = l_Lean_Name_getPrefix(v_declName_3678_);
v___x_3729_ = 0;
lean_inc(v_declName_3678_);
v___x_3730_ = l_Lean_Environment_find_x3f(v_env_3727_, v_declName_3678_, v___x_3729_);
if (lean_obj_tag(v___x_3730_) == 1)
{
lean_object* v_val_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; 
v_val_3731_ = lean_ctor_get(v___x_3730_, 0);
lean_inc(v_val_3731_);
lean_dec_ref_known(v___x_3730_, 1);
v___x_3732_ = l_Lean_Name_getPrefix(v_val_3720_);
lean_inc(v_val_3720_);
lean_inc_ref(v_env_3727_);
v___x_3733_ = l_Lean_Environment_find_x3f(v_env_3727_, v_val_3720_, v___x_3729_);
if (lean_obj_tag(v___x_3733_) == 1)
{
lean_object* v_val_3734_; lean_object* v___x_3735_; 
v_val_3734_ = lean_ctor_get(v___x_3733_, 0);
lean_inc(v_val_3734_);
lean_dec_ref_known(v___x_3733_, 1);
v___x_3735_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq(v_val_3731_, v_val_3734_, v_a_3680_, v_a_3681_, v_a_3682_, v_a_3683_);
if (lean_obj_tag(v___x_3735_) == 0)
{
lean_object* v_a_3736_; lean_object* v_msg_3738_; lean_object* v___y_3739_; lean_object* v___y_3740_; lean_object* v___y_3741_; lean_object* v___y_3742_; lean_object* v___y_3757_; lean_object* v___y_3758_; lean_object* v___y_3759_; lean_object* v___y_3760_; lean_object* v___y_3761_; lean_object* v___y_3762_; lean_object* v___y_3777_; lean_object* v___y_3778_; lean_object* v___y_3779_; lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v___y_3782_; uint8_t v___y_3790_; lean_object* v___y_3791_; lean_object* v___y_3792_; lean_object* v___y_3793_; lean_object* v___y_3794_; lean_object* v___y_3795_; uint8_t v___y_3796_; lean_object* v_msg_3823_; lean_object* v___y_3824_; lean_object* v___y_3825_; lean_object* v___y_3826_; lean_object* v___y_3827_; uint8_t v___x_3830_; 
v_a_3736_ = lean_ctor_get(v___x_3735_, 0);
lean_inc(v_a_3736_);
lean_dec_ref_known(v___x_3735_, 1);
v___x_3830_ = lean_unbox(v_a_3736_);
if (v___x_3830_ == 0)
{
if (v___x_3692_ == 0)
{
lean_dec(v_val_3734_);
lean_dec(v_val_3731_);
v_msg_3823_ = v___x_3725_;
v___y_3824_ = v_a_3680_;
v___y_3825_ = v_a_3681_;
v___y_3826_ = v_a_3682_;
v___y_3827_ = v_a_3683_;
goto v___jp_3822_;
}
else
{
lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; 
v___x_3831_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_3832_ = l_Lean_ConstantInfo_type(v_val_3734_);
lean_dec(v_val_3734_);
v___x_3833_ = l_Lean_indentExpr(v___x_3832_);
v___x_3834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3834_, 0, v___x_3831_);
lean_ctor_set(v___x_3834_, 1, v___x_3833_);
v___x_3835_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_3836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3836_, 0, v___x_3834_);
lean_ctor_set(v___x_3836_, 1, v___x_3835_);
v___x_3837_ = l_Lean_ConstantInfo_type(v_val_3731_);
lean_dec(v_val_3731_);
v___x_3838_ = l_Lean_indentExpr(v___x_3837_);
v___x_3839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3839_, 0, v___x_3836_);
lean_ctor_set(v___x_3839_, 1, v___x_3838_);
v___x_3840_ = l_Lean_MessageData_note(v___x_3839_);
v___x_3841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3841_, 0, v___x_3725_);
lean_ctor_set(v___x_3841_, 1, v___x_3840_);
v_msg_3823_ = v___x_3841_;
v___y_3824_ = v_a_3680_;
v___y_3825_ = v_a_3681_;
v___y_3826_ = v_a_3682_;
v___y_3827_ = v_a_3683_;
goto v___jp_3822_;
}
}
else
{
lean_dec(v_val_3734_);
lean_dec(v_val_3731_);
v_msg_3823_ = v___x_3725_;
v___y_3824_ = v_a_3680_;
v___y_3825_ = v_a_3681_;
v___y_3826_ = v_a_3682_;
v___y_3827_ = v_a_3683_;
goto v___jp_3822_;
}
v___jp_3737_:
{
if (v_allowSuggestion_3679_ == 0)
{
lean_dec(v_a_3736_);
lean_dec(v_val_3720_);
v_extraMsg_3694_ = v_msg_3738_;
v___y_3695_ = v___y_3739_;
v___y_3696_ = v___y_3740_;
v___y_3697_ = v___y_3741_;
v___y_3698_ = v___y_3742_;
goto v___jp_3693_;
}
else
{
uint8_t v___x_3743_; 
v___x_3743_ = lean_unbox(v_a_3736_);
lean_dec(v_a_3736_);
if (v___x_3743_ == 0)
{
lean_dec(v_val_3720_);
v_extraMsg_3694_ = v_msg_3738_;
v___y_3695_ = v___y_3739_;
v___y_3696_ = v___y_3740_;
v___y_3697_ = v___y_3741_;
v___y_3698_ = v___y_3742_;
goto v___jp_3693_;
}
else
{
lean_object* v___x_3744_; 
lean_inc(v_declName_3678_);
v___x_3744_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f(v_declName_3678_, v_val_3720_, v___y_3739_, v___y_3740_, v___y_3741_, v___y_3742_);
if (lean_obj_tag(v___x_3744_) == 0)
{
lean_object* v_a_3745_; 
v_a_3745_ = lean_ctor_get(v___x_3744_, 0);
lean_inc(v_a_3745_);
lean_dec_ref_known(v___x_3744_, 1);
if (lean_obj_tag(v_a_3745_) == 1)
{
lean_object* v_val_3746_; lean_object* v___x_3747_; 
v_val_3746_ = lean_ctor_get(v_a_3745_, 0);
lean_inc(v_val_3746_);
lean_dec_ref_known(v_a_3745_, 1);
v___x_3747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3747_, 0, v_msg_3738_);
lean_ctor_set(v___x_3747_, 1, v_val_3746_);
v_extraMsg_3694_ = v___x_3747_;
v___y_3695_ = v___y_3739_;
v___y_3696_ = v___y_3740_;
v___y_3697_ = v___y_3741_;
v___y_3698_ = v___y_3742_;
goto v___jp_3693_;
}
else
{
lean_dec(v_a_3745_);
v_extraMsg_3694_ = v_msg_3738_;
v___y_3695_ = v___y_3739_;
v___y_3696_ = v___y_3740_;
v___y_3697_ = v___y_3741_;
v___y_3698_ = v___y_3742_;
goto v___jp_3693_;
}
}
else
{
lean_object* v_a_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3755_; 
lean_dec_ref(v_msg_3738_);
lean_dec(v_declName_3678_);
v_a_3748_ = lean_ctor_get(v___x_3744_, 0);
v_isSharedCheck_3755_ = !lean_is_exclusive(v___x_3744_);
if (v_isSharedCheck_3755_ == 0)
{
v___x_3750_ = v___x_3744_;
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_a_3748_);
lean_dec(v___x_3744_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v___x_3753_; 
if (v_isShared_3751_ == 0)
{
v___x_3753_ = v___x_3750_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v_a_3748_);
v___x_3753_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
return v___x_3753_;
}
}
}
}
}
}
v___jp_3756_:
{
lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; 
v___x_3763_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_3764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3764_, 0, v___x_3763_);
lean_ctor_set(v___x_3764_, 1, v___x_3722_);
v___x_3765_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__5, &l_Lean_Linter_checkDeprecated___closed__5_once, _init_l_Lean_Linter_checkDeprecated___closed__5);
v___x_3766_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3766_, 0, v___x_3764_);
lean_ctor_set(v___x_3766_, 1, v___x_3765_);
v___x_3767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3767_, 0, v___x_3766_);
lean_ctor_set(v___x_3767_, 1, v___y_3762_);
v___x_3768_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__7, &l_Lean_Linter_checkDeprecated___closed__7_once, _init_l_Lean_Linter_checkDeprecated___closed__7);
v___x_3769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3769_, 0, v___x_3767_);
lean_ctor_set(v___x_3769_, 1, v___x_3768_);
v___x_3770_ = l_Lean_MessageData_ofName(v___x_3732_);
v___x_3771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3771_, 0, v___x_3769_);
lean_ctor_set(v___x_3771_, 1, v___x_3770_);
v___x_3772_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__9, &l_Lean_Linter_checkDeprecated___closed__9_once, _init_l_Lean_Linter_checkDeprecated___closed__9);
v___x_3773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3773_, 0, v___x_3771_);
lean_ctor_set(v___x_3773_, 1, v___x_3772_);
v___x_3774_ = l_Lean_MessageData_note(v___x_3773_);
v___x_3775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3775_, 0, v___y_3761_);
lean_ctor_set(v___x_3775_, 1, v___x_3774_);
v_msg_3738_ = v___x_3775_;
v___y_3739_ = v___y_3757_;
v___y_3740_ = v___y_3760_;
v___y_3741_ = v___y_3758_;
v___y_3742_ = v___y_3759_;
goto v___jp_3737_;
}
v___jp_3776_:
{
lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; 
v___x_3783_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__11, &l_Lean_Linter_checkDeprecated___closed__11_once, _init_l_Lean_Linter_checkDeprecated___closed__11);
v___x_3784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3784_, 0, v___x_3783_);
lean_ctor_set(v___x_3784_, 1, v___y_3782_);
v___x_3785_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__13, &l_Lean_Linter_checkDeprecated___closed__13_once, _init_l_Lean_Linter_checkDeprecated___closed__13);
v___x_3786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3786_, 0, v___x_3784_);
lean_ctor_set(v___x_3786_, 1, v___x_3785_);
v___x_3787_ = l_Lean_MessageData_note(v___x_3786_);
v___x_3788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3788_, 0, v___y_3781_);
lean_ctor_set(v___x_3788_, 1, v___x_3787_);
v_msg_3738_ = v___x_3788_;
v___y_3739_ = v___y_3777_;
v___y_3740_ = v___y_3780_;
v___y_3741_ = v___y_3778_;
v___y_3742_ = v___y_3779_;
goto v___jp_3737_;
}
v___jp_3789_:
{
if (v___y_3796_ == 0)
{
uint8_t v___x_3797_; 
lean_inc(v_declName_3678_);
lean_inc_ref(v_env_3727_);
v___x_3797_ = l_Lean_isProtected(v_env_3727_, v_declName_3678_);
if (v___x_3797_ == 0)
{
if (v___x_3692_ == 0)
{
lean_dec(v___x_3732_);
lean_dec_ref(v_env_3727_);
lean_dec_ref(v___x_3722_);
v_msg_3738_ = v___y_3795_;
v___y_3739_ = v___y_3791_;
v___y_3740_ = v___y_3794_;
v___y_3741_ = v___y_3792_;
v___y_3742_ = v___y_3793_;
goto v___jp_3737_;
}
else
{
uint8_t v___x_3798_; 
lean_inc(v_val_3720_);
v___x_3798_ = l_Lean_isProtected(v_env_3727_, v_val_3720_);
if (v___x_3798_ == 0)
{
lean_dec(v___x_3732_);
lean_dec_ref(v___x_3722_);
v_msg_3738_ = v___y_3795_;
v___y_3739_ = v___y_3791_;
v___y_3740_ = v___y_3794_;
v___y_3741_ = v___y_3792_;
v___y_3742_ = v___y_3793_;
goto v___jp_3737_;
}
else
{
lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; uint8_t v___x_3802_; 
lean_inc(v___x_3732_);
v___x_3799_ = l_Lean_Name_componentsRev(v___x_3732_);
v___x_3800_ = lean_unsigned_to_nat(1u);
v___x_3801_ = l_List_lengthTR___redArg(v___x_3799_);
v___x_3802_ = lean_nat_dec_lt(v___x_3800_, v___x_3801_);
lean_dec(v___x_3801_);
if (v___x_3802_ == 0)
{
lean_object* v___x_3803_; 
lean_dec(v___x_3799_);
v___x_3803_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__15, &l_Lean_Linter_checkDeprecated___closed__15_once, _init_l_Lean_Linter_checkDeprecated___closed__15);
v___y_3757_ = v___y_3791_;
v___y_3758_ = v___y_3792_;
v___y_3759_ = v___y_3793_;
v___y_3760_ = v___y_3794_;
v___y_3761_ = v___y_3795_;
v___y_3762_ = v___x_3803_;
goto v___jp_3756_;
}
else
{
lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; 
v___x_3804_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__17, &l_Lean_Linter_checkDeprecated___closed__17_once, _init_l_Lean_Linter_checkDeprecated___closed__17);
v___x_3805_ = lean_unsigned_to_nat(0u);
v___x_3806_ = l_List_get___redArg(v___x_3799_, v___x_3805_);
lean_dec(v___x_3799_);
v___x_3807_ = l_Lean_MessageData_ofName(v___x_3806_);
v___x_3808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3808_, 0, v___x_3804_);
lean_ctor_set(v___x_3808_, 1, v___x_3807_);
v___x_3809_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__19, &l_Lean_Linter_checkDeprecated___closed__19_once, _init_l_Lean_Linter_checkDeprecated___closed__19);
v___x_3810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3810_, 0, v___x_3808_);
lean_ctor_set(v___x_3810_, 1, v___x_3809_);
v___y_3757_ = v___y_3791_;
v___y_3758_ = v___y_3792_;
v___y_3759_ = v___y_3793_;
v___y_3760_ = v___y_3794_;
v___y_3761_ = v___y_3795_;
v___y_3762_ = v___x_3810_;
goto v___jp_3756_;
}
}
}
}
else
{
lean_dec(v___x_3732_);
lean_dec_ref(v_env_3727_);
lean_dec_ref(v___x_3722_);
v_msg_3738_ = v___y_3795_;
v___y_3739_ = v___y_3791_;
v___y_3740_ = v___y_3794_;
v___y_3741_ = v___y_3792_;
v___y_3742_ = v___y_3793_;
goto v___jp_3737_;
}
}
else
{
lean_dec(v___x_3732_);
lean_dec_ref(v_env_3727_);
lean_dec_ref(v___x_3722_);
if (lean_obj_tag(v_declName_3678_) == 1)
{
lean_object* v_str_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; 
v_str_3811_ = lean_ctor_get(v_declName_3678_, 1);
v___x_3812_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__21, &l_Lean_Linter_checkDeprecated___closed__21_once, _init_l_Lean_Linter_checkDeprecated___closed__21);
lean_inc_ref(v_str_3811_);
v___x_3813_ = l_Lean_stringToMessageData(v_str_3811_);
v___x_3814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3814_, 0, v___x_3812_);
lean_ctor_set(v___x_3814_, 1, v___x_3813_);
v___x_3815_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__23, &l_Lean_Linter_checkDeprecated___closed__23_once, _init_l_Lean_Linter_checkDeprecated___closed__23);
v___x_3816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3816_, 0, v___x_3814_);
lean_ctor_set(v___x_3816_, 1, v___x_3815_);
lean_inc(v_val_3720_);
v___x_3817_ = l_Lean_MessageData_ofConstName(v_val_3720_, v___y_3790_);
v___x_3818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3818_, 0, v___x_3816_);
lean_ctor_set(v___x_3818_, 1, v___x_3817_);
v___x_3819_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__25, &l_Lean_Linter_checkDeprecated___closed__25_once, _init_l_Lean_Linter_checkDeprecated___closed__25);
v___x_3820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3820_, 0, v___x_3818_);
lean_ctor_set(v___x_3820_, 1, v___x_3819_);
v___y_3777_ = v___y_3791_;
v___y_3778_ = v___y_3792_;
v___y_3779_ = v___y_3793_;
v___y_3780_ = v___y_3794_;
v___y_3781_ = v___y_3795_;
v___y_3782_ = v___x_3820_;
goto v___jp_3776_;
}
else
{
lean_object* v___x_3821_; 
v___x_3821_ = l_Lean_MessageData_nil;
v___y_3777_ = v___y_3791_;
v___y_3778_ = v___y_3792_;
v___y_3779_ = v___y_3793_;
v___y_3780_ = v___y_3794_;
v___y_3781_ = v___y_3795_;
v___y_3782_ = v___x_3821_;
goto v___jp_3776_;
}
}
}
v___jp_3822_:
{
uint8_t v___x_3828_; 
v___x_3828_ = l_Lean_Name_isAnonymous(v___x_3728_);
if (v___x_3828_ == 0)
{
uint8_t v___x_3829_; 
v___x_3829_ = lean_name_eq(v___x_3728_, v___x_3732_);
lean_dec(v___x_3728_);
if (v___x_3829_ == 0)
{
v___y_3790_ = v___x_3828_;
v___y_3791_ = v___y_3824_;
v___y_3792_ = v___y_3826_;
v___y_3793_ = v___y_3827_;
v___y_3794_ = v___y_3825_;
v___y_3795_ = v_msg_3823_;
v___y_3796_ = v___x_3692_;
goto v___jp_3789_;
}
else
{
v___y_3790_ = v___x_3828_;
v___y_3791_ = v___y_3824_;
v___y_3792_ = v___y_3826_;
v___y_3793_ = v___y_3827_;
v___y_3794_ = v___y_3825_;
v___y_3795_ = v_msg_3823_;
v___y_3796_ = v___x_3828_;
goto v___jp_3789_;
}
}
else
{
lean_dec(v___x_3732_);
lean_dec(v___x_3728_);
lean_dec_ref(v_env_3727_);
lean_dec_ref(v___x_3722_);
v_msg_3738_ = v_msg_3823_;
v___y_3739_ = v___y_3824_;
v___y_3740_ = v___y_3825_;
v___y_3741_ = v___y_3826_;
v___y_3742_ = v___y_3827_;
goto v___jp_3737_;
}
}
}
else
{
lean_object* v_a_3842_; lean_object* v___x_3844_; uint8_t v_isShared_3845_; uint8_t v_isSharedCheck_3849_; 
lean_dec(v_val_3734_);
lean_dec(v___x_3732_);
lean_dec(v_val_3731_);
lean_dec(v___x_3728_);
lean_dec_ref(v_env_3727_);
lean_dec_ref_known(v___x_3725_, 2);
lean_dec_ref(v___x_3722_);
lean_dec(v_val_3720_);
lean_dec(v_declName_3678_);
v_a_3842_ = lean_ctor_get(v___x_3735_, 0);
v_isSharedCheck_3849_ = !lean_is_exclusive(v___x_3735_);
if (v_isSharedCheck_3849_ == 0)
{
v___x_3844_ = v___x_3735_;
v_isShared_3845_ = v_isSharedCheck_3849_;
goto v_resetjp_3843_;
}
else
{
lean_inc(v_a_3842_);
lean_dec(v___x_3735_);
v___x_3844_ = lean_box(0);
v_isShared_3845_ = v_isSharedCheck_3849_;
goto v_resetjp_3843_;
}
v_resetjp_3843_:
{
lean_object* v___x_3847_; 
if (v_isShared_3845_ == 0)
{
v___x_3847_ = v___x_3844_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v_a_3842_);
v___x_3847_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
return v___x_3847_;
}
}
}
}
else
{
lean_dec(v___x_3733_);
lean_dec(v___x_3732_);
lean_dec(v_val_3731_);
lean_dec(v___x_3728_);
lean_dec_ref(v_env_3727_);
lean_dec_ref(v___x_3722_);
lean_dec(v_val_3720_);
v_extraMsg_3694_ = v___x_3725_;
v___y_3695_ = v_a_3680_;
v___y_3696_ = v_a_3681_;
v___y_3697_ = v_a_3682_;
v___y_3698_ = v_a_3683_;
goto v___jp_3693_;
}
}
else
{
lean_dec(v___x_3730_);
lean_dec(v___x_3728_);
lean_dec_ref(v_env_3727_);
lean_dec_ref(v___x_3722_);
lean_dec(v_val_3720_);
v_extraMsg_3694_ = v___x_3725_;
v___y_3695_ = v_a_3680_;
v___y_3696_ = v_a_3681_;
v___y_3697_ = v_a_3682_;
v___y_3698_ = v_a_3683_;
goto v___jp_3693_;
}
}
}
else
{
lean_object* v_val_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; 
lean_inc_ref(v_text_x3f_3717_);
lean_dec(v_val_3716_);
v_val_3850_ = lean_ctor_get(v_text_x3f_3717_, 0);
lean_inc(v_val_3850_);
lean_dec_ref_known(v_text_x3f_3717_, 1);
v___x_3851_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__27, &l_Lean_Linter_checkDeprecated___closed__27_once, _init_l_Lean_Linter_checkDeprecated___closed__27);
v___x_3852_ = l_Lean_stringToMessageData(v_val_3850_);
v___x_3853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3853_, 0, v___x_3851_);
lean_ctor_set(v___x_3853_, 1, v___x_3852_);
v_extraMsg_3694_ = v___x_3853_;
v___y_3695_ = v_a_3680_;
v___y_3696_ = v_a_3681_;
v___y_3697_ = v_a_3682_;
v___y_3698_ = v_a_3683_;
goto v___jp_3693_;
}
}
else
{
lean_object* v___x_3854_; lean_object* v___x_3856_; 
lean_dec(v___x_3715_);
lean_dec(v_declName_3678_);
v___x_3854_ = lean_box(0);
if (v_isShared_3690_ == 0)
{
lean_ctor_set(v___x_3689_, 0, v___x_3854_);
v___x_3856_ = v___x_3689_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v___x_3854_);
v___x_3856_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3855_;
}
v_reusejp_3855_:
{
return v___x_3856_;
}
}
}
v___jp_3693_:
{
lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; 
v___x_3699_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_3700_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_3701_ = l_Lean_MessageData_ofConstName(v_declName_3678_, v___x_3692_);
v___x_3702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3702_, 0, v___x_3700_);
lean_ctor_set(v___x_3702_, 1, v___x_3701_);
v___x_3703_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__1, &l_Lean_Linter_checkDeprecated___closed__1_once, _init_l_Lean_Linter_checkDeprecated___closed__1);
v___x_3704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3704_, 0, v___x_3702_);
lean_ctor_set(v___x_3704_, 1, v___x_3703_);
v___x_3705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3705_, 0, v___x_3704_);
lean_ctor_set(v___x_3705_, 1, v_extraMsg_3694_);
v___x_3706_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3706_, 0, v___x_3699_);
lean_ctor_set(v___x_3706_, 1, v___x_3705_);
v___x_3707_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38(v___x_3706_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_);
return v___x_3707_;
}
}
}
}
LEAN_EXPORT void l_Lean_Linter_checkDeprecated_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_3678_ = stack[0].m_obj;
uint8_t v_allowSuggestion_3679_ = stack[1].m_num;
lean_object* v_a_3680_ = stack[2].m_obj;
lean_object* v_a_3681_ = stack[3].m_obj;
lean_object* v_a_3682_ = stack[4].m_obj;
lean_object* v_a_3683_ = stack[5].m_obj;
lean_object* v_res_3859_;
v_res_3859_ = l_Lean_Linter_checkDeprecated(v_declName_3678_, v_allowSuggestion_3679_, v_a_3680_, v_a_3681_, v_a_3682_, v_a_3683_);
stack->m_obj
 = v_res_3859_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkDeprecated___boxed(lean_object* v_declName_3860_, lean_object* v_allowSuggestion_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_){
_start:
{
uint8_t v_allowSuggestion_boxed_3867_; lean_object* v_res_3868_; 
v_allowSuggestion_boxed_3867_ = lean_unbox(v_allowSuggestion_3861_);
v_res_3868_ = l_Lean_Linter_checkDeprecated(v_declName_3860_, v_allowSuggestion_boxed_3867_, v_a_3862_, v_a_3863_, v_a_3864_, v_a_3865_);
lean_dec(v_a_3865_);
lean_dec_ref(v_a_3864_);
lean_dec(v_a_3863_);
lean_dec_ref(v_a_3862_);
return v_res_3868_;
}
}
lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0(lean_object* v_o_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_){
_start:
{
lean_object* v___x_3875_; 
v___x_3875_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(v_o_3869_, v___y_3873_);
return v___x_3875_;
}
}
LEAN_EXPORT void l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_3869_ = stack[0].m_obj;
lean_object* v___y_3870_ = stack[1].m_obj;
lean_object* v___y_3871_ = stack[2].m_obj;
lean_object* v___y_3872_ = stack[3].m_obj;
lean_object* v___y_3873_ = stack[4].m_obj;
lean_object* v_res_3876_;
v_res_3876_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0(v_o_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_);
stack->m_obj
 = v_res_3876_;
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___boxed(lean_object* v_o_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_){
_start:
{
lean_object* v_res_3883_; 
v_res_3883_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0(v_o_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_);
lean_dec(v___y_3881_);
lean_dec_ref(v___y_3880_);
lean_dec(v___y_3879_);
lean_dec_ref(v___y_3878_);
return v_res_3883_;
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
