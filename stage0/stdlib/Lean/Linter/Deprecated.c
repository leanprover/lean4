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
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_ResolveName_backward_privateInPublic_warn;
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_MacroScopesView_review(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_extractMacroScopes(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MacroScopesView_isSuffixOf(lean_object*, lean_object*);
lean_object* l_Lean_privateToUserName_x3f(lean_object*);
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
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
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
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_registerParametricAttributeExt___redArg(lean_object*, uint8_t, lean_object*, uint8_t);
lean_object* l_Lean_TSyntax_getString(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_MessageData_hint_x27(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
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
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
extern lean_object* l_Lean_Linter_linterSetsExt;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
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
lean_object* l_Lean_ParametricAttribute_setParam___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___redArg(lean_object*, lean_object*);
lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
uint8_t l_Lean_isProtected(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__7___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Try this: +typeChanged"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__19___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__19___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23_spec__26___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23_spec__26___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__25___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__25___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26_spec__30___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26_spec__30___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__33(lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__33___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__39___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__39___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44_spec__46_spec__49(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44_spec__46_spec__49___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44_spec__46___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44_spec__46___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44_spec__46___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44_spec__46(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44_spec__46___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Private declaration `"};
static const lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34___closed__0 = (const lean_object*)&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34___closed__0_value;
static lean_once_cell_t l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34___closed__1;
static const lean_string_object l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 167, .m_capacity = 167, .m_length = 166, .m_data = "` accessed publicly; this is allowed only because the `backward.privateInPublic` option is enabled. \n\nDisable `backward.privateInPublic.warn` to silence this warning."};
static const lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34___closed__2 = (const lean_object*)&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34___closed__2_value;
static lean_once_cell_t l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34___closed__3;
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_any___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__29(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__29___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__24___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__24___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46_spec__48_spec__50___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46_spec__48_spec__50___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46_spec__48_spec__50___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46_spec__48_spec__50(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46_spec__48_spec__50___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46_spec__48(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46_spec__48___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__45___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__45___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__24___lam__0___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27___closed__0 = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27___closed__0_value;
static const lean_closure_object l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__24___lam__0___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46_spec__48_spec__50___closed__0_value)} };
static const lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27___closed__1 = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__24_spec__32___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__24_spec__32___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__24___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__24___closed__0 = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__24___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__26(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14___closed__0 = (const lean_object*)&l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6___lam__0___boxed, .m_arity = 7, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6___closed__0 = (const lean_object*)&l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4_spec__10___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4_spec__10___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4_spec__10___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4_spec__10___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4_spec__10___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4_spec__10___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14_spec__19___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__27_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__27_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static const lean_array_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__28_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__28_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__28_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 88, .m_capacity = 88, .m_length = 87, .m_data = "The `+typeChanged` marker is not needed because the updated constant has the same type."};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__36_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "This warning can be disabled with `set_option "};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__36_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__36_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__37_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__37_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__38_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " false`"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__38_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__38_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__39_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__39_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__40_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__40_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__40_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = "` is itself deprecated, but without an explicit replacement; `"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "` is being deprecated in favor of a deprecated declaration"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "` is itself deprecated in favor of `"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__47_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__47_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__48_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "`; consider deprecating `"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__48_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__48_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__49_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__49_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__50_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "` in favor of `"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__50_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__50_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__51_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__51_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__52_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` instead"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__52_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__52_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__53_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__53_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__54_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Deprecate in favor of `"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__54_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__54_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__55_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__55_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__56_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "` instead:"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__56_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__56_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__57_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__57_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__58_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Invalid `[deprecated]` attribute: `"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__58_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__58_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__59_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__59_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__60_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "` cannot be deprecated in favor of itself"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__60_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__60_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__61_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__61_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "deprecatedAttr"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(85, 246, 23, 143, 159, 138, 155, 162)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(78, 182, 79, 155, 204, 118, 39, 140)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "mark declaration as deprecated"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4_spec__10(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__19(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__19___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__24_spec__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__24_spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23_spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26_spec__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26_spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__39(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__39___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__45(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__45___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Linter_checkDeprecated___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44_spec__46___closed__0_value)}};
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
v_type_u2081_310_ = l_Lean_ConstantInfo_instantiateTypeLevelParams(v_decl_u2081_275_, v_levels_309_);
v_type_u2082_311_ = l_Lean_ConstantInfo_instantiateTypeLevelParams(v_decl_u2082_276_, v_levels_309_);
lean_dec(v_levels_309_);
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5(lean_object* v_opts_337_, lean_object* v_opt_338_){
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5___boxed(lean_object* v_opts_347_, lean_object* v_opt_348_){
_start:
{
uint8_t v_res_349_; lean_object* v_r_350_; 
v_res_349_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5(v_opts_347_, v_opt_348_);
lean_dec_ref(v_opt_348_);
lean_dec_ref(v_opts_347_);
v_r_350_ = lean_box(v_res_349_);
return v_r_350_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__7(lean_object* v_x_351_, lean_object* v_x_352_){
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
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__7___boxed(lean_object* v_x_359_, lean_object* v_x_360_){
_start:
{
uint8_t v_res_361_; lean_object* v_r_362_; 
v_res_361_ = l_instBEqOption_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__7(v_x_359_, v_x_360_);
lean_dec(v_x_360_);
lean_dec(v_x_359_);
v_r_362_ = lean_box(v_res_361_);
return v_r_362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(lean_object* v_x_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2____boxed(lean_object* v_x_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(v_x_366_);
lean_dec_ref(v_x_366_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(lean_object* v_x_368_, lean_object* v_x_369_, lean_object* v_x_370_, lean_object* v___y_371_){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = lean_box(0);
v___x_374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2____boxed(lean_object* v_x_375_, lean_object* v_x_376_, lean_object* v_x_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(v_x_375_, v_x_376_, v_x_377_, v___y_378_);
lean_dec(v___y_378_);
lean_dec_ref(v_x_377_);
lean_dec_ref(v_x_376_);
lean_dec(v_x_375_);
return v_res_380_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(uint8_t v___x_381_, lean_object* v_env_382_, lean_object* v_n_383_, lean_object* v_x_384_){
_start:
{
uint8_t v___x_385_; 
v___x_385_ = l_Lean_Environment_contains(v_env_382_, v_n_383_, v___x_381_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2____boxed(lean_object* v___x_386_, lean_object* v_env_387_, lean_object* v_n_388_, lean_object* v_x_389_){
_start:
{
uint8_t v___x_44511__boxed_390_; uint8_t v_res_391_; lean_object* v_r_392_; 
v___x_44511__boxed_390_ = lean_unbox(v___x_386_);
v_res_391_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(v___x_44511__boxed_390_, v_env_387_, v_n_388_, v_x_389_);
lean_dec_ref(v_x_389_);
v_r_392_ = lean_box(v_res_391_);
return v_r_392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22___redArg___lam__0(lean_object* v_localDecl_393_, lean_object* v_givenName_394_){
_start:
{
lean_object* v___x_395_; uint8_t v___x_396_; 
v___x_395_ = l_Lean_LocalDecl_userName(v_localDecl_393_);
v___x_396_ = lean_name_eq(v___x_395_, v_givenName_394_);
lean_dec(v___x_395_);
if (v___x_396_ == 0)
{
lean_object* v___x_397_; 
lean_dec_ref(v_localDecl_393_);
v___x_397_ = lean_box(0);
return v___x_397_;
}
else
{
lean_object* v___x_398_; 
v___x_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_398_, 0, v_localDecl_393_);
return v___x_398_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22___redArg___lam__0___boxed(lean_object* v_localDecl_399_, lean_object* v_givenName_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22___redArg___lam__0(v_localDecl_399_, v_givenName_400_);
lean_dec(v_givenName_400_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__19___redArg(lean_object* v_t_402_, lean_object* v_k_403_){
_start:
{
if (lean_obj_tag(v_t_402_) == 0)
{
lean_object* v_k_404_; lean_object* v_v_405_; lean_object* v_l_406_; lean_object* v_r_407_; uint8_t v___x_408_; 
v_k_404_ = lean_ctor_get(v_t_402_, 1);
v_v_405_ = lean_ctor_get(v_t_402_, 2);
v_l_406_ = lean_ctor_get(v_t_402_, 3);
v_r_407_ = lean_ctor_get(v_t_402_, 4);
v___x_408_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_403_, v_k_404_);
switch(v___x_408_)
{
case 0:
{
v_t_402_ = v_l_406_;
goto _start;
}
case 1:
{
lean_object* v___x_410_; 
lean_inc(v_v_405_);
v___x_410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_410_, 0, v_v_405_);
return v___x_410_;
}
default: 
{
v_t_402_ = v_r_407_;
goto _start;
}
}
}
else
{
lean_object* v___x_412_; 
v___x_412_ = lean_box(0);
return v___x_412_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__19___redArg___boxed(lean_object* v_t_413_, lean_object* v_k_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__19___redArg(v_t_413_, v_k_414_);
lean_dec(v_k_414_);
lean_dec(v_t_413_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22___redArg(lean_object* v_givenName_416_, lean_object* v_auxDeclToFullName_417_, lean_object* v___x_418_, lean_object* v_givenNameView_419_, lean_object* v_as_420_, lean_object* v_i_421_){
_start:
{
lean_object* v_zero_422_; uint8_t v_isZero_423_; 
v_zero_422_ = lean_unsigned_to_nat(0u);
v_isZero_423_ = lean_nat_dec_eq(v_i_421_, v_zero_422_);
if (v_isZero_423_ == 1)
{
lean_object* v___x_424_; 
lean_dec(v_i_421_);
lean_dec_ref(v_givenNameView_419_);
lean_dec(v___x_418_);
v___x_424_ = lean_box(0);
return v___x_424_;
}
else
{
lean_object* v_one_425_; lean_object* v_n_426_; lean_object* v___y_428_; lean_object* v___x_430_; 
v_one_425_ = lean_unsigned_to_nat(1u);
v_n_426_ = lean_nat_sub(v_i_421_, v_one_425_);
lean_dec(v_i_421_);
v___x_430_ = lean_array_fget_borrowed(v_as_420_, v_n_426_);
if (lean_obj_tag(v___x_430_) == 0)
{
v_i_421_ = v_n_426_;
goto _start;
}
else
{
lean_object* v_val_432_; uint8_t v___x_433_; 
v_val_432_ = lean_ctor_get(v___x_430_, 0);
v___x_433_ = l_Lean_LocalDecl_isAuxDecl(v_val_432_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; 
lean_inc(v_val_432_);
v___x_434_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22___redArg___lam__0(v_val_432_, v_givenName_416_);
v___y_428_ = v___x_434_;
goto v___jp_427_;
}
else
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = l_Lean_LocalDecl_fvarId(v_val_432_);
v___x_436_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__19___redArg(v_auxDeclToFullName_417_, v___x_435_);
lean_dec(v___x_435_);
if (lean_obj_tag(v___x_436_) == 1)
{
lean_object* v_val_437_; lean_object* v_fullDeclView_438_; lean_object* v_name_439_; lean_object* v_imported_440_; lean_object* v_ctx_441_; lean_object* v_scopes_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_462_; 
v_val_437_ = lean_ctor_get(v___x_436_, 0);
lean_inc(v_val_437_);
lean_dec_ref_known(v___x_436_, 1);
v_fullDeclView_438_ = l_Lean_extractMacroScopes(v_val_437_);
v_name_439_ = lean_ctor_get(v_fullDeclView_438_, 0);
v_imported_440_ = lean_ctor_get(v_fullDeclView_438_, 1);
v_ctx_441_ = lean_ctor_get(v_fullDeclView_438_, 2);
v_scopes_442_ = lean_ctor_get(v_fullDeclView_438_, 3);
v_isSharedCheck_462_ = !lean_is_exclusive(v_fullDeclView_438_);
if (v_isSharedCheck_462_ == 0)
{
v___x_444_ = v_fullDeclView_438_;
v_isShared_445_ = v_isSharedCheck_462_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_scopes_442_);
lean_inc(v_ctx_441_);
lean_inc(v_imported_440_);
lean_inc(v_name_439_);
lean_dec(v_fullDeclView_438_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_462_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___y_447_; lean_object* v___x_460_; 
lean_inc(v_name_439_);
v___x_460_ = l_Lean_privateToUserName_x3f(v_name_439_);
if (lean_obj_tag(v___x_460_) == 0)
{
v___y_447_ = v_name_439_;
goto v___jp_446_;
}
else
{
lean_object* v_val_461_; 
lean_dec(v_name_439_);
v_val_461_ = lean_ctor_get(v___x_460_, 0);
lean_inc(v_val_461_);
lean_dec_ref_known(v___x_460_, 1);
v___y_447_ = v_val_461_;
goto v___jp_446_;
}
v___jp_446_:
{
lean_object* v_fullDeclView_449_; 
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v___y_447_);
v_fullDeclView_449_ = v___x_444_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v___y_447_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v_imported_440_);
lean_ctor_set(v_reuseFailAlloc_459_, 2, v_ctx_441_);
lean_ctor_set(v_reuseFailAlloc_459_, 3, v_scopes_442_);
v_fullDeclView_449_ = v_reuseFailAlloc_459_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
lean_object* v_fullDeclName_450_; uint8_t v___x_451_; 
lean_inc_ref(v_fullDeclView_449_);
v_fullDeclName_450_ = l_Lean_MacroScopesView_review(v_fullDeclView_449_);
v___x_451_ = l_Lean_Name_isPrefixOf(v___x_418_, v_fullDeclName_450_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; 
lean_dec_ref(v_fullDeclView_449_);
lean_inc(v___x_418_);
lean_inc_ref(v_givenNameView_419_);
lean_inc(v_val_432_);
v___x_452_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_val_432_, v_givenNameView_419_, v_fullDeclName_450_, v___x_418_);
lean_dec(v_fullDeclName_450_);
v___y_428_ = v___x_452_;
goto v___jp_427_;
}
else
{
lean_object* v___x_453_; lean_object* v_localDeclNameView_454_; uint8_t v___x_455_; 
lean_dec(v_fullDeclName_450_);
v___x_453_ = l_Lean_LocalDecl_userName(v_val_432_);
v_localDeclNameView_454_ = l_Lean_extractMacroScopes(v___x_453_);
v___x_455_ = l_Lean_MacroScopesView_isSuffixOf(v_localDeclNameView_454_, v_givenNameView_419_);
lean_dec_ref(v_localDeclNameView_454_);
if (v___x_455_ == 0)
{
lean_dec_ref(v_fullDeclView_449_);
v_i_421_ = v_n_426_;
goto _start;
}
else
{
uint8_t v___x_457_; 
v___x_457_ = l_Lean_MacroScopesView_isSuffixOf(v_givenNameView_419_, v_fullDeclView_449_);
lean_dec_ref(v_fullDeclView_449_);
if (v___x_457_ == 0)
{
v_i_421_ = v_n_426_;
goto _start;
}
else
{
lean_dec(v_n_426_);
lean_dec_ref(v_givenNameView_419_);
lean_dec(v___x_418_);
lean_inc_ref(v___x_430_);
return v___x_430_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_463_; 
lean_dec(v___x_436_);
lean_inc(v_val_432_);
v___x_463_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22___redArg___lam__0(v_val_432_, v_givenName_416_);
v___y_428_ = v___x_463_;
goto v___jp_427_;
}
}
}
v___jp_427_:
{
if (lean_obj_tag(v___y_428_) == 0)
{
v_i_421_ = v_n_426_;
goto _start;
}
else
{
lean_dec(v_n_426_);
lean_dec_ref(v_givenNameView_419_);
lean_dec(v___x_418_);
return v___y_428_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22___redArg___boxed(lean_object* v_givenName_464_, lean_object* v_auxDeclToFullName_465_, lean_object* v___x_466_, lean_object* v_givenNameView_467_, lean_object* v_as_468_, lean_object* v_i_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22___redArg(v_givenName_464_, v_auxDeclToFullName_465_, v___x_466_, v_givenNameView_467_, v_as_468_, v_i_469_);
lean_dec_ref(v_as_468_);
lean_dec(v_auxDeclToFullName_465_);
lean_dec(v_givenName_464_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23_spec__26___redArg(lean_object* v_givenName_471_, lean_object* v_auxDeclToFullName_472_, lean_object* v___x_473_, lean_object* v_givenNameView_474_, lean_object* v_as_475_, lean_object* v_i_476_){
_start:
{
lean_object* v_zero_477_; uint8_t v_isZero_478_; 
v_zero_477_ = lean_unsigned_to_nat(0u);
v_isZero_478_ = lean_nat_dec_eq(v_i_476_, v_zero_477_);
if (v_isZero_478_ == 1)
{
lean_object* v___x_479_; 
lean_dec(v_i_476_);
lean_dec_ref(v_givenNameView_474_);
lean_dec(v___x_473_);
v___x_479_ = lean_box(0);
return v___x_479_;
}
else
{
lean_object* v_one_480_; lean_object* v_n_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v_one_480_ = lean_unsigned_to_nat(1u);
v_n_481_ = lean_nat_sub(v_i_476_, v_one_480_);
lean_dec(v_i_476_);
v___x_482_ = lean_array_fget_borrowed(v_as_475_, v_n_481_);
lean_inc_ref(v_givenNameView_474_);
lean_inc(v___x_473_);
v___x_483_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23(v_givenName_471_, v_auxDeclToFullName_472_, v___x_473_, v_givenNameView_474_, v___x_482_);
if (lean_obj_tag(v___x_483_) == 0)
{
v_i_476_ = v_n_481_;
goto _start;
}
else
{
lean_dec(v_n_481_);
lean_dec_ref(v_givenNameView_474_);
lean_dec(v___x_473_);
return v___x_483_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23(lean_object* v_givenName_485_, lean_object* v_auxDeclToFullName_486_, lean_object* v___x_487_, lean_object* v_givenNameView_488_, lean_object* v_x_489_){
_start:
{
if (lean_obj_tag(v_x_489_) == 0)
{
lean_object* v_cs_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v_cs_490_ = lean_ctor_get(v_x_489_, 0);
v___x_491_ = lean_array_get_size(v_cs_490_);
v___x_492_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23_spec__26___redArg(v_givenName_485_, v_auxDeclToFullName_486_, v___x_487_, v_givenNameView_488_, v_cs_490_, v___x_491_);
return v___x_492_;
}
else
{
lean_object* v_vs_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v_vs_493_ = lean_ctor_get(v_x_489_, 0);
v___x_494_ = lean_array_get_size(v_vs_493_);
v___x_495_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22___redArg(v_givenName_485_, v_auxDeclToFullName_486_, v___x_487_, v_givenNameView_488_, v_vs_493_, v___x_494_);
return v___x_495_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23___boxed(lean_object* v_givenName_496_, lean_object* v_auxDeclToFullName_497_, lean_object* v___x_498_, lean_object* v_givenNameView_499_, lean_object* v_x_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23(v_givenName_496_, v_auxDeclToFullName_497_, v___x_498_, v_givenNameView_499_, v_x_500_);
lean_dec_ref(v_x_500_);
lean_dec(v_auxDeclToFullName_497_);
lean_dec(v_givenName_496_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23_spec__26___redArg___boxed(lean_object* v_givenName_502_, lean_object* v_auxDeclToFullName_503_, lean_object* v___x_504_, lean_object* v_givenNameView_505_, lean_object* v_as_506_, lean_object* v_i_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23_spec__26___redArg(v_givenName_502_, v_auxDeclToFullName_503_, v___x_504_, v_givenNameView_505_, v_as_506_, v_i_507_);
lean_dec_ref(v_as_506_);
lean_dec(v_auxDeclToFullName_503_);
lean_dec(v_givenName_502_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__20(lean_object* v_givenName_509_, lean_object* v_auxDeclToFullName_510_, lean_object* v___x_511_, lean_object* v_givenNameView_512_, lean_object* v_t_513_){
_start:
{
lean_object* v_root_514_; lean_object* v_tail_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v_root_514_ = lean_ctor_get(v_t_513_, 0);
v_tail_515_ = lean_ctor_get(v_t_513_, 1);
v___x_516_ = lean_array_get_size(v_tail_515_);
lean_inc_ref(v_givenNameView_512_);
lean_inc(v___x_511_);
v___x_517_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22___redArg(v_givenName_509_, v_auxDeclToFullName_510_, v___x_511_, v_givenNameView_512_, v_tail_515_, v___x_516_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v___x_518_; 
v___x_518_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23(v_givenName_509_, v_auxDeclToFullName_510_, v___x_511_, v_givenNameView_512_, v_root_514_);
return v___x_518_;
}
else
{
lean_dec_ref(v_givenNameView_512_);
lean_dec(v___x_511_);
return v___x_517_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__20___boxed(lean_object* v_givenName_519_, lean_object* v_auxDeclToFullName_520_, lean_object* v___x_521_, lean_object* v_givenNameView_522_, lean_object* v_t_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__20(v_givenName_519_, v_auxDeclToFullName_520_, v___x_521_, v_givenNameView_522_, v_t_523_);
lean_dec_ref(v_t_523_);
lean_dec(v_auxDeclToFullName_520_);
lean_dec(v_givenName_519_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__25___redArg(lean_object* v_localDecl_x3f_525_, lean_object* v_givenName_526_, lean_object* v_as_527_, lean_object* v_i_528_){
_start:
{
lean_object* v_zero_529_; uint8_t v_isZero_530_; 
v_zero_529_ = lean_unsigned_to_nat(0u);
v_isZero_530_ = lean_nat_dec_eq(v_i_528_, v_zero_529_);
if (v_isZero_530_ == 1)
{
lean_object* v___x_531_; 
lean_dec(v_i_528_);
v___x_531_ = lean_box(0);
return v___x_531_;
}
else
{
lean_object* v_one_532_; lean_object* v_n_533_; lean_object* v___x_534_; 
v_one_532_ = lean_unsigned_to_nat(1u);
v_n_533_ = lean_nat_sub(v_i_528_, v_one_532_);
lean_dec(v_i_528_);
v___x_534_ = lean_array_fget_borrowed(v_as_527_, v_n_533_);
if (lean_obj_tag(v___x_534_) == 0)
{
v_i_528_ = v_n_533_;
goto _start;
}
else
{
lean_object* v_val_536_; uint8_t v___x_537_; 
v_val_536_ = lean_ctor_get(v___x_534_, 0);
v___x_537_ = l_Lean_LocalDecl_isAuxDecl(v_val_536_);
if (v___x_537_ == 0)
{
if (lean_obj_tag(v_localDecl_x3f_525_) == 0)
{
v_i_528_ = v_n_533_;
goto _start;
}
else
{
lean_dec(v_n_533_);
lean_inc_ref(v_localDecl_x3f_525_);
return v_localDecl_x3f_525_;
}
}
else
{
lean_object* v___x_539_; uint8_t v___x_540_; 
v___x_539_ = l_Lean_LocalDecl_userName(v_val_536_);
v___x_540_ = lean_name_eq(v___x_539_, v_givenName_526_);
lean_dec(v___x_539_);
if (v___x_540_ == 0)
{
v_i_528_ = v_n_533_;
goto _start;
}
else
{
lean_dec(v_n_533_);
lean_inc_ref(v___x_534_);
return v___x_534_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__25___redArg___boxed(lean_object* v_localDecl_x3f_542_, lean_object* v_givenName_543_, lean_object* v_as_544_, lean_object* v_i_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__25___redArg(v_localDecl_x3f_542_, v_givenName_543_, v_as_544_, v_i_545_);
lean_dec_ref(v_as_544_);
lean_dec(v_givenName_543_);
lean_dec(v_localDecl_x3f_542_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26_spec__30___redArg(lean_object* v_localDecl_x3f_547_, lean_object* v_givenName_548_, lean_object* v_as_549_, lean_object* v_i_550_){
_start:
{
lean_object* v_zero_551_; uint8_t v_isZero_552_; 
v_zero_551_ = lean_unsigned_to_nat(0u);
v_isZero_552_ = lean_nat_dec_eq(v_i_550_, v_zero_551_);
if (v_isZero_552_ == 1)
{
lean_object* v___x_553_; 
lean_dec(v_i_550_);
v___x_553_ = lean_box(0);
return v___x_553_;
}
else
{
lean_object* v_one_554_; lean_object* v_n_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v_one_554_ = lean_unsigned_to_nat(1u);
v_n_555_ = lean_nat_sub(v_i_550_, v_one_554_);
lean_dec(v_i_550_);
v___x_556_ = lean_array_fget_borrowed(v_as_549_, v_n_555_);
v___x_557_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26(v_localDecl_x3f_547_, v_givenName_548_, v___x_556_);
if (lean_obj_tag(v___x_557_) == 0)
{
v_i_550_ = v_n_555_;
goto _start;
}
else
{
lean_dec(v_n_555_);
return v___x_557_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26(lean_object* v_localDecl_x3f_559_, lean_object* v_givenName_560_, lean_object* v_x_561_){
_start:
{
if (lean_obj_tag(v_x_561_) == 0)
{
lean_object* v_cs_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v_cs_562_ = lean_ctor_get(v_x_561_, 0);
v___x_563_ = lean_array_get_size(v_cs_562_);
v___x_564_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26_spec__30___redArg(v_localDecl_x3f_559_, v_givenName_560_, v_cs_562_, v___x_563_);
return v___x_564_;
}
else
{
lean_object* v_vs_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v_vs_565_ = lean_ctor_get(v_x_561_, 0);
v___x_566_ = lean_array_get_size(v_vs_565_);
v___x_567_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__25___redArg(v_localDecl_x3f_559_, v_givenName_560_, v_vs_565_, v___x_566_);
return v___x_567_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26___boxed(lean_object* v_localDecl_x3f_568_, lean_object* v_givenName_569_, lean_object* v_x_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26(v_localDecl_x3f_568_, v_givenName_569_, v_x_570_);
lean_dec_ref(v_x_570_);
lean_dec(v_givenName_569_);
lean_dec(v_localDecl_x3f_568_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26_spec__30___redArg___boxed(lean_object* v_localDecl_x3f_572_, lean_object* v_givenName_573_, lean_object* v_as_574_, lean_object* v_i_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26_spec__30___redArg(v_localDecl_x3f_572_, v_givenName_573_, v_as_574_, v_i_575_);
lean_dec_ref(v_as_574_);
lean_dec(v_givenName_573_);
lean_dec(v_localDecl_x3f_572_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__21(lean_object* v_localDecl_x3f_577_, lean_object* v_givenName_578_, lean_object* v_t_579_){
_start:
{
lean_object* v_root_580_; lean_object* v_tail_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v_root_580_ = lean_ctor_get(v_t_579_, 0);
v_tail_581_ = lean_ctor_get(v_t_579_, 1);
v___x_582_ = lean_array_get_size(v_tail_581_);
v___x_583_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__25___redArg(v_localDecl_x3f_577_, v_givenName_578_, v_tail_581_, v___x_582_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v___x_584_; 
v___x_584_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26(v_localDecl_x3f_577_, v_givenName_578_, v_root_580_);
return v___x_584_;
}
else
{
return v___x_583_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__21___boxed(lean_object* v_localDecl_x3f_585_, lean_object* v_givenName_586_, lean_object* v_t_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__21(v_localDecl_x3f_585_, v_givenName_586_, v_t_587_);
lean_dec_ref(v_t_587_);
lean_dec(v_givenName_586_);
lean_dec(v_localDecl_x3f_585_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13___lam__0(lean_object* v_auxDeclToFullName_589_, lean_object* v_currNamespace_590_, lean_object* v_decls_591_, lean_object* v_givenNameView_592_){
_start:
{
lean_object* v_givenName_593_; lean_object* v_localDecl_x3f_594_; 
lean_inc_ref(v_givenNameView_592_);
v_givenName_593_ = l_Lean_MacroScopesView_review(v_givenNameView_592_);
v_localDecl_x3f_594_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__20(v_givenName_593_, v_auxDeclToFullName_589_, v_currNamespace_590_, v_givenNameView_592_, v_decls_591_);
if (lean_obj_tag(v_localDecl_x3f_594_) == 0)
{
lean_object* v___x_595_; 
v___x_595_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__21(v_localDecl_x3f_594_, v_givenName_593_, v_decls_591_);
lean_dec(v_givenName_593_);
return v___x_595_;
}
else
{
lean_dec(v_givenName_593_);
return v_localDecl_x3f_594_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13___lam__0___boxed(lean_object* v_auxDeclToFullName_596_, lean_object* v_currNamespace_597_, lean_object* v_decls_598_, lean_object* v_givenNameView_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13___lam__0(v_auxDeclToFullName_596_, v_currNamespace_597_, v_decls_598_, v_givenNameView_599_);
lean_dec_ref(v_decls_598_);
lean_dec(v_auxDeclToFullName_596_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__33(lean_object* v_x_601_){
_start:
{
if (lean_obj_tag(v_x_601_) == 0)
{
lean_object* v___x_602_; 
v___x_602_ = lean_box(0);
return v___x_602_;
}
else
{
lean_object* v_head_603_; lean_object* v_tail_604_; lean_object* v_fst_605_; uint8_t v___x_606_; 
v_head_603_ = lean_ctor_get(v_x_601_, 0);
v_tail_604_ = lean_ctor_get(v_x_601_, 1);
v_fst_605_ = lean_ctor_get(v_head_603_, 0);
v___x_606_ = l_Lean_isPrivateName(v_fst_605_);
if (v___x_606_ == 0)
{
v_x_601_ = v_tail_604_;
goto _start;
}
else
{
lean_object* v___x_608_; 
lean_inc(v_head_603_);
v___x_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_608_, 0, v_head_603_);
return v___x_608_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__33___boxed(lean_object* v_x_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__33(v_x_609_);
lean_dec(v_x_609_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__39___redArg(lean_object* v_opt_611_, lean_object* v___y_612_){
_start:
{
lean_object* v___x_614_; uint8_t v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_614_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_612_);
v___x_615_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5(v___x_614_, v_opt_611_);
lean_dec_ref(v___x_614_);
v___x_616_ = lean_box(v___x_615_);
v___x_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__39___redArg___boxed(lean_object* v_opt_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__39___redArg(v_opt_618_, v___y_619_);
lean_dec_ref(v___y_619_);
lean_dec_ref(v_opt_618_);
return v_res_621_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0(uint8_t v_suppressElabErrors_630_, lean_object* v_x_631_){
_start:
{
if (lean_obj_tag(v_x_631_) == 1)
{
lean_object* v_pre_632_; 
v_pre_632_ = lean_ctor_get(v_x_631_, 0);
switch(lean_obj_tag(v_pre_632_))
{
case 1:
{
lean_object* v_pre_633_; 
v_pre_633_ = lean_ctor_get(v_pre_632_, 0);
switch(lean_obj_tag(v_pre_633_))
{
case 0:
{
lean_object* v_str_634_; lean_object* v_str_635_; lean_object* v___x_636_; uint8_t v___x_637_; 
v_str_634_ = lean_ctor_get(v_x_631_, 1);
v_str_635_ = lean_ctor_get(v_pre_632_, 1);
v___x_636_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__0));
v___x_637_ = lean_string_dec_eq(v_str_635_, v___x_636_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; uint8_t v___x_639_; 
v___x_638_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__1));
v___x_639_ = lean_string_dec_eq(v_str_635_, v___x_638_);
if (v___x_639_ == 0)
{
return v___x_639_;
}
else
{
lean_object* v___x_640_; uint8_t v___x_641_; 
v___x_640_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__2));
v___x_641_ = lean_string_dec_eq(v_str_634_, v___x_640_);
if (v___x_641_ == 0)
{
return v___x_641_;
}
else
{
return v_suppressElabErrors_630_;
}
}
}
else
{
lean_object* v___x_642_; uint8_t v___x_643_; 
v___x_642_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__3));
v___x_643_ = lean_string_dec_eq(v_str_634_, v___x_642_);
if (v___x_643_ == 0)
{
return v___x_643_;
}
else
{
return v_suppressElabErrors_630_;
}
}
}
case 1:
{
lean_object* v_pre_644_; 
v_pre_644_ = lean_ctor_get(v_pre_633_, 0);
if (lean_obj_tag(v_pre_644_) == 0)
{
lean_object* v_str_645_; lean_object* v_str_646_; lean_object* v_str_647_; lean_object* v___x_648_; uint8_t v___x_649_; 
v_str_645_ = lean_ctor_get(v_x_631_, 1);
v_str_646_ = lean_ctor_get(v_pre_632_, 1);
v_str_647_ = lean_ctor_get(v_pre_633_, 1);
v___x_648_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__4));
v___x_649_ = lean_string_dec_eq(v_str_647_, v___x_648_);
if (v___x_649_ == 0)
{
return v___x_649_;
}
else
{
lean_object* v___x_650_; uint8_t v___x_651_; 
v___x_650_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__5));
v___x_651_ = lean_string_dec_eq(v_str_646_, v___x_650_);
if (v___x_651_ == 0)
{
return v___x_651_;
}
else
{
lean_object* v___x_652_; uint8_t v___x_653_; 
v___x_652_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__6));
v___x_653_ = lean_string_dec_eq(v_str_645_, v___x_652_);
if (v___x_653_ == 0)
{
return v___x_653_;
}
else
{
return v_suppressElabErrors_630_;
}
}
}
}
else
{
uint8_t v___x_654_; 
v___x_654_ = 0;
return v___x_654_;
}
}
default: 
{
uint8_t v___x_655_; 
v___x_655_ = 0;
return v___x_655_;
}
}
}
case 0:
{
lean_object* v_str_656_; lean_object* v___x_657_; uint8_t v___x_658_; 
v_str_656_ = lean_ctor_get(v_x_631_, 1);
v___x_657_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__7));
v___x_658_ = lean_string_dec_eq(v_str_656_, v___x_657_);
if (v___x_658_ == 0)
{
return v___x_658_;
}
else
{
return v_suppressElabErrors_630_;
}
}
default: 
{
uint8_t v___x_659_; 
v___x_659_ = 0;
return v___x_659_;
}
}
}
else
{
uint8_t v___x_660_; 
v___x_660_ = 0;
return v___x_660_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___boxed(lean_object* v_suppressElabErrors_661_, lean_object* v_x_662_){
_start:
{
uint8_t v_suppressElabErrors_boxed_663_; uint8_t v_res_664_; lean_object* v_r_665_; 
v_suppressElabErrors_boxed_663_ = lean_unbox(v_suppressElabErrors_661_);
v_res_664_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0(v_suppressElabErrors_boxed_663_, v_x_662_);
lean_dec(v_x_662_);
v_r_665_ = lean_box(v_res_664_);
return v_r_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44_spec__46_spec__49(lean_object* v_msgData_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
lean_object* v___x_672_; lean_object* v_env_673_; uint8_t v___x_674_; lean_object* v_env_675_; lean_object* v___x_676_; lean_object* v_toCold_677_; lean_object* v_mctx_678_; lean_object* v_lctx_679_; lean_object* v_options_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_672_ = lean_st_ref_get(v___y_670_);
v_env_673_ = lean_ctor_get(v___x_672_, 0);
lean_inc_ref(v_env_673_);
lean_dec(v___x_672_);
v___x_674_ = 0;
v_env_675_ = l_Lean_Environment_setRecordingDeps(v_env_673_, v___x_674_);
v___x_676_ = lean_st_ref_get(v___y_668_);
v_toCold_677_ = lean_ctor_get(v___y_669_, 0);
v_mctx_678_ = lean_ctor_get(v___x_676_, 0);
lean_inc_ref(v_mctx_678_);
lean_dec(v___x_676_);
v_lctx_679_ = lean_ctor_get(v___y_667_, 2);
v_options_680_ = lean_ctor_get(v_toCold_677_, 2);
lean_inc_ref(v_options_680_);
lean_inc_ref(v_lctx_679_);
v___x_681_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_681_, 0, v_env_675_);
lean_ctor_set(v___x_681_, 1, v_mctx_678_);
lean_ctor_set(v___x_681_, 2, v_lctx_679_);
lean_ctor_set(v___x_681_, 3, v_options_680_);
v___x_682_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_682_, 0, v___x_681_);
lean_ctor_set(v___x_682_, 1, v_msgData_666_);
v___x_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_683_, 0, v___x_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44_spec__46_spec__49___boxed(lean_object* v_msgData_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44_spec__46_spec__49(v_msgData_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44_spec__46(lean_object* v_ref_692_, lean_object* v_msgData_693_, uint8_t v_severity_694_, uint8_t v_isSilent_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v___y_705_; uint8_t v___y_706_; uint8_t v___y_707_; lean_object* v___y_708_; lean_object* v_toCold_709_; lean_object* v___y_710_; lean_object* v___y_739_; lean_object* v___y_740_; uint8_t v___y_741_; uint8_t v___y_742_; lean_object* v___y_743_; lean_object* v___y_744_; uint8_t v___y_745_; lean_object* v___y_746_; lean_object* v___y_766_; uint8_t v___y_767_; lean_object* v___y_768_; uint8_t v___y_769_; uint8_t v___y_770_; lean_object* v___y_771_; lean_object* v___y_772_; uint8_t v___y_776_; uint8_t v___y_777_; uint8_t v___x_787_; uint8_t v___y_789_; uint8_t v___x_795_; 
v___x_787_ = 2;
v___x_795_ = l_Lean_instBEqMessageSeverity_beq(v_severity_694_, v___x_787_);
if (v___x_795_ == 0)
{
v___y_789_ = v___x_795_;
goto v___jp_788_;
}
else
{
uint8_t v___x_796_; 
lean_inc_ref(v_msgData_693_);
v___x_796_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_693_);
if (v___x_796_ == 0)
{
v___y_789_ = v___x_796_;
goto v___jp_788_;
}
else
{
lean_object* v___x_797_; lean_object* v___x_798_; 
lean_dec_ref(v_msgData_693_);
v___x_797_ = lean_box(0);
v___x_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
return v___x_798_;
}
}
v___jp_701_:
{
lean_object* v_currNamespace_711_; lean_object* v_openDecls_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v_env_717_; lean_object* v_nextMacroScope_718_; lean_object* v_ngen_719_; lean_object* v_auxDeclNGen_720_; lean_object* v_traceState_721_; lean_object* v_cache_722_; lean_object* v_recordedDeps_723_; lean_object* v_messages_724_; lean_object* v_infoState_725_; lean_object* v_snapshotTasks_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_737_; 
v_currNamespace_711_ = lean_ctor_get(v_toCold_709_, 4);
v_openDecls_712_ = lean_ctor_get(v_toCold_709_, 5);
lean_inc(v_openDecls_712_);
lean_inc(v_currNamespace_711_);
v___x_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_713_, 0, v_currNamespace_711_);
lean_ctor_set(v___x_713_, 1, v_openDecls_712_);
v___x_714_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
lean_ctor_set(v___x_714_, 1, v___y_708_);
lean_inc_ref(v___y_704_);
lean_inc_ref(v___y_703_);
v___x_715_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_715_, 0, v___y_703_);
lean_ctor_set(v___x_715_, 1, v___y_705_);
lean_ctor_set(v___x_715_, 2, v___y_702_);
lean_ctor_set(v___x_715_, 3, v___y_704_);
lean_ctor_set(v___x_715_, 4, v___x_714_);
lean_ctor_set_uint8(v___x_715_, sizeof(void*)*5, v___y_707_);
lean_ctor_set_uint8(v___x_715_, sizeof(void*)*5 + 1, v___y_706_);
lean_ctor_set_uint8(v___x_715_, sizeof(void*)*5 + 2, v_isSilent_695_);
v___x_716_ = lean_st_ref_take(v___y_710_);
v_env_717_ = lean_ctor_get(v___x_716_, 0);
v_nextMacroScope_718_ = lean_ctor_get(v___x_716_, 1);
v_ngen_719_ = lean_ctor_get(v___x_716_, 2);
v_auxDeclNGen_720_ = lean_ctor_get(v___x_716_, 3);
v_traceState_721_ = lean_ctor_get(v___x_716_, 4);
v_cache_722_ = lean_ctor_get(v___x_716_, 5);
v_recordedDeps_723_ = lean_ctor_get(v___x_716_, 6);
v_messages_724_ = lean_ctor_get(v___x_716_, 7);
v_infoState_725_ = lean_ctor_get(v___x_716_, 8);
v_snapshotTasks_726_ = lean_ctor_get(v___x_716_, 9);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_737_ == 0)
{
v___x_728_ = v___x_716_;
v_isShared_729_ = v_isSharedCheck_737_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_snapshotTasks_726_);
lean_inc(v_infoState_725_);
lean_inc(v_messages_724_);
lean_inc(v_recordedDeps_723_);
lean_inc(v_cache_722_);
lean_inc(v_traceState_721_);
lean_inc(v_auxDeclNGen_720_);
lean_inc(v_ngen_719_);
lean_inc(v_nextMacroScope_718_);
lean_inc(v_env_717_);
lean_dec(v___x_716_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_737_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_733_; 
v___x_730_ = lean_box(0);
v___x_731_ = l_Lean_MessageLog_add(v___x_715_, v_messages_724_);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 7, v___x_731_);
v___x_733_ = v___x_728_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_env_717_);
lean_ctor_set(v_reuseFailAlloc_736_, 1, v_nextMacroScope_718_);
lean_ctor_set(v_reuseFailAlloc_736_, 2, v_ngen_719_);
lean_ctor_set(v_reuseFailAlloc_736_, 3, v_auxDeclNGen_720_);
lean_ctor_set(v_reuseFailAlloc_736_, 4, v_traceState_721_);
lean_ctor_set(v_reuseFailAlloc_736_, 5, v_cache_722_);
lean_ctor_set(v_reuseFailAlloc_736_, 6, v_recordedDeps_723_);
lean_ctor_set(v_reuseFailAlloc_736_, 7, v___x_731_);
lean_ctor_set(v_reuseFailAlloc_736_, 8, v_infoState_725_);
lean_ctor_set(v_reuseFailAlloc_736_, 9, v_snapshotTasks_726_);
v___x_733_ = v_reuseFailAlloc_736_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = lean_st_ref_put(v___y_710_, v___x_733_);
v___x_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_735_, 0, v___x_730_);
return v___x_735_;
}
}
}
v___jp_738_:
{
lean_object* v_fileName_747_; lean_object* v_fileMap_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_764_; 
v_fileName_747_ = lean_ctor_get(v___y_744_, 0);
v_fileMap_748_ = lean_ctor_get(v___y_744_, 1);
v___x_749_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_693_);
v___x_750_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44_spec__46_spec__49(v___x_749_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
v_a_751_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_764_ == 0)
{
v___x_753_ = v___x_750_;
v_isShared_754_ = v_isSharedCheck_764_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_750_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_764_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
lean_inc_ref_n(v_fileMap_748_, 2);
v___x_755_ = l_Lean_FileMap_toPosition(v_fileMap_748_, v___y_743_);
lean_dec(v___y_743_);
v___x_756_ = l_Lean_FileMap_toPosition(v_fileMap_748_, v___y_746_);
lean_dec(v___y_746_);
v___x_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
v___x_758_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44_spec__46___closed__0));
if (v___y_741_ == 0)
{
lean_del_object(v___x_753_);
lean_dec_ref(v___y_739_);
v___y_702_ = v___x_757_;
v___y_703_ = v_fileName_747_;
v___y_704_ = v___x_758_;
v___y_705_ = v___x_755_;
v___y_706_ = v___y_742_;
v___y_707_ = v___y_745_;
v___y_708_ = v_a_751_;
v_toCold_709_ = v___y_740_;
v___y_710_ = v___y_699_;
goto v___jp_701_;
}
else
{
uint8_t v___x_759_; 
lean_inc(v_a_751_);
v___x_759_ = l_Lean_MessageData_hasTag(v___y_739_, v_a_751_);
if (v___x_759_ == 0)
{
lean_object* v___x_760_; lean_object* v___x_762_; 
lean_dec_ref_known(v___x_757_, 1);
lean_dec_ref(v___x_755_);
lean_dec(v_a_751_);
v___x_760_ = lean_box(0);
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 0, v___x_760_);
v___x_762_ = v___x_753_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_760_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
else
{
lean_del_object(v___x_753_);
v___y_702_ = v___x_757_;
v___y_703_ = v_fileName_747_;
v___y_704_ = v___x_758_;
v___y_705_ = v___x_755_;
v___y_706_ = v___y_742_;
v___y_707_ = v___y_745_;
v___y_708_ = v_a_751_;
v_toCold_709_ = v___y_740_;
v___y_710_ = v___y_699_;
goto v___jp_701_;
}
}
}
}
v___jp_765_:
{
lean_object* v___x_773_; 
v___x_773_ = l_Lean_Syntax_getTailPos_x3f(v___y_771_, v___y_770_);
lean_dec(v___y_771_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_inc(v___y_772_);
v___y_739_ = v___y_766_;
v___y_740_ = v___y_768_;
v___y_741_ = v___y_767_;
v___y_742_ = v___y_769_;
v___y_743_ = v___y_772_;
v___y_744_ = v___y_768_;
v___y_745_ = v___y_770_;
v___y_746_ = v___y_772_;
goto v___jp_738_;
}
else
{
lean_object* v_val_774_; 
v_val_774_ = lean_ctor_get(v___x_773_, 0);
lean_inc(v_val_774_);
lean_dec_ref_known(v___x_773_, 1);
v___y_739_ = v___y_766_;
v___y_740_ = v___y_768_;
v___y_741_ = v___y_767_;
v___y_742_ = v___y_769_;
v___y_743_ = v___y_772_;
v___y_744_ = v___y_768_;
v___y_745_ = v___y_770_;
v___y_746_ = v_val_774_;
goto v___jp_738_;
}
}
v___jp_775_:
{
lean_object* v_toCold_778_; lean_object* v_ref_779_; uint8_t v_suppressElabErrors_780_; lean_object* v___x_781_; lean_object* v___f_782_; lean_object* v_ref_783_; lean_object* v___x_784_; 
v_toCold_778_ = lean_ctor_get(v___y_698_, 0);
v_ref_779_ = lean_ctor_get(v___y_698_, 2);
v_suppressElabErrors_780_ = lean_ctor_get_uint8(v___y_698_, sizeof(void*)*3 + 2);
v___x_781_ = lean_box(v_suppressElabErrors_780_);
v___f_782_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___boxed), 2, 1);
lean_closure_set(v___f_782_, 0, v___x_781_);
v_ref_783_ = l_Lean_replaceRef(v_ref_692_, v_ref_779_);
v___x_784_ = l_Lean_Syntax_getPos_x3f(v_ref_783_, v___y_776_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v___x_785_; 
v___x_785_ = lean_unsigned_to_nat(0u);
v___y_766_ = v___f_782_;
v___y_767_ = v_suppressElabErrors_780_;
v___y_768_ = v_toCold_778_;
v___y_769_ = v___y_777_;
v___y_770_ = v___y_776_;
v___y_771_ = v_ref_783_;
v___y_772_ = v___x_785_;
goto v___jp_765_;
}
else
{
lean_object* v_val_786_; 
v_val_786_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_val_786_);
lean_dec_ref_known(v___x_784_, 1);
v___y_766_ = v___f_782_;
v___y_767_ = v_suppressElabErrors_780_;
v___y_768_ = v_toCold_778_;
v___y_769_ = v___y_777_;
v___y_770_ = v___y_776_;
v___y_771_ = v_ref_783_;
v___y_772_ = v_val_786_;
goto v___jp_765_;
}
}
v___jp_788_:
{
uint8_t v___x_790_; uint8_t v___x_791_; 
v___x_790_ = 1;
v___x_791_ = l_Lean_instBEqMessageSeverity_beq(v_severity_694_, v___x_790_);
if (v___x_791_ == 0)
{
v___y_776_ = v___y_789_;
v___y_777_ = v_severity_694_;
goto v___jp_775_;
}
else
{
lean_object* v___x_792_; lean_object* v___x_793_; uint8_t v___x_794_; 
v___x_792_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_698_);
v___x_793_ = l_Lean_warningAsError;
v___x_794_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5(v___x_792_, v___x_793_);
lean_dec_ref(v___x_792_);
if (v___x_794_ == 0)
{
v___y_776_ = v___y_789_;
v___y_777_ = v_severity_694_;
goto v___jp_775_;
}
else
{
v___y_776_ = v___y_789_;
v___y_777_ = v___x_787_;
goto v___jp_775_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44_spec__46___boxed(lean_object* v_ref_799_, lean_object* v_msgData_800_, lean_object* v_severity_801_, lean_object* v_isSilent_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
uint8_t v_severity_boxed_808_; uint8_t v_isSilent_boxed_809_; lean_object* v_res_810_; 
v_severity_boxed_808_ = lean_unbox(v_severity_801_);
v_isSilent_boxed_809_ = lean_unbox(v_isSilent_802_);
v_res_810_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44_spec__46(v_ref_799_, v_msgData_800_, v_severity_boxed_808_, v_isSilent_boxed_809_, v___y_803_, v___y_804_, v___y_805_, v___y_806_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v_ref_799_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44(lean_object* v_msgData_811_, uint8_t v_severity_812_, uint8_t v_isSilent_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
lean_object* v_ref_819_; lean_object* v___x_820_; 
v_ref_819_ = lean_ctor_get(v___y_816_, 2);
v___x_820_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44_spec__46(v_ref_819_, v_msgData_811_, v_severity_812_, v_isSilent_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44___boxed(lean_object* v_msgData_821_, lean_object* v_severity_822_, lean_object* v_isSilent_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
uint8_t v_severity_boxed_829_; uint8_t v_isSilent_boxed_830_; lean_object* v_res_831_; 
v_severity_boxed_829_ = lean_unbox(v_severity_822_);
v_isSilent_boxed_830_ = lean_unbox(v_isSilent_823_);
v_res_831_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44(v_msgData_821_, v_severity_boxed_829_, v_isSilent_boxed_830_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40(lean_object* v_msgData_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
uint8_t v___x_838_; uint8_t v___x_839_; lean_object* v___x_840_; 
v___x_838_ = 1;
v___x_839_ = 0;
v___x_840_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44(v_msgData_832_, v___x_838_, v___x_839_, v___y_833_, v___y_834_, v___y_835_, v___y_836_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40___boxed(lean_object* v_msgData_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40(v_msgData_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
return v_res_847_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34___closed__1(void){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34___closed__0));
v___x_850_ = l_Lean_stringToMessageData(v___x_849_);
return v___x_850_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34___closed__3(void){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_852_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34___closed__2));
v___x_853_ = l_Lean_stringToMessageData(v___x_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34(lean_object* v_id_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
lean_object* v___x_860_; lean_object* v_env_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_883_; 
v___x_860_ = lean_st_ref_get(v___y_858_);
v_env_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc_ref(v_env_861_);
lean_dec(v___x_860_);
v___x_862_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_863_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__39___redArg(v___x_862_, v___y_857_);
v_a_864_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_883_ == 0)
{
v___x_866_ = v___x_863_;
v_isShared_867_ = v_isSharedCheck_883_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_863_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_883_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
uint8_t v_isExporting_873_; 
v_isExporting_873_ = lean_ctor_get_uint8(v_env_861_, sizeof(void*)*13);
lean_dec_ref(v_env_861_);
if (v_isExporting_873_ == 0)
{
lean_dec(v_a_864_);
lean_dec(v_id_854_);
goto v___jp_868_;
}
else
{
uint8_t v___x_874_; 
v___x_874_ = l_Lean_isPrivateName(v_id_854_);
if (v___x_874_ == 0)
{
lean_dec(v_a_864_);
lean_dec(v_id_854_);
goto v___jp_868_;
}
else
{
uint8_t v___x_875_; 
v___x_875_ = lean_unbox(v_a_864_);
lean_dec(v_a_864_);
if (v___x_875_ == 0)
{
lean_dec(v_id_854_);
goto v___jp_868_;
}
else
{
lean_object* v___x_876_; uint8_t v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
lean_del_object(v___x_866_);
v___x_876_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34___closed__1);
v___x_877_ = 0;
v___x_878_ = l_Lean_MessageData_ofConstName(v_id_854_, v___x_877_);
v___x_879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_876_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
v___x_880_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34___closed__3);
v___x_881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_881_, 0, v___x_879_);
lean_ctor_set(v___x_881_, 1, v___x_880_);
v___x_882_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40(v___x_881_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
return v___x_882_;
}
}
}
v___jp_868_:
{
lean_object* v___x_869_; lean_object* v___x_871_; 
v___x_869_ = lean_box(0);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v___x_869_);
v___x_871_ = v___x_866_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_869_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34___boxed(lean_object* v_id_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34(v_id_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28(lean_object* v_id_891_, uint8_t v_enableLog_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
lean_object* v___x_898_; lean_object* v_toCold_899_; lean_object* v_env_900_; lean_object* v_currNamespace_901_; lean_object* v_openDecls_902_; lean_object* v___x_903_; lean_object* v_res_904_; lean_object* v___x_905_; 
v___x_898_ = lean_st_ref_get(v___y_896_);
v_toCold_899_ = lean_ctor_get(v___y_895_, 0);
v_env_900_ = lean_ctor_get(v___x_898_, 0);
lean_inc_ref(v_env_900_);
lean_dec(v___x_898_);
v_currNamespace_901_ = lean_ctor_get(v_toCold_899_, 4);
v_openDecls_902_ = lean_ctor_get(v_toCold_899_, 5);
v___x_903_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_895_);
lean_inc(v_openDecls_902_);
lean_inc(v_currNamespace_901_);
v_res_904_ = l_Lean_ResolveName_resolveGlobalName(v_env_900_, v___x_903_, v_currNamespace_901_, v_openDecls_902_, v_id_891_);
lean_dec_ref(v___x_903_);
v___x_905_ = lean_st_ref_get(v___y_896_);
if (v_enableLog_892_ == 0)
{
lean_object* v___x_906_; 
lean_dec(v___x_905_);
v___x_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_906_, 0, v_res_904_);
return v___x_906_;
}
else
{
lean_object* v_env_907_; uint8_t v_isExporting_908_; 
v_env_907_ = lean_ctor_get(v___x_905_, 0);
lean_inc_ref(v_env_907_);
lean_dec(v___x_905_);
v_isExporting_908_ = lean_ctor_get_uint8(v_env_907_, sizeof(void*)*13);
lean_dec_ref(v_env_907_);
if (v_isExporting_908_ == 0)
{
lean_object* v___x_909_; 
v___x_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_909_, 0, v_res_904_);
return v___x_909_;
}
else
{
lean_object* v___x_910_; 
v___x_910_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__33(v_res_904_);
if (lean_obj_tag(v___x_910_) == 1)
{
lean_object* v_val_911_; lean_object* v_fst_912_; lean_object* v___x_913_; 
v_val_911_ = lean_ctor_get(v___x_910_, 0);
lean_inc(v_val_911_);
lean_dec_ref_known(v___x_910_, 1);
v_fst_912_ = lean_ctor_get(v_val_911_, 0);
lean_inc(v_fst_912_);
lean_dec(v_val_911_);
v___x_913_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34(v_fst_912_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_920_; 
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_920_ == 0)
{
lean_object* v_unused_921_; 
v_unused_921_ = lean_ctor_get(v___x_913_, 0);
lean_dec(v_unused_921_);
v___x_915_ = v___x_913_;
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
else
{
lean_dec(v___x_913_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_918_; 
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 0, v_res_904_);
v___x_918_ = v___x_915_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_res_904_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
else
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
lean_dec(v_res_904_);
v_a_922_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_929_ == 0)
{
v___x_924_ = v___x_913_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_913_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_a_922_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
else
{
lean_object* v___x_930_; 
lean_dec(v___x_910_);
v___x_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_930_, 0, v_res_904_);
return v___x_930_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28___boxed(lean_object* v_id_931_, lean_object* v_enableLog_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
uint8_t v_enableLog_boxed_938_; lean_object* v_res_939_; 
v_enableLog_boxed_938_ = lean_unbox(v_enableLog_932_);
v_res_939_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28(v_id_931_, v_enableLog_boxed_938_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
return v_res_939_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__29(lean_object* v_snd_940_, lean_object* v_x_941_){
_start:
{
if (lean_obj_tag(v_x_941_) == 0)
{
uint8_t v___x_942_; 
v___x_942_ = 0;
return v___x_942_;
}
else
{
lean_object* v_head_943_; lean_object* v_tail_944_; lean_object* v_snd_945_; lean_object* v___x_946_; lean_object* v___x_947_; uint8_t v___x_948_; 
v_head_943_ = lean_ctor_get(v_x_941_, 0);
v_tail_944_ = lean_ctor_get(v_x_941_, 1);
v_snd_945_ = lean_ctor_get(v_head_943_, 1);
v___x_946_ = l_List_lengthTR___redArg(v_snd_945_);
v___x_947_ = l_List_lengthTR___redArg(v_snd_940_);
v___x_948_ = lean_nat_dec_lt(v___x_946_, v___x_947_);
lean_dec(v___x_947_);
lean_dec(v___x_946_);
if (v___x_948_ == 0)
{
v_x_941_ = v_tail_944_;
goto _start;
}
else
{
return v___x_948_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__29___boxed(lean_object* v_snd_950_, lean_object* v_x_951_){
_start:
{
uint8_t v_res_952_; lean_object* v_r_953_; 
v_res_952_ = l_List_any___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__29(v_snd_950_, v_x_951_);
lean_dec(v_x_951_);
lean_dec(v_snd_950_);
v_r_953_ = lean_box(v_res_952_);
return v_r_953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22(lean_object* v_view_954_, lean_object* v_findLocalDecl_x3f_955_, lean_object* v_n_956_, lean_object* v_projs_957_, lean_object* v_auxDecl_x3f_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v_auxDecl_x3f_972_; lean_object* v_imported_1003_; lean_object* v_ctx_1004_; lean_object* v_scopes_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v_imported_1003_ = lean_ctor_get(v_view_954_, 1);
v_ctx_1004_ = lean_ctor_get(v_view_954_, 2);
v_scopes_1005_ = lean_ctor_get(v_view_954_, 3);
lean_inc(v_scopes_1005_);
lean_inc(v_ctx_1004_);
lean_inc(v_imported_1003_);
lean_inc(v_n_956_);
v___x_1006_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1006_, 0, v_n_956_);
lean_ctor_set(v___x_1006_, 1, v_imported_1003_);
lean_ctor_set(v___x_1006_, 2, v_ctx_1004_);
lean_ctor_set(v___x_1006_, 3, v_scopes_1005_);
lean_inc_ref(v_findLocalDecl_x3f_955_);
v___x_1007_ = lean_apply_1(v_findLocalDecl_x3f_955_, v___x_1006_);
if (lean_obj_tag(v___x_1007_) == 1)
{
lean_object* v_val_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1023_; 
v_val_1008_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1010_ = v___x_1007_;
v_isShared_1011_ = v_isSharedCheck_1023_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_val_1008_);
lean_dec(v___x_1007_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1023_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
uint8_t v___x_1012_; 
v___x_1012_ = l_Lean_LocalDecl_isAuxDecl(v_val_1008_);
if (v___x_1012_ == 0)
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1016_; 
lean_dec(v_auxDecl_x3f_958_);
lean_dec(v_n_956_);
lean_dec_ref(v_findLocalDecl_x3f_955_);
lean_dec_ref(v_view_954_);
v___x_1013_ = l_Lean_LocalDecl_toExpr(v_val_1008_);
v___x_1014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
lean_ctor_set(v___x_1014_, 1, v_projs_957_);
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 0, v___x_1014_);
v___x_1016_ = v___x_1010_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1014_);
v___x_1016_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
lean_object* v___x_1017_; 
v___x_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
return v___x_1017_;
}
}
else
{
if (lean_obj_tag(v_auxDecl_x3f_958_) == 0)
{
lean_object* v___x_1019_; lean_object* v___x_1021_; 
lean_inc(v_projs_957_);
v___x_1019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1019_, 0, v_val_1008_);
lean_ctor_set(v___x_1019_, 1, v_projs_957_);
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 0, v___x_1019_);
v___x_1021_ = v___x_1010_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v___x_1019_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
v_auxDecl_x3f_972_ = v___x_1021_;
goto v___jp_971_;
}
}
else
{
lean_del_object(v___x_1010_);
lean_dec(v_val_1008_);
v_auxDecl_x3f_972_ = v_auxDecl_x3f_958_;
goto v___jp_971_;
}
}
}
}
else
{
lean_dec(v___x_1007_);
v_auxDecl_x3f_972_ = v_auxDecl_x3f_958_;
goto v___jp_971_;
}
v___jp_964_:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_967_ = l_Lean_LocalDecl_toExpr(v___y_966_);
v___x_968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
lean_ctor_set(v___x_968_, 1, v___y_965_);
v___x_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
v___x_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_970_, 0, v___x_969_);
return v___x_970_;
}
v___jp_971_:
{
if (lean_obj_tag(v_n_956_) == 1)
{
lean_object* v_pre_973_; lean_object* v_str_974_; lean_object* v___x_975_; 
v_pre_973_ = lean_ctor_get(v_n_956_, 0);
lean_inc(v_pre_973_);
v_str_974_ = lean_ctor_get(v_n_956_, 1);
lean_inc_ref(v_str_974_);
lean_dec_ref_known(v_n_956_, 2);
v___x_975_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_975_, 0, v_str_974_);
lean_ctor_set(v___x_975_, 1, v_projs_957_);
v_n_956_ = v_pre_973_;
v_projs_957_ = v___x_975_;
v_auxDecl_x3f_958_ = v_auxDecl_x3f_972_;
goto _start;
}
else
{
lean_dec(v_projs_957_);
lean_dec(v_n_956_);
lean_dec_ref(v_findLocalDecl_x3f_955_);
if (lean_obj_tag(v_auxDecl_x3f_972_) == 1)
{
lean_object* v_val_977_; lean_object* v_fst_978_; lean_object* v_snd_979_; uint8_t v___x_980_; 
v_val_977_ = lean_ctor_get(v_auxDecl_x3f_972_, 0);
lean_inc(v_val_977_);
lean_dec_ref_known(v_auxDecl_x3f_972_, 1);
v_fst_978_ = lean_ctor_get(v_val_977_, 0);
lean_inc(v_fst_978_);
v_snd_979_ = lean_ctor_get(v_val_977_, 1);
lean_inc(v_snd_979_);
lean_dec(v_val_977_);
v___x_980_ = l_List_isEmpty___redArg(v_snd_979_);
if (v___x_980_ == 0)
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = l_Lean_MacroScopesView_review(v_view_954_);
v___x_982_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28(v___x_981_, v___x_980_, v___y_959_, v___y_960_, v___y_961_, v___y_962_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_992_; 
v_a_983_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_992_ == 0)
{
v___x_985_ = v___x_982_;
v_isShared_986_ = v_isSharedCheck_992_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_982_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_992_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
uint8_t v___x_987_; 
v___x_987_ = l_List_any___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__29(v_snd_979_, v_a_983_);
lean_dec(v_a_983_);
if (v___x_987_ == 0)
{
lean_del_object(v___x_985_);
v___y_965_ = v_snd_979_;
v___y_966_ = v_fst_978_;
goto v___jp_964_;
}
else
{
lean_object* v___x_988_; lean_object* v___x_990_; 
lean_dec(v_snd_979_);
lean_dec(v_fst_978_);
v___x_988_ = lean_box(0);
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 0, v___x_988_);
v___x_990_ = v___x_985_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_988_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
else
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
lean_dec(v_snd_979_);
lean_dec(v_fst_978_);
v_a_993_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_995_ = v___x_982_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_982_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_993_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
else
{
lean_dec_ref(v_view_954_);
v___y_965_ = v_snd_979_;
v___y_966_ = v_fst_978_;
goto v___jp_964_;
}
}
else
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
lean_dec(v_auxDecl_x3f_972_);
lean_dec_ref(v_view_954_);
v___x_1001_ = lean_box(0);
v___x_1002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1001_);
return v___x_1002_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22___boxed(lean_object* v_view_1024_, lean_object* v_findLocalDecl_x3f_1025_, lean_object* v_n_1026_, lean_object* v_projs_1027_, lean_object* v_auxDecl_x3f_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22(v_view_1024_, v_findLocalDecl_x3f_1025_, v_n_1026_, v_projs_1027_, v_auxDecl_x3f_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13(lean_object* v_n_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v_lctx_1041_; lean_object* v_toCold_1042_; lean_object* v_decls_1043_; lean_object* v_auxDeclToFullName_1044_; lean_object* v_currNamespace_1045_; lean_object* v_view_1046_; lean_object* v_name_1047_; lean_object* v_findLocalDecl_x3f_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v_lctx_1041_ = lean_ctor_get(v___y_1036_, 2);
v_toCold_1042_ = lean_ctor_get(v___y_1038_, 0);
v_decls_1043_ = lean_ctor_get(v_lctx_1041_, 1);
v_auxDeclToFullName_1044_ = lean_ctor_get(v_lctx_1041_, 2);
v_currNamespace_1045_ = lean_ctor_get(v_toCold_1042_, 4);
v_view_1046_ = l_Lean_extractMacroScopes(v_n_1035_);
v_name_1047_ = lean_ctor_get(v_view_1046_, 0);
lean_inc(v_name_1047_);
lean_inc_ref(v_decls_1043_);
lean_inc(v_currNamespace_1045_);
lean_inc(v_auxDeclToFullName_1044_);
v_findLocalDecl_x3f_1048_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13___lam__0___boxed), 4, 3);
lean_closure_set(v_findLocalDecl_x3f_1048_, 0, v_auxDeclToFullName_1044_);
lean_closure_set(v_findLocalDecl_x3f_1048_, 1, v_currNamespace_1045_);
lean_closure_set(v_findLocalDecl_x3f_1048_, 2, v_decls_1043_);
v___x_1049_ = lean_box(0);
v___x_1050_ = lean_box(0);
v___x_1051_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22(v_view_1046_, v_findLocalDecl_x3f_1048_, v_name_1047_, v___x_1049_, v___x_1050_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13___boxed(lean_object* v_n_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13(v_n_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6___lam__0(uint8_t v___x_1059_, lean_object* v_n_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
lean_object* v___x_1066_; 
v___x_1066_ = l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13(v_n_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1080_; 
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1069_ = v___x_1066_;
v_isShared_1070_ = v_isSharedCheck_1080_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v___x_1066_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1080_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
if (lean_obj_tag(v_a_1067_) == 0)
{
uint8_t v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1074_; 
v___x_1071_ = 1;
v___x_1072_ = lean_box(v___x_1071_);
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 0, v___x_1072_);
v___x_1074_ = v___x_1069_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1072_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
else
{
lean_object* v___x_1076_; lean_object* v___x_1078_; 
lean_dec_ref_known(v_a_1067_, 1);
v___x_1076_ = lean_box(v___x_1059_);
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 0, v___x_1076_);
v___x_1078_ = v___x_1069_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1076_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
else
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1088_; 
v_a_1081_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1083_ = v___x_1066_;
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1066_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1086_; 
if (v_isShared_1084_ == 0)
{
v___x_1086_ = v___x_1083_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1081_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6___lam__0___boxed(lean_object* v___x_1089_, lean_object* v_n_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
uint8_t v___x_45385__boxed_1096_; lean_object* v_res_1097_; 
v___x_45385__boxed_1096_ = lean_unbox(v___x_1089_);
v_res_1097_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6___lam__0(v___x_45385__boxed_1096_, v_n_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__24___lam__0(lean_object* v___x_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
lean_object* v___x_1104_; 
v___x_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1098_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__24___lam__0___boxed(lean_object* v___x_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__24___lam__0(v___x_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46_spec__48_spec__50(lean_object* v_ref_1114_, lean_object* v_msgData_1115_, uint8_t v_severity_1116_, uint8_t v_isSilent_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_){
_start:
{
lean_object* v_a_1124_; lean_object* v___y_1128_; lean_object* v___y_1129_; lean_object* v___y_1130_; uint8_t v___y_1131_; lean_object* v___y_1132_; uint8_t v___y_1133_; lean_object* v___y_1134_; lean_object* v_toCold_1135_; lean_object* v___y_1136_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; uint8_t v___y_1167_; lean_object* v___y_1168_; uint8_t v___y_1169_; uint8_t v___y_1170_; lean_object* v___y_1171_; uint8_t v___y_1190_; lean_object* v___y_1191_; lean_object* v___y_1192_; uint8_t v___y_1193_; uint8_t v___y_1194_; lean_object* v___y_1195_; lean_object* v___y_1196_; uint8_t v___y_1200_; uint8_t v___y_1201_; uint8_t v___x_1211_; uint8_t v___y_1213_; uint8_t v___x_1219_; 
v___x_1211_ = 2;
v___x_1219_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1116_, v___x_1211_);
if (v___x_1219_ == 0)
{
v___y_1213_ = v___x_1219_;
goto v___jp_1212_;
}
else
{
uint8_t v___x_1220_; 
lean_inc_ref(v_msgData_1115_);
v___x_1220_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1115_);
if (v___x_1220_ == 0)
{
v___y_1213_ = v___x_1220_;
goto v___jp_1212_;
}
else
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
lean_dec_ref(v_msgData_1115_);
v___x_1221_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46_spec__48_spec__50___closed__0));
v___x_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
return v___x_1222_;
}
}
v___jp_1123_:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1125_, 0, v_a_1124_);
v___x_1126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1125_);
return v___x_1126_;
}
v___jp_1127_:
{
lean_object* v_currNamespace_1137_; lean_object* v_openDecls_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v_env_1143_; lean_object* v_nextMacroScope_1144_; lean_object* v_ngen_1145_; lean_object* v_auxDeclNGen_1146_; lean_object* v_traceState_1147_; lean_object* v_cache_1148_; lean_object* v_recordedDeps_1149_; lean_object* v_messages_1150_; lean_object* v_infoState_1151_; lean_object* v_snapshotTasks_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1162_; 
v_currNamespace_1137_ = lean_ctor_get(v_toCold_1135_, 4);
v_openDecls_1138_ = lean_ctor_get(v_toCold_1135_, 5);
lean_inc(v_openDecls_1138_);
lean_inc(v_currNamespace_1137_);
v___x_1139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1139_, 0, v_currNamespace_1137_);
lean_ctor_set(v___x_1139_, 1, v_openDecls_1138_);
v___x_1140_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1139_);
lean_ctor_set(v___x_1140_, 1, v___y_1134_);
lean_inc_ref(v___y_1128_);
lean_inc_ref(v___y_1129_);
v___x_1141_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1141_, 0, v___y_1129_);
lean_ctor_set(v___x_1141_, 1, v___y_1132_);
lean_ctor_set(v___x_1141_, 2, v___y_1130_);
lean_ctor_set(v___x_1141_, 3, v___y_1128_);
lean_ctor_set(v___x_1141_, 4, v___x_1140_);
lean_ctor_set_uint8(v___x_1141_, sizeof(void*)*5, v___y_1133_);
lean_ctor_set_uint8(v___x_1141_, sizeof(void*)*5 + 1, v___y_1131_);
lean_ctor_set_uint8(v___x_1141_, sizeof(void*)*5 + 2, v_isSilent_1117_);
v___x_1142_ = lean_st_ref_take(v___y_1136_);
v_env_1143_ = lean_ctor_get(v___x_1142_, 0);
v_nextMacroScope_1144_ = lean_ctor_get(v___x_1142_, 1);
v_ngen_1145_ = lean_ctor_get(v___x_1142_, 2);
v_auxDeclNGen_1146_ = lean_ctor_get(v___x_1142_, 3);
v_traceState_1147_ = lean_ctor_get(v___x_1142_, 4);
v_cache_1148_ = lean_ctor_get(v___x_1142_, 5);
v_recordedDeps_1149_ = lean_ctor_get(v___x_1142_, 6);
v_messages_1150_ = lean_ctor_get(v___x_1142_, 7);
v_infoState_1151_ = lean_ctor_get(v___x_1142_, 8);
v_snapshotTasks_1152_ = lean_ctor_get(v___x_1142_, 9);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1154_ = v___x_1142_;
v_isShared_1155_ = v_isSharedCheck_1162_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_snapshotTasks_1152_);
lean_inc(v_infoState_1151_);
lean_inc(v_messages_1150_);
lean_inc(v_recordedDeps_1149_);
lean_inc(v_cache_1148_);
lean_inc(v_traceState_1147_);
lean_inc(v_auxDeclNGen_1146_);
lean_inc(v_ngen_1145_);
lean_inc(v_nextMacroScope_1144_);
lean_inc(v_env_1143_);
lean_dec(v___x_1142_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1162_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1159_; 
v___x_1156_ = lean_box(0);
v___x_1157_ = l_Lean_MessageLog_add(v___x_1141_, v_messages_1150_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 7, v___x_1157_);
v___x_1159_ = v___x_1154_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_env_1143_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v_nextMacroScope_1144_);
lean_ctor_set(v_reuseFailAlloc_1161_, 2, v_ngen_1145_);
lean_ctor_set(v_reuseFailAlloc_1161_, 3, v_auxDeclNGen_1146_);
lean_ctor_set(v_reuseFailAlloc_1161_, 4, v_traceState_1147_);
lean_ctor_set(v_reuseFailAlloc_1161_, 5, v_cache_1148_);
lean_ctor_set(v_reuseFailAlloc_1161_, 6, v_recordedDeps_1149_);
lean_ctor_set(v_reuseFailAlloc_1161_, 7, v___x_1157_);
lean_ctor_set(v_reuseFailAlloc_1161_, 8, v_infoState_1151_);
lean_ctor_set(v_reuseFailAlloc_1161_, 9, v_snapshotTasks_1152_);
v___x_1159_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
lean_object* v___x_1160_; 
v___x_1160_ = lean_st_ref_put(v___y_1136_, v___x_1159_);
v_a_1124_ = v___x_1156_;
goto v___jp_1123_;
}
}
}
v___jp_1163_:
{
lean_object* v_fileName_1172_; lean_object* v_fileMap_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1188_; 
v_fileName_1172_ = lean_ctor_get(v___y_1168_, 0);
v_fileMap_1173_ = lean_ctor_get(v___y_1168_, 1);
v___x_1174_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1115_);
v___x_1175_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44_spec__46_spec__49(v___x_1174_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1178_ = v___x_1175_;
v_isShared_1179_ = v_isSharedCheck_1188_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1175_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1188_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1183_; 
lean_inc_ref_n(v_fileMap_1173_, 2);
v___x_1180_ = l_Lean_FileMap_toPosition(v_fileMap_1173_, v___y_1166_);
lean_dec(v___y_1166_);
v___x_1181_ = l_Lean_FileMap_toPosition(v_fileMap_1173_, v___y_1171_);
lean_dec(v___y_1171_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set_tag(v___x_1178_, 1);
lean_ctor_set(v___x_1178_, 0, v___x_1181_);
v___x_1183_ = v___x_1178_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___x_1181_);
v___x_1183_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
lean_object* v___x_1184_; 
v___x_1184_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44_spec__46___closed__0));
if (v___y_1167_ == 0)
{
lean_dec_ref(v___y_1164_);
v___y_1128_ = v___x_1184_;
v___y_1129_ = v_fileName_1172_;
v___y_1130_ = v___x_1183_;
v___y_1131_ = v___y_1169_;
v___y_1132_ = v___x_1180_;
v___y_1133_ = v___y_1170_;
v___y_1134_ = v_a_1176_;
v_toCold_1135_ = v___y_1165_;
v___y_1136_ = v___y_1121_;
goto v___jp_1127_;
}
else
{
uint8_t v___x_1185_; 
lean_inc(v_a_1176_);
v___x_1185_ = l_Lean_MessageData_hasTag(v___y_1164_, v_a_1176_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1186_; 
lean_dec_ref(v___x_1183_);
lean_dec_ref(v___x_1180_);
lean_dec(v_a_1176_);
v___x_1186_ = lean_box(0);
v_a_1124_ = v___x_1186_;
goto v___jp_1123_;
}
else
{
v___y_1128_ = v___x_1184_;
v___y_1129_ = v_fileName_1172_;
v___y_1130_ = v___x_1183_;
v___y_1131_ = v___y_1169_;
v___y_1132_ = v___x_1180_;
v___y_1133_ = v___y_1170_;
v___y_1134_ = v_a_1176_;
v_toCold_1135_ = v___y_1165_;
v___y_1136_ = v___y_1121_;
goto v___jp_1127_;
}
}
}
}
}
v___jp_1189_:
{
lean_object* v___x_1197_; 
v___x_1197_ = l_Lean_Syntax_getTailPos_x3f(v___y_1195_, v___y_1194_);
lean_dec(v___y_1195_);
if (lean_obj_tag(v___x_1197_) == 0)
{
lean_inc(v___y_1196_);
v___y_1164_ = v___y_1191_;
v___y_1165_ = v___y_1192_;
v___y_1166_ = v___y_1196_;
v___y_1167_ = v___y_1190_;
v___y_1168_ = v___y_1192_;
v___y_1169_ = v___y_1193_;
v___y_1170_ = v___y_1194_;
v___y_1171_ = v___y_1196_;
goto v___jp_1163_;
}
else
{
lean_object* v_val_1198_; 
v_val_1198_ = lean_ctor_get(v___x_1197_, 0);
lean_inc(v_val_1198_);
lean_dec_ref_known(v___x_1197_, 1);
v___y_1164_ = v___y_1191_;
v___y_1165_ = v___y_1192_;
v___y_1166_ = v___y_1196_;
v___y_1167_ = v___y_1190_;
v___y_1168_ = v___y_1192_;
v___y_1169_ = v___y_1193_;
v___y_1170_ = v___y_1194_;
v___y_1171_ = v_val_1198_;
goto v___jp_1163_;
}
}
v___jp_1199_:
{
lean_object* v_toCold_1202_; lean_object* v_ref_1203_; uint8_t v_suppressElabErrors_1204_; lean_object* v___x_1205_; lean_object* v___f_1206_; lean_object* v_ref_1207_; lean_object* v___x_1208_; 
v_toCold_1202_ = lean_ctor_get(v___y_1120_, 0);
v_ref_1203_ = lean_ctor_get(v___y_1120_, 2);
v_suppressElabErrors_1204_ = lean_ctor_get_uint8(v___y_1120_, sizeof(void*)*3 + 2);
v___x_1205_ = lean_box(v_suppressElabErrors_1204_);
v___f_1206_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1206_, 0, v___x_1205_);
v_ref_1207_ = l_Lean_replaceRef(v_ref_1114_, v_ref_1203_);
v___x_1208_ = l_Lean_Syntax_getPos_x3f(v_ref_1207_, v___y_1200_);
if (lean_obj_tag(v___x_1208_) == 0)
{
lean_object* v___x_1209_; 
v___x_1209_ = lean_unsigned_to_nat(0u);
v___y_1190_ = v_suppressElabErrors_1204_;
v___y_1191_ = v___f_1206_;
v___y_1192_ = v_toCold_1202_;
v___y_1193_ = v___y_1201_;
v___y_1194_ = v___y_1200_;
v___y_1195_ = v_ref_1207_;
v___y_1196_ = v___x_1209_;
goto v___jp_1189_;
}
else
{
lean_object* v_val_1210_; 
v_val_1210_ = lean_ctor_get(v___x_1208_, 0);
lean_inc(v_val_1210_);
lean_dec_ref_known(v___x_1208_, 1);
v___y_1190_ = v_suppressElabErrors_1204_;
v___y_1191_ = v___f_1206_;
v___y_1192_ = v_toCold_1202_;
v___y_1193_ = v___y_1201_;
v___y_1194_ = v___y_1200_;
v___y_1195_ = v_ref_1207_;
v___y_1196_ = v_val_1210_;
goto v___jp_1189_;
}
}
v___jp_1212_:
{
uint8_t v___x_1214_; uint8_t v___x_1215_; 
v___x_1214_ = 1;
v___x_1215_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1116_, v___x_1214_);
if (v___x_1215_ == 0)
{
v___y_1200_ = v___y_1213_;
v___y_1201_ = v_severity_1116_;
goto v___jp_1199_;
}
else
{
lean_object* v___x_1216_; lean_object* v___x_1217_; uint8_t v___x_1218_; 
v___x_1216_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1120_);
v___x_1217_ = l_Lean_warningAsError;
v___x_1218_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5(v___x_1216_, v___x_1217_);
lean_dec_ref(v___x_1216_);
if (v___x_1218_ == 0)
{
v___y_1200_ = v___y_1213_;
v___y_1201_ = v_severity_1116_;
goto v___jp_1199_;
}
else
{
v___y_1200_ = v___y_1213_;
v___y_1201_ = v___x_1211_;
goto v___jp_1199_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46_spec__48_spec__50___boxed(lean_object* v_ref_1223_, lean_object* v_msgData_1224_, lean_object* v_severity_1225_, lean_object* v_isSilent_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
uint8_t v_severity_boxed_1232_; uint8_t v_isSilent_boxed_1233_; lean_object* v_res_1234_; 
v_severity_boxed_1232_ = lean_unbox(v_severity_1225_);
v_isSilent_boxed_1233_ = lean_unbox(v_isSilent_1226_);
v_res_1234_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46_spec__48_spec__50(v_ref_1223_, v_msgData_1224_, v_severity_boxed_1232_, v_isSilent_boxed_1233_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v_ref_1223_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46_spec__48(lean_object* v_msgData_1235_, uint8_t v_severity_1236_, uint8_t v_isSilent_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
lean_object* v_ref_1243_; lean_object* v___x_1244_; 
v_ref_1243_ = lean_ctor_get(v___y_1240_, 2);
v___x_1244_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46_spec__48_spec__50(v_ref_1243_, v_msgData_1235_, v_severity_1236_, v_isSilent_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46_spec__48___boxed(lean_object* v_msgData_1245_, lean_object* v_severity_1246_, lean_object* v_isSilent_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
uint8_t v_severity_boxed_1253_; uint8_t v_isSilent_boxed_1254_; lean_object* v_res_1255_; 
v_severity_boxed_1253_ = lean_unbox(v_severity_1246_);
v_isSilent_boxed_1254_ = lean_unbox(v_isSilent_1247_);
v_res_1255_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46_spec__48(v_msgData_1245_, v_severity_boxed_1253_, v_isSilent_boxed_1254_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46(lean_object* v_msgData_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
uint8_t v___x_1262_; uint8_t v___x_1263_; lean_object* v___x_1264_; 
v___x_1262_ = 1;
v___x_1263_ = 0;
v___x_1264_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46_spec__48(v_msgData_1256_, v___x_1262_, v___x_1263_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46___boxed(lean_object* v_msgData_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46(v_msgData_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__45___redArg(lean_object* v_opt_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v___x_1275_; uint8_t v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1275_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1273_);
v___x_1276_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5(v___x_1275_, v_opt_1272_);
lean_dec_ref(v___x_1275_);
v___x_1277_ = lean_box(v___x_1276_);
v___x_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1277_);
v___x_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1278_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__45___redArg___boxed(lean_object* v_opt_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__45___redArg(v_opt_1280_, v___y_1281_);
lean_dec_ref(v___y_1281_);
lean_dec_ref(v_opt_1280_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42(lean_object* v_id_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
lean_object* v___x_1290_; lean_object* v_env_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1314_; 
v___x_1290_ = lean_st_ref_get(v___y_1288_);
v_env_1291_ = lean_ctor_get(v___x_1290_, 0);
lean_inc_ref(v_env_1291_);
lean_dec(v___x_1290_);
v___x_1292_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1293_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__45___redArg(v___x_1292_, v___y_1287_);
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1296_ = v___x_1293_;
v_isShared_1297_ = v_isSharedCheck_1314_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1293_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1314_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
uint8_t v_isExporting_1303_; 
v_isExporting_1303_ = lean_ctor_get_uint8(v_env_1291_, sizeof(void*)*13);
lean_dec_ref(v_env_1291_);
if (v_isExporting_1303_ == 0)
{
lean_dec(v_a_1294_);
lean_dec(v_id_1284_);
goto v___jp_1298_;
}
else
{
lean_object* v_val_1304_; uint8_t v___x_1305_; 
v_val_1304_ = lean_ctor_get(v_a_1294_, 0);
lean_inc(v_val_1304_);
lean_dec(v_a_1294_);
v___x_1305_ = l_Lean_isPrivateName(v_id_1284_);
if (v___x_1305_ == 0)
{
lean_dec(v_val_1304_);
lean_dec(v_id_1284_);
goto v___jp_1298_;
}
else
{
uint8_t v___x_1306_; 
v___x_1306_ = lean_unbox(v_val_1304_);
lean_dec(v_val_1304_);
if (v___x_1306_ == 0)
{
lean_dec(v_id_1284_);
goto v___jp_1298_;
}
else
{
lean_object* v___x_1307_; uint8_t v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
lean_del_object(v___x_1296_);
v___x_1307_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34___closed__1);
v___x_1308_ = 0;
v___x_1309_ = l_Lean_MessageData_ofConstName(v_id_1284_, v___x_1308_);
v___x_1310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1307_);
lean_ctor_set(v___x_1310_, 1, v___x_1309_);
v___x_1311_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34___closed__3);
v___x_1312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1310_);
lean_ctor_set(v___x_1312_, 1, v___x_1311_);
v___x_1313_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46(v___x_1312_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_);
return v___x_1313_;
}
}
}
v___jp_1298_:
{
lean_object* v___x_1299_; lean_object* v___x_1301_; 
v___x_1299_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__46_spec__48_spec__50___closed__0));
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 0, v___x_1299_);
v___x_1301_ = v___x_1296_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___x_1299_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42___boxed(lean_object* v_id_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42(v_id_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36(lean_object* v_id_1322_, uint8_t v_enableLog_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
lean_object* v___x_1329_; lean_object* v_toCold_1330_; lean_object* v_env_1331_; lean_object* v_currNamespace_1332_; lean_object* v_openDecls_1333_; lean_object* v___x_1334_; lean_object* v_res_1335_; lean_object* v___x_1339_; 
v___x_1329_ = lean_st_ref_get(v___y_1327_);
v_toCold_1330_ = lean_ctor_get(v___y_1326_, 0);
v_env_1331_ = lean_ctor_get(v___x_1329_, 0);
lean_inc_ref(v_env_1331_);
lean_dec(v___x_1329_);
v_currNamespace_1332_ = lean_ctor_get(v_toCold_1330_, 4);
v_openDecls_1333_ = lean_ctor_get(v_toCold_1330_, 5);
v___x_1334_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1326_);
lean_inc(v_openDecls_1333_);
lean_inc(v_currNamespace_1332_);
v_res_1335_ = l_Lean_ResolveName_resolveGlobalName(v_env_1331_, v___x_1334_, v_currNamespace_1332_, v_openDecls_1333_, v_id_1322_);
lean_dec_ref(v___x_1334_);
v___x_1339_ = lean_st_ref_get(v___y_1327_);
if (v_enableLog_1323_ == 0)
{
lean_dec(v___x_1339_);
goto v___jp_1336_;
}
else
{
lean_object* v_env_1340_; uint8_t v_isExporting_1341_; 
v_env_1340_ = lean_ctor_get(v___x_1339_, 0);
lean_inc_ref(v_env_1340_);
lean_dec(v___x_1339_);
v_isExporting_1341_ = lean_ctor_get_uint8(v_env_1340_, sizeof(void*)*13);
lean_dec_ref(v_env_1340_);
if (v_isExporting_1341_ == 0)
{
goto v___jp_1336_;
}
else
{
lean_object* v___x_1342_; 
v___x_1342_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__33(v_res_1335_);
if (lean_obj_tag(v___x_1342_) == 1)
{
lean_object* v_val_1343_; lean_object* v_fst_1344_; lean_object* v___x_1345_; 
v_val_1343_ = lean_ctor_get(v___x_1342_, 0);
lean_inc(v_val_1343_);
lean_dec_ref_known(v___x_1342_, 1);
v_fst_1344_ = lean_ctor_get(v_val_1343_, 0);
lean_inc(v_fst_1344_);
lean_dec(v_val_1343_);
v___x_1345_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42(v_fst_1344_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1354_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1348_ = v___x_1345_;
v_isShared_1349_ = v_isSharedCheck_1354_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1345_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1354_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
if (lean_obj_tag(v_a_1346_) == 0)
{
lean_object* v___x_1350_; lean_object* v___x_1352_; 
lean_dec(v_res_1335_);
v___x_1350_ = lean_box(0);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 0, v___x_1350_);
v___x_1352_ = v___x_1348_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v___x_1350_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
else
{
lean_dec_ref_known(v_a_1346_, 1);
lean_del_object(v___x_1348_);
goto v___jp_1336_;
}
}
}
else
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1362_; 
lean_dec(v_res_1335_);
v_a_1355_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1357_ = v___x_1345_;
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1345_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1355_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
else
{
lean_dec(v___x_1342_);
goto v___jp_1336_;
}
}
}
v___jp_1336_:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1337_, 0, v_res_1335_);
v___x_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1337_);
return v___x_1338_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36___boxed(lean_object* v_id_1363_, lean_object* v_enableLog_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
uint8_t v_enableLog_boxed_1370_; lean_object* v_res_1371_; 
v_enableLog_boxed_1370_ = lean_unbox(v_enableLog_1364_);
v_res_1371_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36(v_id_1363_, v_enableLog_boxed_1370_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27(lean_object* v_n_u2080_1376_, lean_object* v_filter_1377_, lean_object* v_view_x3f_1378_, lean_object* v_n_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1455_; 
if (lean_obj_tag(v_view_x3f_1378_) == 1)
{
lean_object* v_val_1482_; lean_object* v_imported_1483_; lean_object* v_ctx_1484_; lean_object* v_scopes_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1493_; 
v_val_1482_ = lean_ctor_get(v_view_x3f_1378_, 0);
lean_inc(v_val_1482_);
lean_dec_ref_known(v_view_x3f_1378_, 1);
v_imported_1483_ = lean_ctor_get(v_val_1482_, 1);
v_ctx_1484_ = lean_ctor_get(v_val_1482_, 2);
v_scopes_1485_ = lean_ctor_get(v_val_1482_, 3);
v_isSharedCheck_1493_ = !lean_is_exclusive(v_val_1482_);
if (v_isSharedCheck_1493_ == 0)
{
lean_object* v_unused_1494_; 
v_unused_1494_ = lean_ctor_get(v_val_1482_, 0);
lean_dec(v_unused_1494_);
v___x_1487_ = v_val_1482_;
v_isShared_1488_ = v_isSharedCheck_1493_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_scopes_1485_);
lean_inc(v_ctx_1484_);
lean_inc(v_imported_1483_);
lean_dec(v_val_1482_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1493_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1490_; 
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 0, v_n_1379_);
v___x_1490_ = v___x_1487_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_n_1379_);
lean_ctor_set(v_reuseFailAlloc_1492_, 1, v_imported_1483_);
lean_ctor_set(v_reuseFailAlloc_1492_, 2, v_ctx_1484_);
lean_ctor_set(v_reuseFailAlloc_1492_, 3, v_scopes_1485_);
v___x_1490_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
lean_object* v___x_1491_; 
v___x_1491_ = l_Lean_MacroScopesView_review(v___x_1490_);
v___y_1455_ = v___x_1491_;
goto v___jp_1454_;
}
}
}
else
{
lean_dec(v_view_x3f_1378_);
v___y_1455_ = v_n_1379_;
goto v___jp_1454_;
}
v___jp_1385_:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1386_ = lean_box(0);
v___x_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1386_);
return v___x_1387_;
}
v___jp_1388_:
{
lean_object* v___x_1391_; 
lean_inc_ref(v___y_1390_);
lean_inc(v___y_1383_);
lean_inc_ref(v___y_1382_);
lean_inc(v___y_1381_);
lean_inc_ref(v___y_1380_);
v___x_1391_ = lean_apply_5(v___y_1390_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, lean_box(0));
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1411_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1394_ = v___x_1391_;
v_isShared_1395_ = v_isSharedCheck_1411_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_dec(v___x_1391_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1411_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
if (lean_obj_tag(v_a_1392_) == 0)
{
lean_object* v___x_1396_; lean_object* v___x_1398_; 
lean_dec(v___y_1389_);
v___x_1396_ = lean_box(0);
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 0, v___x_1396_);
v___x_1398_ = v___x_1394_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1396_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
else
{
lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1409_; 
v_isSharedCheck_1409_ = !lean_is_exclusive(v_a_1392_);
if (v_isSharedCheck_1409_ == 0)
{
lean_object* v_unused_1410_; 
v_unused_1410_ = lean_ctor_get(v_a_1392_, 0);
lean_dec(v_unused_1410_);
v___x_1401_ = v_a_1392_;
v_isShared_1402_ = v_isSharedCheck_1409_;
goto v_resetjp_1400_;
}
else
{
lean_dec(v_a_1392_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1409_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1404_; 
if (v_isShared_1402_ == 0)
{
lean_ctor_set(v___x_1401_, 0, v___y_1389_);
v___x_1404_ = v___x_1401_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v___y_1389_);
v___x_1404_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
lean_object* v___x_1406_; 
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 0, v___x_1404_);
v___x_1406_ = v___x_1394_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v___x_1404_);
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
else
{
lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1419_; 
lean_dec(v___y_1389_);
v_a_1412_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1414_ = v___x_1391_;
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_dec(v___x_1391_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1417_; 
if (v_isShared_1415_ == 0)
{
v___x_1417_ = v___x_1414_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_a_1412_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
}
v___jp_1420_:
{
lean_object* v___x_1423_; 
lean_inc_ref(v___y_1422_);
lean_inc(v___y_1383_);
lean_inc_ref(v___y_1382_);
lean_inc(v___y_1381_);
lean_inc_ref(v___y_1380_);
v___x_1423_ = lean_apply_5(v___y_1422_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, lean_box(0));
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v_a_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1445_; 
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1426_ = v___x_1423_;
v_isShared_1427_ = v_isSharedCheck_1445_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_a_1424_);
lean_dec(v___x_1423_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1445_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
if (lean_obj_tag(v_a_1424_) == 0)
{
lean_object* v___x_1428_; lean_object* v___x_1430_; 
lean_dec(v___y_1421_);
lean_dec_ref(v_filter_1377_);
v___x_1428_ = lean_box(0);
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 0, v___x_1428_);
v___x_1430_ = v___x_1426_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___x_1428_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
else
{
lean_object* v___x_1432_; 
lean_dec_ref_known(v_a_1424_, 1);
lean_del_object(v___x_1426_);
lean_inc(v___y_1383_);
lean_inc_ref(v___y_1382_);
lean_inc(v___y_1381_);
lean_inc_ref(v___y_1380_);
lean_inc(v___y_1421_);
v___x_1432_ = lean_apply_6(v_filter_1377_, v___y_1421_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, lean_box(0));
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v_a_1433_; uint8_t v___x_1434_; 
v_a_1433_ = lean_ctor_get(v___x_1432_, 0);
lean_inc(v_a_1433_);
lean_dec_ref_known(v___x_1432_, 1);
v___x_1434_ = lean_unbox(v_a_1433_);
lean_dec(v_a_1433_);
if (v___x_1434_ == 0)
{
lean_object* v___f_1435_; 
v___f_1435_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27___closed__0));
v___y_1389_ = v___y_1421_;
v___y_1390_ = v___f_1435_;
goto v___jp_1388_;
}
else
{
lean_object* v___f_1436_; 
v___f_1436_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27___closed__1));
v___y_1389_ = v___y_1421_;
v___y_1390_ = v___f_1436_;
goto v___jp_1388_;
}
}
else
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1444_; 
lean_dec(v___y_1421_);
v_a_1437_ = lean_ctor_get(v___x_1432_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1439_ = v___x_1432_;
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1432_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1442_; 
if (v_isShared_1440_ == 0)
{
v___x_1442_ = v___x_1439_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_a_1437_);
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
lean_object* v_a_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1453_; 
lean_dec(v___y_1421_);
lean_dec_ref(v_filter_1377_);
v_a_1446_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1448_ = v___x_1423_;
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_a_1446_);
lean_dec(v___x_1423_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1451_; 
if (v_isShared_1449_ == 0)
{
v___x_1451_ = v___x_1448_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_a_1446_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
}
v___jp_1454_:
{
uint8_t v___x_1456_; lean_object* v___x_1457_; 
v___x_1456_ = 0;
lean_inc(v___y_1455_);
v___x_1457_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36(v___y_1455_, v___x_1456_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1473_; 
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1460_ = v___x_1457_;
v_isShared_1461_ = v_isSharedCheck_1473_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1457_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1473_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
if (lean_obj_tag(v_a_1458_) == 0)
{
lean_object* v___x_1462_; lean_object* v___x_1464_; 
lean_dec(v___y_1455_);
lean_dec_ref(v_filter_1377_);
v___x_1462_ = lean_box(0);
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 0, v___x_1462_);
v___x_1464_ = v___x_1460_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1462_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
else
{
lean_object* v_val_1466_; 
lean_del_object(v___x_1460_);
v_val_1466_ = lean_ctor_get(v_a_1458_, 0);
lean_inc(v_val_1466_);
lean_dec_ref_known(v_a_1458_, 1);
if (lean_obj_tag(v_val_1466_) == 1)
{
lean_object* v_head_1467_; lean_object* v_tail_1468_; 
v_head_1467_ = lean_ctor_get(v_val_1466_, 0);
lean_inc(v_head_1467_);
v_tail_1468_ = lean_ctor_get(v_val_1466_, 1);
lean_inc(v_tail_1468_);
lean_dec_ref_known(v_val_1466_, 2);
if (lean_obj_tag(v_tail_1468_) == 0)
{
lean_object* v_fst_1469_; uint8_t v___x_1470_; 
v_fst_1469_ = lean_ctor_get(v_head_1467_, 0);
lean_inc(v_fst_1469_);
lean_dec(v_head_1467_);
v___x_1470_ = lean_name_eq(v_fst_1469_, v_n_u2080_1376_);
lean_dec(v_fst_1469_);
if (v___x_1470_ == 0)
{
lean_object* v___f_1471_; 
v___f_1471_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27___closed__0));
v___y_1421_ = v___y_1455_;
v___y_1422_ = v___f_1471_;
goto v___jp_1420_;
}
else
{
lean_object* v___f_1472_; 
v___f_1472_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27___closed__1));
v___y_1421_ = v___y_1455_;
v___y_1422_ = v___f_1472_;
goto v___jp_1420_;
}
}
else
{
lean_dec(v_tail_1468_);
lean_dec(v_head_1467_);
lean_dec(v___y_1455_);
lean_dec_ref(v_filter_1377_);
goto v___jp_1385_;
}
}
else
{
lean_dec(v_val_1466_);
lean_dec(v___y_1455_);
lean_dec_ref(v_filter_1377_);
goto v___jp_1385_;
}
}
}
}
else
{
lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1481_; 
lean_dec(v___y_1455_);
lean_dec_ref(v_filter_1377_);
v_a_1474_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1476_ = v___x_1457_;
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v___x_1457_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1479_; 
if (v_isShared_1477_ == 0)
{
v___x_1479_ = v___x_1476_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_a_1474_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27___boxed(lean_object* v_n_u2080_1495_, lean_object* v_filter_1496_, lean_object* v_view_x3f_1497_, lean_object* v_n_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27(v_n_u2080_1495_, v_filter_1496_, v_view_x3f_1497_, v_n_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v_n_u2080_1495_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__24_spec__32___redArg(lean_object* v_n_u2080_1505_, lean_object* v_filter_1506_, lean_object* v_view_x3f_1507_, lean_object* v_as_x27_1508_, lean_object* v_b_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
if (lean_obj_tag(v_as_x27_1508_) == 0)
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
lean_dec(v_view_x3f_1507_);
lean_dec_ref(v_filter_1506_);
v___x_1515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1515_, 0, v_b_1509_);
v___x_1516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1515_);
return v___x_1516_;
}
else
{
lean_object* v_head_1517_; lean_object* v_tail_1518_; lean_object* v_snd_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1557_; 
v_head_1517_ = lean_ctor_get(v_as_x27_1508_, 0);
v_tail_1518_ = lean_ctor_get(v_as_x27_1508_, 1);
v_snd_1519_ = lean_ctor_get(v_b_1509_, 1);
v_isSharedCheck_1557_ = !lean_is_exclusive(v_b_1509_);
if (v_isSharedCheck_1557_ == 0)
{
lean_object* v_unused_1558_; 
v_unused_1558_ = lean_ctor_get(v_b_1509_, 0);
lean_dec(v_unused_1558_);
v___x_1521_ = v_b_1509_;
v_isShared_1522_ = v_isSharedCheck_1557_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_snd_1519_);
lean_dec(v_b_1509_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1557_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
v___x_1523_ = lean_box(0);
v___x_1524_ = l_Lean_Name_appendCore(v_head_1517_, v_snd_1519_);
lean_inc(v___x_1524_);
lean_inc(v_view_x3f_1507_);
lean_inc_ref(v_filter_1506_);
v___x_1525_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27(v_n_u2080_1505_, v_filter_1506_, v_view_x3f_1507_, v___x_1524_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
if (lean_obj_tag(v___x_1525_) == 0)
{
lean_object* v_a_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1548_; 
v_a_1526_ = lean_ctor_get(v___x_1525_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1525_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1528_ = v___x_1525_;
v_isShared_1529_ = v_isSharedCheck_1548_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_a_1526_);
lean_dec(v___x_1525_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1548_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
if (lean_obj_tag(v_a_1526_) == 0)
{
lean_object* v___x_1531_; 
lean_del_object(v___x_1528_);
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 1, v___x_1524_);
lean_ctor_set(v___x_1521_, 0, v___x_1523_);
v___x_1531_ = v___x_1521_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v___x_1523_);
lean_ctor_set(v_reuseFailAlloc_1533_, 1, v___x_1524_);
v___x_1531_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
v_as_x27_1508_ = v_tail_1518_;
v_b_1509_ = v___x_1531_;
goto _start;
}
}
else
{
lean_object* v___x_1535_; 
lean_dec(v_view_x3f_1507_);
lean_dec_ref(v_filter_1506_);
lean_inc_ref(v_a_1526_);
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 1, v___x_1524_);
lean_ctor_set(v___x_1521_, 0, v_a_1526_);
v___x_1535_ = v___x_1521_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_a_1526_);
lean_ctor_set(v_reuseFailAlloc_1547_, 1, v___x_1524_);
v___x_1535_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1545_; 
v_isSharedCheck_1545_ = !lean_is_exclusive(v_a_1526_);
if (v_isSharedCheck_1545_ == 0)
{
lean_object* v_unused_1546_; 
v_unused_1546_ = lean_ctor_get(v_a_1526_, 0);
lean_dec(v_unused_1546_);
v___x_1537_ = v_a_1526_;
v_isShared_1538_ = v_isSharedCheck_1545_;
goto v_resetjp_1536_;
}
else
{
lean_dec(v_a_1526_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1545_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1540_; 
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 0, v___x_1535_);
v___x_1540_ = v___x_1537_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1535_);
v___x_1540_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
lean_object* v___x_1542_; 
if (v_isShared_1529_ == 0)
{
lean_ctor_set(v___x_1528_, 0, v___x_1540_);
v___x_1542_ = v___x_1528_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v___x_1540_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1556_; 
lean_dec(v___x_1524_);
lean_del_object(v___x_1521_);
lean_dec(v_view_x3f_1507_);
lean_dec_ref(v_filter_1506_);
v_a_1549_ = lean_ctor_get(v___x_1525_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1525_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1551_ = v___x_1525_;
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v___x_1525_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1554_; 
if (v_isShared_1552_ == 0)
{
v___x_1554_ = v___x_1551_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_a_1549_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__24_spec__32___redArg___boxed(lean_object* v_n_u2080_1559_, lean_object* v_filter_1560_, lean_object* v_view_x3f_1561_, lean_object* v_as_x27_1562_, lean_object* v_b_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__24_spec__32___redArg(v_n_u2080_1559_, v_filter_1560_, v_view_x3f_1561_, v_as_x27_1562_, v_b_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_);
lean_dec(v___y_1567_);
lean_dec_ref(v___y_1566_);
lean_dec(v___y_1565_);
lean_dec_ref(v___y_1564_);
lean_dec(v_as_x27_1562_);
lean_dec(v_n_u2080_1559_);
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__24(lean_object* v_n_u2080_1573_, lean_object* v_filter_1574_, lean_object* v_view_x3f_1575_, lean_object* v_n_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
lean_object* v___y_1583_; uint8_t v___x_1624_; 
v___x_1624_ = l_Lean_Name_hasMacroScopes(v_n_1576_);
if (v___x_1624_ == 0)
{
lean_object* v___f_1625_; 
v___f_1625_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27___closed__1));
v___y_1583_ = v___f_1625_;
goto v___jp_1582_;
}
else
{
lean_object* v___f_1626_; 
v___f_1626_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27___closed__0));
v___y_1583_ = v___f_1626_;
goto v___jp_1582_;
}
v___jp_1582_:
{
lean_object* v___x_1584_; 
lean_inc_ref(v___y_1583_);
lean_inc(v___y_1580_);
lean_inc_ref(v___y_1579_);
lean_inc(v___y_1578_);
lean_inc_ref(v___y_1577_);
v___x_1584_ = lean_apply_5(v___y_1583_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, lean_box(0));
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1615_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1587_ = v___x_1584_;
v_isShared_1588_ = v_isSharedCheck_1615_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1584_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1615_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
if (lean_obj_tag(v_a_1585_) == 0)
{
lean_object* v___x_1589_; lean_object* v___x_1591_; 
lean_dec(v_n_1576_);
lean_dec(v_view_x3f_1575_);
lean_dec_ref(v_filter_1574_);
v___x_1589_ = lean_box(0);
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 0, v___x_1589_);
v___x_1591_ = v___x_1587_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1589_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
else
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
lean_dec_ref_known(v_a_1585_, 1);
lean_del_object(v___x_1587_);
v___x_1593_ = l_Lean_privateToUserName(v_n_1576_);
v___x_1594_ = l_Lean_Name_componentsRev(v___x_1593_);
v___x_1595_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__24___closed__0));
v___x_1596_ = l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__24_spec__32___redArg(v_n_u2080_1573_, v_filter_1574_, v_view_x3f_1575_, v___x_1594_, v___x_1595_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
lean_dec(v___x_1594_);
if (lean_obj_tag(v___x_1596_) == 0)
{
lean_object* v_a_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1606_; 
v_a_1597_ = lean_ctor_get(v___x_1596_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1599_ = v___x_1596_;
v_isShared_1600_ = v_isSharedCheck_1606_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_a_1597_);
lean_dec(v___x_1596_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1606_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v_val_1601_; lean_object* v_fst_1602_; lean_object* v___x_1604_; 
v_val_1601_ = lean_ctor_get(v_a_1597_, 0);
lean_inc(v_val_1601_);
lean_dec(v_a_1597_);
v_fst_1602_ = lean_ctor_get(v_val_1601_, 0);
lean_inc(v_fst_1602_);
lean_dec(v_val_1601_);
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 0, v_fst_1602_);
v___x_1604_ = v___x_1599_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_fst_1602_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
else
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1614_; 
v_a_1607_ = lean_ctor_get(v___x_1596_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1609_ = v___x_1596_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1596_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
if (v_isShared_1610_ == 0)
{
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_a_1607_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
}
}
else
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1623_; 
lean_dec(v_n_1576_);
lean_dec(v_view_x3f_1575_);
lean_dec_ref(v_filter_1574_);
v_a_1616_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1618_ = v___x_1584_;
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1584_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1621_; 
if (v_isShared_1619_ == 0)
{
v___x_1621_ = v___x_1618_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_a_1616_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__24___boxed(lean_object* v_n_u2080_1627_, lean_object* v_filter_1628_, lean_object* v_view_x3f_1629_, lean_object* v_n_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__24(v_n_u2080_1627_, v_filter_1628_, v_view_x3f_1629_, v_n_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
lean_dec(v_n_u2080_1627_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__25(lean_object* v_n_u2080_1637_, lean_object* v_filter_1638_, lean_object* v_as_1639_, lean_object* v_i_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_){
_start:
{
lean_object* v___x_1646_; uint8_t v___x_1647_; 
v___x_1646_ = lean_array_get_size(v_as_1639_);
v___x_1647_ = lean_nat_dec_lt(v_i_1640_, v___x_1646_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
lean_dec(v_i_1640_);
lean_dec_ref(v_filter_1638_);
v___x_1648_ = lean_box(0);
v___x_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1648_);
return v___x_1649_;
}
else
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1650_ = lean_box(0);
v___x_1651_ = lean_array_fget_borrowed(v_as_1639_, v_i_1640_);
lean_inc(v___x_1651_);
lean_inc_ref(v_filter_1638_);
v___x_1652_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__24(v_n_u2080_1637_, v_filter_1638_, v___x_1650_, v___x_1651_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v_a_1653_; 
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
if (lean_obj_tag(v_a_1653_) == 0)
{
lean_object* v___x_1654_; lean_object* v___x_1655_; 
lean_dec_ref_known(v___x_1652_, 1);
v___x_1654_ = lean_unsigned_to_nat(1u);
v___x_1655_ = lean_nat_add(v_i_1640_, v___x_1654_);
lean_dec(v_i_1640_);
v_i_1640_ = v___x_1655_;
goto _start;
}
else
{
lean_dec(v_i_1640_);
lean_dec_ref(v_filter_1638_);
return v___x_1652_;
}
}
else
{
lean_dec(v_i_1640_);
lean_dec_ref(v_filter_1638_);
return v___x_1652_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__25___boxed(lean_object* v_n_u2080_1657_, lean_object* v_filter_1658_, lean_object* v_as_1659_, lean_object* v_i_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__25(v_n_u2080_1657_, v_filter_1658_, v_as_1659_, v_i_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
lean_dec_ref(v_as_1659_);
lean_dec(v_n_u2080_1657_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__26(lean_object* v_n_u2081_1667_, lean_object* v_as_1668_, size_t v_i_1669_, size_t v_stop_1670_, lean_object* v_b_1671_){
_start:
{
lean_object* v___y_1673_; uint8_t v___x_1677_; 
v___x_1677_ = lean_usize_dec_eq(v_i_1669_, v_stop_1670_);
if (v___x_1677_ == 0)
{
lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; uint8_t v___x_1681_; 
v___x_1678_ = lean_array_uget_borrowed(v_as_1668_, v_i_1669_);
v___x_1679_ = l_Lean_Name_getPrefix(v___x_1678_);
v___x_1680_ = l_Lean_Name_getPrefix(v_n_u2081_1667_);
v___x_1681_ = l_Lean_Name_isPrefixOf(v___x_1679_, v___x_1680_);
lean_dec(v___x_1680_);
lean_dec(v___x_1679_);
if (v___x_1681_ == 0)
{
v___y_1673_ = v_b_1671_;
goto v___jp_1672_;
}
else
{
lean_object* v___x_1682_; 
lean_inc(v___x_1678_);
v___x_1682_ = lean_array_push(v_b_1671_, v___x_1678_);
v___y_1673_ = v___x_1682_;
goto v___jp_1672_;
}
}
else
{
return v_b_1671_;
}
v___jp_1672_:
{
size_t v___x_1674_; size_t v___x_1675_; 
v___x_1674_ = ((size_t)1ULL);
v___x_1675_ = lean_usize_add(v_i_1669_, v___x_1674_);
v_i_1669_ = v___x_1675_;
v_b_1671_ = v___y_1673_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__26___boxed(lean_object* v_n_u2081_1683_, lean_object* v_as_1684_, lean_object* v_i_1685_, lean_object* v_stop_1686_, lean_object* v_b_1687_){
_start:
{
size_t v_i_boxed_1688_; size_t v_stop_boxed_1689_; lean_object* v_res_1690_; 
v_i_boxed_1688_ = lean_unbox_usize(v_i_1685_);
lean_dec(v_i_1685_);
v_stop_boxed_1689_ = lean_unbox_usize(v_stop_1686_);
lean_dec(v_stop_1686_);
v_res_1690_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__26(v_n_u2081_1683_, v_as_1684_, v_i_boxed_1688_, v_stop_boxed_1689_, v_b_1687_);
lean_dec_ref(v_as_1684_);
lean_dec(v_n_u2081_1683_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14(lean_object* v_n_u2080_1693_, uint8_t v_fullNames_1694_, uint8_t v_allowHorizAliases_1695_, lean_object* v_filter_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v_view_1702_; lean_object* v_name_1703_; lean_object* v_n_u2081_1704_; 
lean_inc(v_n_u2080_1693_);
v_view_1702_ = l_Lean_extractMacroScopes(v_n_u2080_1693_);
v_name_1703_ = lean_ctor_get(v_view_1702_, 0);
lean_inc(v_name_1703_);
v_n_u2081_1704_ = l_Lean_privateToUserName(v_name_1703_);
if (v_fullNames_1694_ == 0)
{
lean_object* v___x_1705_; lean_object* v_aliases_1707_; lean_object* v_env_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1705_ = lean_st_ref_get(v___y_1700_);
v_env_1722_ = lean_ctor_get(v___x_1705_, 0);
lean_inc_ref(v_env_1722_);
lean_dec(v___x_1705_);
lean_inc(v_n_u2080_1693_);
v___x_1723_ = l_Lean_getRevAliases(v_env_1722_, v_n_u2080_1693_);
v___x_1724_ = lean_array_mk(v___x_1723_);
if (v_allowHorizAliases_1695_ == 0)
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; uint8_t v___x_1728_; 
v___x_1725_ = lean_unsigned_to_nat(0u);
v___x_1726_ = lean_array_get_size(v___x_1724_);
v___x_1727_ = ((lean_object*)(l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14___closed__0));
v___x_1728_ = lean_nat_dec_lt(v___x_1725_, v___x_1726_);
if (v___x_1728_ == 0)
{
lean_dec_ref(v___x_1724_);
v_aliases_1707_ = v___x_1727_;
goto v___jp_1706_;
}
else
{
size_t v___x_1729_; size_t v___x_1730_; lean_object* v___x_1731_; 
v___x_1729_ = ((size_t)0ULL);
v___x_1730_ = lean_usize_of_nat(v___x_1726_);
v___x_1731_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__26(v_n_u2081_1704_, v___x_1724_, v___x_1729_, v___x_1730_, v___x_1727_);
lean_dec_ref(v___x_1724_);
v_aliases_1707_ = v___x_1731_;
goto v___jp_1706_;
}
}
else
{
v_aliases_1707_ = v___x_1724_;
goto v___jp_1706_;
}
v___jp_1706_:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1708_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_filter_1696_);
v___x_1709_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__25(v_n_u2080_1693_, v_filter_1696_, v_aliases_1707_, v___x_1708_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
lean_dec_ref(v_aliases_1707_);
if (lean_obj_tag(v___x_1709_) == 0)
{
lean_object* v_a_1710_; 
v_a_1710_ = lean_ctor_get(v___x_1709_, 0);
if (lean_obj_tag(v_a_1710_) == 0)
{
lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1720_; 
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1720_ == 0)
{
lean_object* v_unused_1721_; 
v_unused_1721_ = lean_ctor_get(v___x_1709_, 0);
lean_dec(v_unused_1721_);
v___x_1712_ = v___x_1709_;
v_isShared_1713_ = v_isSharedCheck_1720_;
goto v_resetjp_1711_;
}
else
{
lean_dec(v___x_1709_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1720_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1715_; 
if (v_isShared_1713_ == 0)
{
lean_ctor_set_tag(v___x_1712_, 1);
lean_ctor_set(v___x_1712_, 0, v_view_1702_);
v___x_1715_ = v___x_1712_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_view_1702_);
v___x_1715_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1716_ = l_Lean_rootNamespace;
v___x_1717_ = l_Lean_Name_append(v___x_1716_, v_n_u2081_1704_);
v___x_1718_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__24(v_n_u2080_1693_, v_filter_1696_, v___x_1715_, v___x_1717_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
lean_dec(v_n_u2080_1693_);
return v___x_1718_;
}
}
}
else
{
lean_dec(v_n_u2081_1704_);
lean_dec_ref(v_view_1702_);
lean_dec_ref(v_filter_1696_);
lean_dec(v_n_u2080_1693_);
return v___x_1709_;
}
}
else
{
lean_dec(v_n_u2081_1704_);
lean_dec_ref(v_view_1702_);
lean_dec_ref(v_filter_1696_);
lean_dec(v_n_u2080_1693_);
return v___x_1709_;
}
}
}
else
{
lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1732_, 0, v_view_1702_);
lean_inc(v_n_u2081_1704_);
lean_inc_ref(v___x_1732_);
lean_inc_ref(v_filter_1696_);
v___x_1733_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27(v_n_u2080_1693_, v_filter_1696_, v___x_1732_, v_n_u2081_1704_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
if (lean_obj_tag(v___x_1733_) == 0)
{
lean_object* v_a_1734_; 
v_a_1734_ = lean_ctor_get(v___x_1733_, 0);
if (lean_obj_tag(v_a_1734_) == 0)
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
lean_dec_ref_known(v___x_1733_, 1);
v___x_1735_ = l_Lean_rootNamespace;
v___x_1736_ = l_Lean_Name_append(v___x_1735_, v_n_u2081_1704_);
v___x_1737_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27(v_n_u2080_1693_, v_filter_1696_, v___x_1732_, v___x_1736_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
lean_dec(v_n_u2080_1693_);
return v___x_1737_;
}
else
{
lean_dec_ref_known(v___x_1732_, 1);
lean_dec(v_n_u2081_1704_);
lean_dec_ref(v_filter_1696_);
lean_dec(v_n_u2080_1693_);
return v___x_1733_;
}
}
else
{
lean_dec_ref_known(v___x_1732_, 1);
lean_dec(v_n_u2081_1704_);
lean_dec_ref(v_filter_1696_);
lean_dec(v_n_u2080_1693_);
return v___x_1733_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14___boxed(lean_object* v_n_u2080_1738_, lean_object* v_fullNames_1739_, lean_object* v_allowHorizAliases_1740_, lean_object* v_filter_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
uint8_t v_fullNames_boxed_1747_; uint8_t v_allowHorizAliases_boxed_1748_; lean_object* v_res_1749_; 
v_fullNames_boxed_1747_ = lean_unbox(v_fullNames_1739_);
v_allowHorizAliases_boxed_1748_ = lean_unbox(v_allowHorizAliases_1740_);
v_res_1749_ = l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14(v_n_u2080_1738_, v_fullNames_boxed_1747_, v_allowHorizAliases_boxed_1748_, v_filter_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6(lean_object* v_n_u2080_1753_, uint8_t v_fullNames_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
uint8_t v___x_1760_; lean_object* v___f_1761_; lean_object* v___x_1762_; 
v___x_1760_ = 0;
v___f_1761_ = ((lean_object*)(l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6___closed__0));
v___x_1762_ = l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14(v_n_u2080_1753_, v_fullNames_1754_, v___x_1760_, v___f_1761_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6___boxed(lean_object* v_n_u2080_1763_, lean_object* v_fullNames_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
uint8_t v_fullNames_boxed_1770_; lean_object* v_res_1771_; 
v_fullNames_boxed_1770_ = lean_unbox(v_fullNames_1764_);
v_res_1771_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6(v_n_u2080_1763_, v_fullNames_boxed_1770_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
return v_res_1771_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_1772_; 
v___x_1772_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1772_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1773_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4_spec__10___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4_spec__10___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4_spec__10___redArg___closed__0);
v___x_1774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1773_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4_spec__10___redArg(){
_start:
{
lean_object* v___x_1776_; 
v___x_1776_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4_spec__10___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4_spec__10___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4_spec__10___redArg___closed__1);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4_spec__10___redArg___boxed(lean_object* v___dummy_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4_spec__10___redArg();
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3_spec__8___redArg(lean_object* v_o_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v_env_1784_; lean_object* v___x_1785_; lean_object* v_toEnvExtension_1786_; lean_object* v_asyncMode_1787_; lean_object* v___x_1788_; uint8_t v___x_1789_; lean_object* v___x_1790_; lean_object* v_merged_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1799_; 
v___x_1782_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_1783_ = lean_st_ref_get(v___y_1780_);
v_env_1784_ = lean_ctor_get(v___x_1783_, 0);
lean_inc_ref(v_env_1784_);
lean_dec(v___x_1783_);
v___x_1785_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_1786_ = lean_ctor_get(v___x_1785_, 0);
v_asyncMode_1787_ = lean_ctor_get(v_toEnvExtension_1786_, 2);
v___x_1788_ = lean_box(0);
v___x_1789_ = 0;
v___x_1790_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1782_, v___x_1785_, v_env_1784_, v_asyncMode_1787_, v___x_1788_, v___x_1789_);
v_merged_1791_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1799_ == 0)
{
lean_object* v_unused_1800_; 
v_unused_1800_ = lean_ctor_get(v___x_1790_, 1);
lean_dec(v_unused_1800_);
v___x_1793_ = v___x_1790_;
v_isShared_1794_ = v_isSharedCheck_1799_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_merged_1791_);
lean_dec(v___x_1790_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1799_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1796_; 
if (v_isShared_1794_ == 0)
{
lean_ctor_set(v___x_1793_, 1, v_merged_1791_);
lean_ctor_set(v___x_1793_, 0, v_o_1779_);
v___x_1796_ = v___x_1793_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_o_1779_);
lean_ctor_set(v_reuseFailAlloc_1798_, 1, v_merged_1791_);
v___x_1796_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
lean_object* v___x_1797_; 
v___x_1797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1796_);
return v___x_1797_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3_spec__8___redArg___boxed(lean_object* v_o_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
lean_object* v_res_1804_; 
v_res_1804_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3_spec__8___redArg(v_o_1801_, v___y_1802_);
lean_dec(v___y_1802_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3(lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1808_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1805_);
v___x_1809_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3_spec__8___redArg(v___x_1808_, v___y_1806_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3___boxed(lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3(v___y_1810_, v___y_1811_);
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___lam__0(lean_object* v___x_1814_, lean_object* v_entry_1815_, lean_object* v_s_1816_){
_start:
{
lean_object* v_addEntryFn_1817_; lean_object* v_importedEntries_1818_; lean_object* v_state_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1827_; 
v_addEntryFn_1817_ = lean_ctor_get(v___x_1814_, 3);
lean_inc(v_addEntryFn_1817_);
lean_dec_ref(v___x_1814_);
v_importedEntries_1818_ = lean_ctor_get(v_s_1816_, 0);
v_state_1819_ = lean_ctor_get(v_s_1816_, 1);
v_isSharedCheck_1827_ = !lean_is_exclusive(v_s_1816_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1821_ = v_s_1816_;
v_isShared_1822_ = v_isSharedCheck_1827_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_state_1819_);
lean_inc(v_importedEntries_1818_);
lean_dec(v_s_1816_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1827_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v_state_1823_; lean_object* v___x_1825_; 
v_state_1823_ = lean_apply_2(v_addEntryFn_1817_, v_state_1819_, v_entry_1815_);
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 1, v_state_1823_);
v___x_1825_ = v___x_1821_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_importedEntries_1818_);
lean_ctor_set(v_reuseFailAlloc_1826_, 1, v_state_1823_);
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
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1828_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4_spec__10___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4_spec__10___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4_spec__10___redArg___closed__0);
v___x_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1828_);
return v___x_1829_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1830_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1831_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_1832_ = lean_unsigned_to_nat(0u);
v___x_1833_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1832_);
lean_ctor_set(v___x_1833_, 1, v___x_1832_);
lean_ctor_set(v___x_1833_, 2, v___x_1832_);
lean_ctor_set(v___x_1833_, 3, v___x_1832_);
lean_ctor_set(v___x_1833_, 4, v___x_1831_);
lean_ctor_set(v___x_1833_, 5, v___x_1831_);
lean_ctor_set(v___x_1833_, 6, v___x_1831_);
lean_ctor_set(v___x_1833_, 7, v___x_1831_);
lean_ctor_set(v___x_1833_, 8, v___x_1831_);
lean_ctor_set(v___x_1833_, 9, v___x_1831_);
lean_ctor_set(v___x_1833_, 10, v___x_1831_);
lean_ctor_set(v___x_1833_, 11, v___x_1830_);
return v___x_1833_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1834_ = lean_unsigned_to_nat(32u);
v___x_1835_ = lean_mk_empty_array_with_capacity(v___x_1834_);
v___x_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1835_);
return v___x_1836_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
size_t v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1837_ = ((size_t)5ULL);
v___x_1838_ = lean_unsigned_to_nat(0u);
v___x_1839_ = lean_unsigned_to_nat(32u);
v___x_1840_ = lean_mk_empty_array_with_capacity(v___x_1839_);
v___x_1841_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_1842_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1842_, 0, v___x_1841_);
lean_ctor_set(v___x_1842_, 1, v___x_1840_);
lean_ctor_set(v___x_1842_, 2, v___x_1838_);
lean_ctor_set(v___x_1842_, 3, v___x_1838_);
lean_ctor_set_usize(v___x_1842_, 4, v___x_1837_);
return v___x_1842_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1843_ = lean_box(1);
v___x_1844_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_1845_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_1846_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1845_);
lean_ctor_set(v___x_1846_, 1, v___x_1844_);
lean_ctor_set(v___x_1846_, 2, v___x_1843_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
lean_object* v___x_1851_; lean_object* v_toCold_1852_; lean_object* v_env_1853_; lean_object* v_options_1854_; uint8_t v___x_1855_; lean_object* v_env_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1851_ = lean_st_ref_get(v___y_1849_);
v_toCold_1852_ = lean_ctor_get(v___y_1848_, 0);
v_env_1853_ = lean_ctor_get(v___x_1851_, 0);
lean_inc_ref(v_env_1853_);
lean_dec(v___x_1851_);
v_options_1854_ = lean_ctor_get(v_toCold_1852_, 2);
v___x_1855_ = 0;
v_env_1856_ = l_Lean_Environment_setRecordingDeps(v_env_1853_, v___x_1855_);
v___x_1857_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_1858_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__4);
lean_inc_ref(v_options_1854_);
v___x_1859_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1859_, 0, v_env_1856_);
lean_ctor_set(v___x_1859_, 1, v___x_1857_);
lean_ctor_set(v___x_1859_, 2, v___x_1858_);
lean_ctor_set(v___x_1859_, 3, v_options_1854_);
v___x_1860_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1859_);
lean_ctor_set(v___x_1860_, 1, v_msgData_1847_);
v___x_1861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1860_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
lean_object* v_res_1866_; 
v_res_1866_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0(v_msgData_1862_, v___y_1863_, v___y_1864_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
return v_res_1866_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0(void){
_start:
{
lean_object* v___x_1867_; double v___x_1868_; 
v___x_1867_ = lean_unsigned_to_nat(0u);
v___x_1868_ = lean_float_of_nat(v___x_1867_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__9(lean_object* v_cls_1871_, lean_object* v_msg_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_){
_start:
{
lean_object* v_ref_1876_; lean_object* v___x_1877_; lean_object* v_a_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1923_; 
v_ref_1876_ = lean_ctor_get(v___y_1873_, 2);
v___x_1877_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0(v_msg_1872_, v___y_1873_, v___y_1874_);
v_a_1878_ = lean_ctor_get(v___x_1877_, 0);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1880_ = v___x_1877_;
v_isShared_1881_ = v_isSharedCheck_1923_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_a_1878_);
lean_dec(v___x_1877_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1923_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1882_; lean_object* v_traceState_1883_; lean_object* v_env_1884_; lean_object* v_nextMacroScope_1885_; lean_object* v_ngen_1886_; lean_object* v_auxDeclNGen_1887_; lean_object* v_cache_1888_; lean_object* v_recordedDeps_1889_; lean_object* v_messages_1890_; lean_object* v_infoState_1891_; lean_object* v_snapshotTasks_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1922_; 
v___x_1882_ = lean_st_ref_take(v___y_1874_);
v_traceState_1883_ = lean_ctor_get(v___x_1882_, 4);
v_env_1884_ = lean_ctor_get(v___x_1882_, 0);
v_nextMacroScope_1885_ = lean_ctor_get(v___x_1882_, 1);
v_ngen_1886_ = lean_ctor_get(v___x_1882_, 2);
v_auxDeclNGen_1887_ = lean_ctor_get(v___x_1882_, 3);
v_cache_1888_ = lean_ctor_get(v___x_1882_, 5);
v_recordedDeps_1889_ = lean_ctor_get(v___x_1882_, 6);
v_messages_1890_ = lean_ctor_get(v___x_1882_, 7);
v_infoState_1891_ = lean_ctor_get(v___x_1882_, 8);
v_snapshotTasks_1892_ = lean_ctor_get(v___x_1882_, 9);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1894_ = v___x_1882_;
v_isShared_1895_ = v_isSharedCheck_1922_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_snapshotTasks_1892_);
lean_inc(v_infoState_1891_);
lean_inc(v_messages_1890_);
lean_inc(v_recordedDeps_1889_);
lean_inc(v_cache_1888_);
lean_inc(v_traceState_1883_);
lean_inc(v_auxDeclNGen_1887_);
lean_inc(v_ngen_1886_);
lean_inc(v_nextMacroScope_1885_);
lean_inc(v_env_1884_);
lean_dec(v___x_1882_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1922_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
uint64_t v_tid_1896_; lean_object* v_traces_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1921_; 
v_tid_1896_ = lean_ctor_get_uint64(v_traceState_1883_, sizeof(void*)*1);
v_traces_1897_ = lean_ctor_get(v_traceState_1883_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v_traceState_1883_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1899_ = v_traceState_1883_;
v_isShared_1900_ = v_isSharedCheck_1921_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_traces_1897_);
lean_dec(v_traceState_1883_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1921_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; double v___x_1903_; uint8_t v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1912_; 
v___x_1901_ = lean_box(0);
v___x_1902_ = lean_box(0);
v___x_1903_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0);
v___x_1904_ = 0;
v___x_1905_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44_spec__46___closed__0));
v___x_1906_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1906_, 0, v_cls_1871_);
lean_ctor_set(v___x_1906_, 1, v___x_1902_);
lean_ctor_set(v___x_1906_, 2, v___x_1905_);
lean_ctor_set_float(v___x_1906_, sizeof(void*)*3, v___x_1903_);
lean_ctor_set_float(v___x_1906_, sizeof(void*)*3 + 8, v___x_1903_);
lean_ctor_set_uint8(v___x_1906_, sizeof(void*)*3 + 16, v___x_1904_);
v___x_1907_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__1));
v___x_1908_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1906_);
lean_ctor_set(v___x_1908_, 1, v_a_1878_);
lean_ctor_set(v___x_1908_, 2, v___x_1907_);
lean_inc(v_ref_1876_);
v___x_1909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1909_, 0, v_ref_1876_);
lean_ctor_set(v___x_1909_, 1, v___x_1908_);
v___x_1910_ = l_Lean_PersistentArray_push___redArg(v_traces_1897_, v___x_1909_);
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 0, v___x_1910_);
v___x_1912_ = v___x_1899_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v___x_1910_);
lean_ctor_set_uint64(v_reuseFailAlloc_1920_, sizeof(void*)*1, v_tid_1896_);
v___x_1912_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
lean_object* v___x_1914_; 
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 4, v___x_1912_);
v___x_1914_ = v___x_1894_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_env_1884_);
lean_ctor_set(v_reuseFailAlloc_1919_, 1, v_nextMacroScope_1885_);
lean_ctor_set(v_reuseFailAlloc_1919_, 2, v_ngen_1886_);
lean_ctor_set(v_reuseFailAlloc_1919_, 3, v_auxDeclNGen_1887_);
lean_ctor_set(v_reuseFailAlloc_1919_, 4, v___x_1912_);
lean_ctor_set(v_reuseFailAlloc_1919_, 5, v_cache_1888_);
lean_ctor_set(v_reuseFailAlloc_1919_, 6, v_recordedDeps_1889_);
lean_ctor_set(v_reuseFailAlloc_1919_, 7, v_messages_1890_);
lean_ctor_set(v_reuseFailAlloc_1919_, 8, v_infoState_1891_);
lean_ctor_set(v_reuseFailAlloc_1919_, 9, v_snapshotTasks_1892_);
v___x_1914_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
lean_object* v___x_1915_; lean_object* v___x_1917_; 
v___x_1915_ = lean_st_ref_put(v___y_1874_, v___x_1914_);
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 0, v___x_1901_);
v___x_1917_ = v___x_1880_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v___x_1901_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__9___boxed(lean_object* v_cls_1924_, lean_object* v_msg_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_){
_start:
{
lean_object* v_res_1929_; 
v_res_1929_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__9(v_cls_1924_, v_msg_1925_, v___y_1926_, v___y_1927_);
lean_dec(v___y_1927_);
lean_dec_ref(v___y_1926_);
return v_res_1929_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14_spec__19___redArg(lean_object* v_keys_1930_, lean_object* v_i_1931_, lean_object* v_k_1932_){
_start:
{
lean_object* v___x_1933_; uint8_t v___x_1934_; 
v___x_1933_ = lean_array_get_size(v_keys_1930_);
v___x_1934_ = lean_nat_dec_lt(v_i_1931_, v___x_1933_);
if (v___x_1934_ == 0)
{
lean_dec(v_i_1931_);
return v___x_1934_;
}
else
{
lean_object* v_k_x27_1935_; uint8_t v___x_1936_; 
v_k_x27_1935_ = lean_array_fget_borrowed(v_keys_1930_, v_i_1931_);
v___x_1936_ = l_Lean_instBEqExtraModUse_beq(v_k_1932_, v_k_x27_1935_);
if (v___x_1936_ == 0)
{
lean_object* v___x_1937_; lean_object* v___x_1938_; 
v___x_1937_ = lean_unsigned_to_nat(1u);
v___x_1938_ = lean_nat_add(v_i_1931_, v___x_1937_);
lean_dec(v_i_1931_);
v_i_1931_ = v___x_1938_;
goto _start;
}
else
{
lean_dec(v_i_1931_);
return v___x_1934_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14_spec__19___redArg___boxed(lean_object* v_keys_1940_, lean_object* v_i_1941_, lean_object* v_k_1942_){
_start:
{
uint8_t v_res_1943_; lean_object* v_r_1944_; 
v_res_1943_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14_spec__19___redArg(v_keys_1940_, v_i_1941_, v_k_1942_);
lean_dec_ref(v_k_1942_);
lean_dec_ref(v_keys_1940_);
v_r_1944_ = lean_box(v_res_1943_);
return v_r_1944_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14___redArg(lean_object* v_x_1945_, size_t v_x_1946_, lean_object* v_x_1947_){
_start:
{
if (lean_obj_tag(v_x_1945_) == 0)
{
lean_object* v_es_1948_; lean_object* v___x_1949_; size_t v___x_1950_; size_t v___x_1951_; lean_object* v_j_1952_; lean_object* v___x_1953_; 
v_es_1948_ = lean_ctor_get(v_x_1945_, 0);
v___x_1949_ = lean_box(2);
v___x_1950_ = ((size_t)31ULL);
v___x_1951_ = lean_usize_land(v_x_1946_, v___x_1950_);
v_j_1952_ = lean_usize_to_nat(v___x_1951_);
v___x_1953_ = lean_array_get_borrowed(v___x_1949_, v_es_1948_, v_j_1952_);
lean_dec(v_j_1952_);
switch(lean_obj_tag(v___x_1953_))
{
case 0:
{
lean_object* v_key_1954_; uint8_t v___x_1955_; 
v_key_1954_ = lean_ctor_get(v___x_1953_, 0);
v___x_1955_ = l_Lean_instBEqExtraModUse_beq(v_x_1947_, v_key_1954_);
return v___x_1955_;
}
case 1:
{
lean_object* v_node_1956_; size_t v___x_1957_; size_t v___x_1958_; 
v_node_1956_ = lean_ctor_get(v___x_1953_, 0);
v___x_1957_ = ((size_t)5ULL);
v___x_1958_ = lean_usize_shift_right(v_x_1946_, v___x_1957_);
v_x_1945_ = v_node_1956_;
v_x_1946_ = v___x_1958_;
goto _start;
}
default: 
{
uint8_t v___x_1960_; 
v___x_1960_ = 0;
return v___x_1960_;
}
}
}
else
{
lean_object* v_ks_1961_; lean_object* v___x_1962_; uint8_t v___x_1963_; 
v_ks_1961_ = lean_ctor_get(v_x_1945_, 0);
v___x_1962_ = lean_unsigned_to_nat(0u);
v___x_1963_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14_spec__19___redArg(v_ks_1961_, v___x_1962_, v_x_1947_);
return v___x_1963_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14___redArg___boxed(lean_object* v_x_1964_, lean_object* v_x_1965_, lean_object* v_x_1966_){
_start:
{
size_t v_x_46787__boxed_1967_; uint8_t v_res_1968_; lean_object* v_r_1969_; 
v_x_46787__boxed_1967_ = lean_unbox_usize(v_x_1965_);
lean_dec(v_x_1965_);
v_res_1968_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14___redArg(v_x_1964_, v_x_46787__boxed_1967_, v_x_1966_);
lean_dec_ref(v_x_1966_);
lean_dec_ref(v_x_1964_);
v_r_1969_ = lean_box(v_res_1968_);
return v_r_1969_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg(lean_object* v_x_1970_, lean_object* v_x_1971_){
_start:
{
uint64_t v___x_1972_; size_t v___x_1973_; uint8_t v___x_1974_; 
v___x_1972_ = l_Lean_instHashableExtraModUse_hash(v_x_1971_);
v___x_1973_ = lean_uint64_to_usize(v___x_1972_);
v___x_1974_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14___redArg(v_x_1970_, v___x_1973_, v_x_1971_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_x_1975_, lean_object* v_x_1976_){
_start:
{
uint8_t v_res_1977_; lean_object* v_r_1978_; 
v_res_1977_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg(v_x_1975_, v_x_1976_);
lean_dec_ref(v_x_1976_);
lean_dec_ref(v_x_1975_);
v_r_1978_ = lean_box(v_res_1977_);
return v_r_1978_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1979_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4_spec__10___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4_spec__10___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4_spec__10___redArg___closed__0);
v___x_1980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1979_);
return v___x_1980_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___x_1981_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__0);
v___x_1982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1981_);
lean_ctor_set(v___x_1982_, 1, v___x_1981_);
return v___x_1982_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__2(void){
_start:
{
lean_object* v___x_1983_; 
v___x_1983_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_1983_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__6(void){
_start:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; 
v___x_1988_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__5));
v___x_1989_ = l_Lean_stringToMessageData(v___x_1988_);
return v___x_1989_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__8(void){
_start:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1991_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__7));
v___x_1992_ = l_Lean_stringToMessageData(v___x_1991_);
return v___x_1992_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__9(void){
_start:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1993_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44_spec__46___closed__0));
v___x_1994_ = l_Lean_stringToMessageData(v___x_1993_);
return v___x_1994_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__11(void){
_start:
{
lean_object* v_cls_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; 
v_cls_1997_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__4));
v___x_1998_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__10));
v___x_1999_ = l_Lean_Name_append(v___x_1998_, v_cls_1997_);
return v___x_1999_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__13(void){
_start:
{
lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_2001_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__12));
v___x_2002_ = l_Lean_stringToMessageData(v___x_2001_);
return v___x_2002_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__14(void){
_start:
{
lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_2003_ = ((lean_object*)(l_Lean_Linter_mkSinceHint___closed__5));
v___x_2004_ = l_Lean_stringToMessageData(v___x_2003_);
return v___x_2004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4(lean_object* v_mod_2009_, uint8_t v_isMeta_2010_, lean_object* v_hint_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_){
_start:
{
lean_object* v___y_2016_; lean_object* v___y_2017_; lean_object* v___y_2018_; lean_object* v___y_2019_; lean_object* v___y_2020_; lean_object* v___y_2021_; lean_object* v___y_2022_; lean_object* v___y_2023_; lean_object* v___y_2024_; lean_object* v___y_2025_; lean_object* v___y_2026_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v_env_2033_; uint8_t v_isExporting_2034_; lean_object* v_entry_2035_; lean_object* v___x_2036_; lean_object* v_env_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; uint8_t v___x_2042_; 
v___x_2031_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__2);
v___x_2032_ = lean_st_ref_get(v___y_2013_);
v_env_2033_ = lean_ctor_get(v___x_2032_, 0);
lean_inc_ref(v_env_2033_);
lean_dec(v___x_2032_);
v_isExporting_2034_ = lean_ctor_get_uint8(v_env_2033_, sizeof(void*)*13);
lean_dec_ref(v_env_2033_);
lean_inc(v_mod_2009_);
v_entry_2035_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2035_, 0, v_mod_2009_);
lean_ctor_set_uint8(v_entry_2035_, sizeof(void*)*1, v_isExporting_2034_);
lean_ctor_set_uint8(v_entry_2035_, sizeof(void*)*1 + 1, v_isMeta_2010_);
v___x_2036_ = lean_st_ref_get(v___y_2013_);
v_env_2037_ = lean_ctor_get(v___x_2036_, 0);
lean_inc_ref(v_env_2037_);
lean_dec(v___x_2036_);
v___x_2038_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2039_ = lean_box(1);
v___x_2040_ = lean_box(0);
v___x_2041_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2031_, v___x_2038_, v_env_2037_, v___x_2039_, v___x_2040_);
v___x_2042_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg(v___x_2041_, v_entry_2035_);
lean_dec(v___x_2041_);
if (v___x_2042_ == 0)
{
lean_object* v_toCold_2043_; lean_object* v_options_2044_; lean_object* v_inheritedTraceOptions_2045_; uint8_t v_hasTrace_2046_; lean_object* v___f_2047_; uint8_t v___x_2048_; lean_object* v___y_2050_; 
v_toCold_2043_ = lean_ctor_get(v___y_2012_, 0);
v_options_2044_ = lean_ctor_get(v_toCold_2043_, 2);
v_inheritedTraceOptions_2045_ = lean_ctor_get(v_toCold_2043_, 11);
v_hasTrace_2046_ = lean_ctor_get_uint8(v_options_2044_, sizeof(void*)*1);
v___f_2047_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___lam__0), 3, 2);
lean_closure_set(v___f_2047_, 0, v___x_2038_);
lean_closure_set(v___f_2047_, 1, v_entry_2035_);
v___x_2048_ = 1;
if (v_hasTrace_2046_ == 0)
{
lean_dec(v_hint_2011_);
lean_dec(v_mod_2009_);
v___y_2050_ = v___y_2013_;
goto v___jp_2049_;
}
else
{
lean_object* v_cls_2068_; lean_object* v___y_2070_; lean_object* v___y_2071_; lean_object* v___y_2075_; lean_object* v___y_2076_; lean_object* v___x_2088_; uint8_t v___x_2089_; 
v_cls_2068_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__4));
v___x_2088_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__11);
v___x_2089_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2045_, v_options_2044_, v___x_2088_);
if (v___x_2089_ == 0)
{
lean_dec(v_hint_2011_);
lean_dec(v_mod_2009_);
v___y_2050_ = v___y_2013_;
goto v___jp_2049_;
}
else
{
lean_object* v___x_2090_; lean_object* v___y_2092_; 
v___x_2090_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__13);
if (v_isExporting_2034_ == 0)
{
lean_object* v___x_2099_; 
v___x_2099_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__17));
v___y_2092_ = v___x_2099_;
goto v___jp_2091_;
}
else
{
lean_object* v___x_2100_; 
v___x_2100_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__18));
v___y_2092_ = v___x_2100_;
goto v___jp_2091_;
}
v___jp_2091_:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; 
lean_inc_ref(v___y_2092_);
v___x_2093_ = l_Lean_stringToMessageData(v___y_2092_);
v___x_2094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2090_);
lean_ctor_set(v___x_2094_, 1, v___x_2093_);
v___x_2095_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__14);
v___x_2096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2094_);
lean_ctor_set(v___x_2096_, 1, v___x_2095_);
if (v_isMeta_2010_ == 0)
{
lean_object* v___x_2097_; 
v___x_2097_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__15));
v___y_2075_ = v___x_2096_;
v___y_2076_ = v___x_2097_;
goto v___jp_2074_;
}
else
{
lean_object* v___x_2098_; 
v___x_2098_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__16));
v___y_2075_ = v___x_2096_;
v___y_2076_ = v___x_2098_;
goto v___jp_2074_;
}
}
}
v___jp_2069_:
{
lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2072_, 0, v___y_2070_);
lean_ctor_set(v___x_2072_, 1, v___y_2071_);
v___x_2073_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__9(v_cls_2068_, v___x_2072_, v___y_2012_, v___y_2013_);
if (lean_obj_tag(v___x_2073_) == 0)
{
lean_dec_ref_known(v___x_2073_, 1);
v___y_2050_ = v___y_2013_;
goto v___jp_2049_;
}
else
{
lean_dec_ref(v___f_2047_);
return v___x_2073_;
}
}
v___jp_2074_:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; uint8_t v___x_2083_; 
lean_inc_ref(v___y_2076_);
v___x_2077_ = l_Lean_stringToMessageData(v___y_2076_);
v___x_2078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2078_, 0, v___y_2075_);
lean_ctor_set(v___x_2078_, 1, v___x_2077_);
v___x_2079_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__6);
v___x_2080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2078_);
lean_ctor_set(v___x_2080_, 1, v___x_2079_);
v___x_2081_ = l_Lean_MessageData_ofName(v_mod_2009_);
v___x_2082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2080_);
lean_ctor_set(v___x_2082_, 1, v___x_2081_);
v___x_2083_ = l_Lean_Name_isAnonymous(v_hint_2011_);
if (v___x_2083_ == 0)
{
lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2084_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__8);
v___x_2085_ = l_Lean_MessageData_ofName(v_hint_2011_);
v___x_2086_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2084_);
lean_ctor_set(v___x_2086_, 1, v___x_2085_);
v___y_2070_ = v___x_2082_;
v___y_2071_ = v___x_2086_;
goto v___jp_2069_;
}
else
{
lean_object* v___x_2087_; 
lean_dec(v_hint_2011_);
v___x_2087_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__9);
v___y_2070_ = v___x_2082_;
v___y_2071_ = v___x_2087_;
goto v___jp_2069_;
}
}
}
v___jp_2049_:
{
lean_object* v___x_2051_; lean_object* v_toEnvExtension_2052_; lean_object* v_env_2053_; lean_object* v_nextMacroScope_2054_; lean_object* v_ngen_2055_; lean_object* v_auxDeclNGen_2056_; lean_object* v_traceState_2057_; lean_object* v_recordedDeps_2058_; lean_object* v_messages_2059_; lean_object* v_infoState_2060_; lean_object* v_snapshotTasks_2061_; lean_object* v_asyncMode_2062_; uint8_t v_logWrites_2063_; lean_object* v___x_2064_; 
v___x_2051_ = lean_st_ref_take(v___y_2050_);
v_toEnvExtension_2052_ = lean_ctor_get(v___x_2038_, 0);
v_env_2053_ = lean_ctor_get(v___x_2051_, 0);
lean_inc_ref(v_env_2053_);
v_nextMacroScope_2054_ = lean_ctor_get(v___x_2051_, 1);
lean_inc(v_nextMacroScope_2054_);
v_ngen_2055_ = lean_ctor_get(v___x_2051_, 2);
lean_inc_ref(v_ngen_2055_);
v_auxDeclNGen_2056_ = lean_ctor_get(v___x_2051_, 3);
lean_inc_ref(v_auxDeclNGen_2056_);
v_traceState_2057_ = lean_ctor_get(v___x_2051_, 4);
lean_inc_ref(v_traceState_2057_);
v_recordedDeps_2058_ = lean_ctor_get(v___x_2051_, 6);
lean_inc_ref(v_recordedDeps_2058_);
v_messages_2059_ = lean_ctor_get(v___x_2051_, 7);
lean_inc_ref(v_messages_2059_);
v_infoState_2060_ = lean_ctor_get(v___x_2051_, 8);
lean_inc_ref(v_infoState_2060_);
v_snapshotTasks_2061_ = lean_ctor_get(v___x_2051_, 9);
lean_inc_ref(v_snapshotTasks_2061_);
lean_dec(v___x_2051_);
v_asyncMode_2062_ = lean_ctor_get(v_toEnvExtension_2052_, 2);
v_logWrites_2063_ = lean_ctor_get_uint8(v_toEnvExtension_2052_, sizeof(void*)*6);
v___x_2064_ = lean_box(0);
if (v_logWrites_2063_ == 0)
{
lean_object* v___x_2065_; 
lean_inc_ref(v_toEnvExtension_2052_);
v___x_2065_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2052_, v_env_2053_, v___f_2047_, v_asyncMode_2062_, v___x_2040_, v___x_2048_);
v___y_2016_ = v_recordedDeps_2058_;
v___y_2017_ = v_messages_2059_;
v___y_2018_ = v___y_2050_;
v___y_2019_ = v_infoState_2060_;
v___y_2020_ = v_ngen_2055_;
v___y_2021_ = v_auxDeclNGen_2056_;
v___y_2022_ = v___x_2064_;
v___y_2023_ = v_traceState_2057_;
v___y_2024_ = v_snapshotTasks_2061_;
v___y_2025_ = v_nextMacroScope_2054_;
v___y_2026_ = v___x_2065_;
goto v___jp_2015_;
}
else
{
lean_object* v___x_2066_; lean_object* v___x_2067_; 
lean_inc_ref_n(v_toEnvExtension_2052_, 2);
v___x_2066_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2052_, v_env_2053_);
lean_dec_ref(v_env_2053_);
v___x_2067_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2052_, v___x_2066_, v___f_2047_, v_asyncMode_2062_, v___x_2040_, v___x_2048_);
v___y_2016_ = v_recordedDeps_2058_;
v___y_2017_ = v_messages_2059_;
v___y_2018_ = v___y_2050_;
v___y_2019_ = v_infoState_2060_;
v___y_2020_ = v_ngen_2055_;
v___y_2021_ = v_auxDeclNGen_2056_;
v___y_2022_ = v___x_2064_;
v___y_2023_ = v_traceState_2057_;
v___y_2024_ = v_snapshotTasks_2061_;
v___y_2025_ = v_nextMacroScope_2054_;
v___y_2026_ = v___x_2067_;
goto v___jp_2015_;
}
}
}
else
{
lean_object* v___x_2101_; lean_object* v___x_2102_; 
lean_dec_ref_known(v_entry_2035_, 1);
lean_dec(v_hint_2011_);
lean_dec(v_mod_2009_);
v___x_2101_ = lean_box(0);
v___x_2102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2101_);
return v___x_2102_;
}
v___jp_2015_:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2027_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__1);
v___x_2028_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2028_, 0, v___y_2026_);
lean_ctor_set(v___x_2028_, 1, v___y_2025_);
lean_ctor_set(v___x_2028_, 2, v___y_2020_);
lean_ctor_set(v___x_2028_, 3, v___y_2021_);
lean_ctor_set(v___x_2028_, 4, v___y_2023_);
lean_ctor_set(v___x_2028_, 5, v___x_2027_);
lean_ctor_set(v___x_2028_, 6, v___y_2016_);
lean_ctor_set(v___x_2028_, 7, v___y_2017_);
lean_ctor_set(v___x_2028_, 8, v___y_2019_);
lean_ctor_set(v___x_2028_, 9, v___y_2024_);
v___x_2029_ = lean_st_ref_put(v___y_2018_, v___x_2028_);
v___x_2030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2030_, 0, v___y_2022_);
return v___x_2030_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___boxed(lean_object* v_mod_2103_, lean_object* v_isMeta_2104_, lean_object* v_hint_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_){
_start:
{
uint8_t v_isMeta_boxed_2109_; lean_object* v_res_2110_; 
v_isMeta_boxed_2109_ = lean_unbox(v_isMeta_2104_);
v_res_2110_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4(v_mod_2103_, v_isMeta_boxed_2109_, v_hint_2105_, v___y_2106_, v___y_2107_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
return v_res_2110_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg(lean_object* v_a_2111_, lean_object* v_x_2112_){
_start:
{
if (lean_obj_tag(v_x_2112_) == 0)
{
lean_object* v___x_2113_; 
v___x_2113_ = lean_box(0);
return v___x_2113_;
}
else
{
lean_object* v_key_2114_; lean_object* v_value_2115_; lean_object* v_tail_2116_; uint8_t v___x_2117_; 
v_key_2114_ = lean_ctor_get(v_x_2112_, 0);
v_value_2115_ = lean_ctor_get(v_x_2112_, 1);
v_tail_2116_ = lean_ctor_get(v_x_2112_, 2);
v___x_2117_ = lean_name_eq(v_key_2114_, v_a_2111_);
if (v___x_2117_ == 0)
{
v_x_2112_ = v_tail_2116_;
goto _start;
}
else
{
lean_object* v___x_2119_; 
lean_inc(v_value_2115_);
v___x_2119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2119_, 0, v_value_2115_);
return v___x_2119_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg___boxed(lean_object* v_a_2120_, lean_object* v_x_2121_){
_start:
{
lean_object* v_res_2122_; 
v_res_2122_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg(v_a_2120_, v_x_2121_);
lean_dec(v_x_2121_);
lean_dec(v_a_2120_);
return v_res_2122_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6___redArg(lean_object* v_m_2123_, lean_object* v_a_2124_){
_start:
{
lean_object* v_buckets_2125_; lean_object* v___x_2126_; uint64_t v___y_2128_; 
v_buckets_2125_ = lean_ctor_get(v_m_2123_, 1);
v___x_2126_ = lean_array_get_size(v_buckets_2125_);
if (lean_obj_tag(v_a_2124_) == 0)
{
uint64_t v___x_2142_; 
v___x_2142_ = 1723ULL;
v___y_2128_ = v___x_2142_;
goto v___jp_2127_;
}
else
{
uint64_t v_hash_2143_; 
v_hash_2143_ = lean_ctor_get_uint64(v_a_2124_, sizeof(void*)*2);
v___y_2128_ = v_hash_2143_;
goto v___jp_2127_;
}
v___jp_2127_:
{
uint64_t v___x_2129_; uint64_t v___x_2130_; uint64_t v_fold_2131_; uint64_t v___x_2132_; uint64_t v___x_2133_; uint64_t v___x_2134_; size_t v___x_2135_; size_t v___x_2136_; size_t v___x_2137_; size_t v___x_2138_; size_t v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; 
v___x_2129_ = 32ULL;
v___x_2130_ = lean_uint64_shift_right(v___y_2128_, v___x_2129_);
v_fold_2131_ = lean_uint64_xor(v___y_2128_, v___x_2130_);
v___x_2132_ = 16ULL;
v___x_2133_ = lean_uint64_shift_right(v_fold_2131_, v___x_2132_);
v___x_2134_ = lean_uint64_xor(v_fold_2131_, v___x_2133_);
v___x_2135_ = lean_uint64_to_usize(v___x_2134_);
v___x_2136_ = lean_usize_of_nat(v___x_2126_);
v___x_2137_ = ((size_t)1ULL);
v___x_2138_ = lean_usize_sub(v___x_2136_, v___x_2137_);
v___x_2139_ = lean_usize_land(v___x_2135_, v___x_2138_);
v___x_2140_ = lean_array_uget_borrowed(v_buckets_2125_, v___x_2139_);
v___x_2141_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg(v_a_2124_, v___x_2140_);
return v___x_2141_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6___redArg___boxed(lean_object* v_m_2144_, lean_object* v_a_2145_){
_start:
{
lean_object* v_res_2146_; 
v_res_2146_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6___redArg(v_m_2144_, v_a_2145_);
lean_dec(v_a_2145_);
lean_dec_ref(v_m_2144_);
return v_res_2146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__5(lean_object* v___x_2147_, lean_object* v_declName_2148_, lean_object* v_as_2149_, size_t v_sz_2150_, size_t v_i_2151_, lean_object* v_b_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_){
_start:
{
uint8_t v___x_2156_; 
v___x_2156_ = lean_usize_dec_lt(v_i_2151_, v_sz_2150_);
if (v___x_2156_ == 0)
{
lean_object* v___x_2157_; 
lean_dec(v_declName_2148_);
v___x_2157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2157_, 0, v_b_2152_);
return v___x_2157_;
}
else
{
lean_object* v___x_2158_; lean_object* v_modules_2159_; lean_object* v___x_2160_; lean_object* v_a_2161_; lean_object* v___x_2162_; lean_object* v_toImport_2163_; lean_object* v_module_2164_; lean_object* v___x_2165_; uint8_t v___x_2166_; lean_object* v___x_2167_; 
v___x_2158_ = l_Lean_Environment_header(v___x_2147_);
v_modules_2159_ = lean_ctor_get(v___x_2158_, 3);
lean_inc_ref(v_modules_2159_);
lean_dec_ref(v___x_2158_);
v___x_2160_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2161_ = lean_array_uget_borrowed(v_as_2149_, v_i_2151_);
v___x_2162_ = lean_array_get(v___x_2160_, v_modules_2159_, v_a_2161_);
lean_dec_ref(v_modules_2159_);
v_toImport_2163_ = lean_ctor_get(v___x_2162_, 0);
lean_inc_ref(v_toImport_2163_);
lean_dec(v___x_2162_);
v_module_2164_ = lean_ctor_get(v_toImport_2163_, 0);
lean_inc(v_module_2164_);
lean_dec_ref(v_toImport_2163_);
v___x_2165_ = lean_box(0);
v___x_2166_ = 0;
lean_inc(v_declName_2148_);
v___x_2167_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4(v_module_2164_, v___x_2166_, v_declName_2148_, v___y_2153_, v___y_2154_);
if (lean_obj_tag(v___x_2167_) == 0)
{
size_t v___x_2168_; size_t v___x_2169_; 
lean_dec_ref_known(v___x_2167_, 1);
v___x_2168_ = ((size_t)1ULL);
v___x_2169_ = lean_usize_add(v_i_2151_, v___x_2168_);
v_i_2151_ = v___x_2169_;
v_b_2152_ = v___x_2165_;
goto _start;
}
else
{
lean_dec(v_declName_2148_);
return v___x_2167_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__5___boxed(lean_object* v___x_2171_, lean_object* v_declName_2172_, lean_object* v_as_2173_, lean_object* v_sz_2174_, lean_object* v_i_2175_, lean_object* v_b_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_){
_start:
{
size_t v_sz_boxed_2180_; size_t v_i_boxed_2181_; lean_object* v_res_2182_; 
v_sz_boxed_2180_ = lean_unbox_usize(v_sz_2174_);
lean_dec(v_sz_2174_);
v_i_boxed_2181_ = lean_unbox_usize(v_i_2175_);
lean_dec(v_i_2175_);
v_res_2182_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__5(v___x_2171_, v_declName_2172_, v_as_2173_, v_sz_boxed_2180_, v_i_boxed_2181_, v_b_2176_, v___y_2177_, v___y_2178_);
lean_dec(v___y_2178_);
lean_dec_ref(v___y_2177_);
lean_dec_ref(v_as_2173_);
lean_dec_ref(v___x_2171_);
return v_res_2182_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2___closed__0(void){
_start:
{
lean_object* v___x_2183_; 
v___x_2183_ = l_Std_HashMap_instInhabited___redArg();
return v___x_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2(lean_object* v_declName_2186_, uint8_t v_isMeta_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_){
_start:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v_env_2196_; lean_object* v___y_2198_; lean_object* v___x_2211_; 
v___x_2191_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2___closed__0);
v___x_2192_ = lean_st_ref_get(v___y_2189_);
v_env_2196_ = lean_ctor_get(v___x_2192_, 0);
lean_inc_ref(v_env_2196_);
lean_dec(v___x_2192_);
v___x_2211_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2196_, v_declName_2186_);
if (lean_obj_tag(v___x_2211_) == 0)
{
lean_dec_ref(v_env_2196_);
lean_dec(v_declName_2186_);
goto v___jp_2193_;
}
else
{
lean_object* v_val_2212_; lean_object* v___x_2213_; lean_object* v_modules_2214_; lean_object* v___x_2215_; uint8_t v___x_2216_; 
v_val_2212_ = lean_ctor_get(v___x_2211_, 0);
lean_inc(v_val_2212_);
lean_dec_ref_known(v___x_2211_, 1);
v___x_2213_ = l_Lean_Environment_header(v_env_2196_);
v_modules_2214_ = lean_ctor_get(v___x_2213_, 3);
lean_inc_ref(v_modules_2214_);
lean_dec_ref(v___x_2213_);
v___x_2215_ = lean_array_get_size(v_modules_2214_);
v___x_2216_ = lean_nat_dec_lt(v_val_2212_, v___x_2215_);
if (v___x_2216_ == 0)
{
lean_dec_ref(v_modules_2214_);
lean_dec(v_val_2212_);
lean_dec_ref(v_env_2196_);
lean_dec(v_declName_2186_);
goto v___jp_2193_;
}
else
{
lean_object* v___x_2217_; lean_object* v___x_2218_; uint8_t v___y_2220_; 
v___x_2217_ = lean_array_fget(v_modules_2214_, v_val_2212_);
lean_dec(v_val_2212_);
lean_dec_ref(v_modules_2214_);
v___x_2218_ = lean_st_ref_get(v___y_2189_);
if (v_isMeta_2187_ == 0)
{
lean_dec(v___x_2218_);
v___y_2220_ = v_isMeta_2187_;
goto v___jp_2219_;
}
else
{
lean_object* v_env_2231_; uint8_t v___x_2232_; 
v_env_2231_ = lean_ctor_get(v___x_2218_, 0);
lean_inc_ref(v_env_2231_);
lean_dec(v___x_2218_);
lean_inc(v_declName_2186_);
v___x_2232_ = l_Lean_isMarkedMeta(v_env_2231_, v_declName_2186_);
if (v___x_2232_ == 0)
{
v___y_2220_ = v_isMeta_2187_;
goto v___jp_2219_;
}
else
{
uint8_t v___x_2233_; 
v___x_2233_ = 0;
v___y_2220_ = v___x_2233_;
goto v___jp_2219_;
}
}
v___jp_2219_:
{
lean_object* v_toImport_2221_; lean_object* v_module_2222_; lean_object* v___x_2223_; 
v_toImport_2221_ = lean_ctor_get(v___x_2217_, 0);
lean_inc_ref(v_toImport_2221_);
lean_dec(v___x_2217_);
v_module_2222_ = lean_ctor_get(v_toImport_2221_, 0);
lean_inc(v_module_2222_);
lean_dec_ref(v_toImport_2221_);
lean_inc(v_declName_2186_);
v___x_2223_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4(v_module_2222_, v___y_2220_, v_declName_2186_, v___y_2188_, v___y_2189_);
if (lean_obj_tag(v___x_2223_) == 0)
{
lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
lean_dec_ref_known(v___x_2223_, 1);
v___x_2224_ = l_Lean_indirectModUseExt;
v___x_2225_ = lean_box(1);
v___x_2226_ = lean_box(0);
lean_inc_ref(v_env_2196_);
v___x_2227_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2191_, v___x_2224_, v_env_2196_, v___x_2225_, v___x_2226_);
v___x_2228_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6___redArg(v___x_2227_, v_declName_2186_);
lean_dec(v___x_2227_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_object* v___x_2229_; 
v___x_2229_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2___closed__1));
v___y_2198_ = v___x_2229_;
goto v___jp_2197_;
}
else
{
lean_object* v_val_2230_; 
v_val_2230_ = lean_ctor_get(v___x_2228_, 0);
lean_inc(v_val_2230_);
lean_dec_ref_known(v___x_2228_, 1);
v___y_2198_ = v_val_2230_;
goto v___jp_2197_;
}
}
else
{
lean_dec_ref(v_env_2196_);
lean_dec(v_declName_2186_);
return v___x_2223_;
}
}
}
}
v___jp_2193_:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2194_ = lean_box(0);
v___x_2195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2194_);
return v___x_2195_;
}
v___jp_2197_:
{
lean_object* v___x_2199_; size_t v_sz_2200_; size_t v___x_2201_; lean_object* v___x_2202_; 
v___x_2199_ = lean_box(0);
v_sz_2200_ = lean_array_size(v___y_2198_);
v___x_2201_ = ((size_t)0ULL);
v___x_2202_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__5(v_env_2196_, v_declName_2186_, v___y_2198_, v_sz_2200_, v___x_2201_, v___x_2199_, v___y_2188_, v___y_2189_);
lean_dec_ref(v___y_2198_);
lean_dec_ref(v_env_2196_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2209_; 
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2209_ == 0)
{
lean_object* v_unused_2210_; 
v_unused_2210_ = lean_ctor_get(v___x_2202_, 0);
lean_dec(v_unused_2210_);
v___x_2204_ = v___x_2202_;
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
else
{
lean_dec(v___x_2202_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2207_; 
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 0, v___x_2199_);
v___x_2207_ = v___x_2204_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v___x_2199_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
else
{
return v___x_2202_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2___boxed(lean_object* v_declName_2234_, lean_object* v_isMeta_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_){
_start:
{
uint8_t v_isMeta_boxed_2239_; lean_object* v_res_2240_; 
v_isMeta_boxed_2239_ = lean_unbox(v_isMeta_2235_);
v_res_2240_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2(v_declName_2234_, v_isMeta_boxed_2239_, v___y_2236_, v___y_2237_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
return v_res_2240_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5(lean_object* v_ref_2241_, lean_object* v_msgData_2242_, uint8_t v_severity_2243_, uint8_t v_isSilent_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v___y_2249_; uint8_t v___y_2250_; lean_object* v___y_2251_; lean_object* v___y_2252_; uint8_t v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v_toCold_2256_; lean_object* v___y_2257_; lean_object* v___y_2286_; lean_object* v___y_2287_; uint8_t v___y_2288_; lean_object* v___y_2289_; uint8_t v___y_2290_; lean_object* v___y_2291_; uint8_t v___y_2292_; lean_object* v___y_2293_; lean_object* v___y_2313_; lean_object* v___y_2314_; uint8_t v___y_2315_; lean_object* v___y_2316_; uint8_t v___y_2317_; uint8_t v___y_2318_; lean_object* v___y_2319_; uint8_t v___y_2323_; uint8_t v___y_2324_; uint8_t v___x_2334_; uint8_t v___y_2336_; uint8_t v___x_2342_; 
v___x_2334_ = 2;
v___x_2342_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2243_, v___x_2334_);
if (v___x_2342_ == 0)
{
v___y_2336_ = v___x_2342_;
goto v___jp_2335_;
}
else
{
uint8_t v___x_2343_; 
lean_inc_ref(v_msgData_2242_);
v___x_2343_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2242_);
if (v___x_2343_ == 0)
{
v___y_2336_ = v___x_2343_;
goto v___jp_2335_;
}
else
{
lean_object* v___x_2344_; lean_object* v___x_2345_; 
lean_dec_ref(v_msgData_2242_);
v___x_2344_ = lean_box(0);
v___x_2345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2344_);
return v___x_2345_;
}
}
v___jp_2248_:
{
lean_object* v_currNamespace_2258_; lean_object* v_openDecls_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v_env_2264_; lean_object* v_nextMacroScope_2265_; lean_object* v_ngen_2266_; lean_object* v_auxDeclNGen_2267_; lean_object* v_traceState_2268_; lean_object* v_cache_2269_; lean_object* v_recordedDeps_2270_; lean_object* v_messages_2271_; lean_object* v_infoState_2272_; lean_object* v_snapshotTasks_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2284_; 
v_currNamespace_2258_ = lean_ctor_get(v_toCold_2256_, 4);
v_openDecls_2259_ = lean_ctor_get(v_toCold_2256_, 5);
lean_inc(v_openDecls_2259_);
lean_inc(v_currNamespace_2258_);
v___x_2260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2260_, 0, v_currNamespace_2258_);
lean_ctor_set(v___x_2260_, 1, v_openDecls_2259_);
v___x_2261_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2260_);
lean_ctor_set(v___x_2261_, 1, v___y_2249_);
lean_inc_ref(v___y_2255_);
lean_inc_ref(v___y_2251_);
v___x_2262_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2262_, 0, v___y_2251_);
lean_ctor_set(v___x_2262_, 1, v___y_2254_);
lean_ctor_set(v___x_2262_, 2, v___y_2252_);
lean_ctor_set(v___x_2262_, 3, v___y_2255_);
lean_ctor_set(v___x_2262_, 4, v___x_2261_);
lean_ctor_set_uint8(v___x_2262_, sizeof(void*)*5, v___y_2250_);
lean_ctor_set_uint8(v___x_2262_, sizeof(void*)*5 + 1, v___y_2253_);
lean_ctor_set_uint8(v___x_2262_, sizeof(void*)*5 + 2, v_isSilent_2244_);
v___x_2263_ = lean_st_ref_take(v___y_2257_);
v_env_2264_ = lean_ctor_get(v___x_2263_, 0);
v_nextMacroScope_2265_ = lean_ctor_get(v___x_2263_, 1);
v_ngen_2266_ = lean_ctor_get(v___x_2263_, 2);
v_auxDeclNGen_2267_ = lean_ctor_get(v___x_2263_, 3);
v_traceState_2268_ = lean_ctor_get(v___x_2263_, 4);
v_cache_2269_ = lean_ctor_get(v___x_2263_, 5);
v_recordedDeps_2270_ = lean_ctor_get(v___x_2263_, 6);
v_messages_2271_ = lean_ctor_get(v___x_2263_, 7);
v_infoState_2272_ = lean_ctor_get(v___x_2263_, 8);
v_snapshotTasks_2273_ = lean_ctor_get(v___x_2263_, 9);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2263_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2275_ = v___x_2263_;
v_isShared_2276_ = v_isSharedCheck_2284_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_snapshotTasks_2273_);
lean_inc(v_infoState_2272_);
lean_inc(v_messages_2271_);
lean_inc(v_recordedDeps_2270_);
lean_inc(v_cache_2269_);
lean_inc(v_traceState_2268_);
lean_inc(v_auxDeclNGen_2267_);
lean_inc(v_ngen_2266_);
lean_inc(v_nextMacroScope_2265_);
lean_inc(v_env_2264_);
lean_dec(v___x_2263_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2284_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2280_; 
v___x_2277_ = lean_box(0);
v___x_2278_ = l_Lean_MessageLog_add(v___x_2262_, v_messages_2271_);
if (v_isShared_2276_ == 0)
{
lean_ctor_set(v___x_2275_, 7, v___x_2278_);
v___x_2280_ = v___x_2275_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_env_2264_);
lean_ctor_set(v_reuseFailAlloc_2283_, 1, v_nextMacroScope_2265_);
lean_ctor_set(v_reuseFailAlloc_2283_, 2, v_ngen_2266_);
lean_ctor_set(v_reuseFailAlloc_2283_, 3, v_auxDeclNGen_2267_);
lean_ctor_set(v_reuseFailAlloc_2283_, 4, v_traceState_2268_);
lean_ctor_set(v_reuseFailAlloc_2283_, 5, v_cache_2269_);
lean_ctor_set(v_reuseFailAlloc_2283_, 6, v_recordedDeps_2270_);
lean_ctor_set(v_reuseFailAlloc_2283_, 7, v___x_2278_);
lean_ctor_set(v_reuseFailAlloc_2283_, 8, v_infoState_2272_);
lean_ctor_set(v_reuseFailAlloc_2283_, 9, v_snapshotTasks_2273_);
v___x_2280_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2281_ = lean_st_ref_put(v___y_2257_, v___x_2280_);
v___x_2282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2277_);
return v___x_2282_;
}
}
}
v___jp_2285_:
{
lean_object* v_fileName_2294_; lean_object* v_fileMap_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2311_; 
v_fileName_2294_ = lean_ctor_get(v___y_2291_, 0);
v_fileMap_2295_ = lean_ctor_get(v___y_2291_, 1);
v___x_2296_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2242_);
v___x_2297_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0(v___x_2296_, v___y_2245_, v___y_2246_);
v_a_2298_ = lean_ctor_get(v___x_2297_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2300_ = v___x_2297_;
v_isShared_2301_ = v_isSharedCheck_2311_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2297_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2311_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
lean_inc_ref_n(v_fileMap_2295_, 2);
v___x_2302_ = l_Lean_FileMap_toPosition(v_fileMap_2295_, v___y_2289_);
lean_dec(v___y_2289_);
v___x_2303_ = l_Lean_FileMap_toPosition(v_fileMap_2295_, v___y_2293_);
lean_dec(v___y_2293_);
v___x_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2303_);
v___x_2305_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40_spec__44_spec__46___closed__0));
if (v___y_2292_ == 0)
{
lean_del_object(v___x_2300_);
lean_dec_ref(v___y_2286_);
v___y_2249_ = v_a_2298_;
v___y_2250_ = v___y_2288_;
v___y_2251_ = v_fileName_2294_;
v___y_2252_ = v___x_2304_;
v___y_2253_ = v___y_2290_;
v___y_2254_ = v___x_2302_;
v___y_2255_ = v___x_2305_;
v_toCold_2256_ = v___y_2287_;
v___y_2257_ = v___y_2246_;
goto v___jp_2248_;
}
else
{
uint8_t v___x_2306_; 
lean_inc(v_a_2298_);
v___x_2306_ = l_Lean_MessageData_hasTag(v___y_2286_, v_a_2298_);
if (v___x_2306_ == 0)
{
lean_object* v___x_2307_; lean_object* v___x_2309_; 
lean_dec_ref_known(v___x_2304_, 1);
lean_dec_ref(v___x_2302_);
lean_dec(v_a_2298_);
v___x_2307_ = lean_box(0);
if (v_isShared_2301_ == 0)
{
lean_ctor_set(v___x_2300_, 0, v___x_2307_);
v___x_2309_ = v___x_2300_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v___x_2307_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
else
{
lean_del_object(v___x_2300_);
v___y_2249_ = v_a_2298_;
v___y_2250_ = v___y_2288_;
v___y_2251_ = v_fileName_2294_;
v___y_2252_ = v___x_2304_;
v___y_2253_ = v___y_2290_;
v___y_2254_ = v___x_2302_;
v___y_2255_ = v___x_2305_;
v_toCold_2256_ = v___y_2287_;
v___y_2257_ = v___y_2246_;
goto v___jp_2248_;
}
}
}
}
v___jp_2312_:
{
lean_object* v___x_2320_; 
v___x_2320_ = l_Lean_Syntax_getTailPos_x3f(v___y_2316_, v___y_2317_);
lean_dec(v___y_2316_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_inc(v___y_2319_);
v___y_2286_ = v___y_2313_;
v___y_2287_ = v___y_2314_;
v___y_2288_ = v___y_2317_;
v___y_2289_ = v___y_2319_;
v___y_2290_ = v___y_2318_;
v___y_2291_ = v___y_2314_;
v___y_2292_ = v___y_2315_;
v___y_2293_ = v___y_2319_;
goto v___jp_2285_;
}
else
{
lean_object* v_val_2321_; 
v_val_2321_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_val_2321_);
lean_dec_ref_known(v___x_2320_, 1);
v___y_2286_ = v___y_2313_;
v___y_2287_ = v___y_2314_;
v___y_2288_ = v___y_2317_;
v___y_2289_ = v___y_2319_;
v___y_2290_ = v___y_2318_;
v___y_2291_ = v___y_2314_;
v___y_2292_ = v___y_2315_;
v___y_2293_ = v_val_2321_;
goto v___jp_2285_;
}
}
v___jp_2322_:
{
lean_object* v_toCold_2325_; lean_object* v_ref_2326_; uint8_t v_suppressElabErrors_2327_; lean_object* v___x_2328_; lean_object* v___f_2329_; lean_object* v_ref_2330_; lean_object* v___x_2331_; 
v_toCold_2325_ = lean_ctor_get(v___y_2245_, 0);
v_ref_2326_ = lean_ctor_get(v___y_2245_, 2);
v_suppressElabErrors_2327_ = lean_ctor_get_uint8(v___y_2245_, sizeof(void*)*3 + 2);
v___x_2328_ = lean_box(v_suppressElabErrors_2327_);
v___f_2329_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2329_, 0, v___x_2328_);
v_ref_2330_ = l_Lean_replaceRef(v_ref_2241_, v_ref_2326_);
v___x_2331_ = l_Lean_Syntax_getPos_x3f(v_ref_2330_, v___y_2323_);
if (lean_obj_tag(v___x_2331_) == 0)
{
lean_object* v___x_2332_; 
v___x_2332_ = lean_unsigned_to_nat(0u);
v___y_2313_ = v___f_2329_;
v___y_2314_ = v_toCold_2325_;
v___y_2315_ = v_suppressElabErrors_2327_;
v___y_2316_ = v_ref_2330_;
v___y_2317_ = v___y_2323_;
v___y_2318_ = v___y_2324_;
v___y_2319_ = v___x_2332_;
goto v___jp_2312_;
}
else
{
lean_object* v_val_2333_; 
v_val_2333_ = lean_ctor_get(v___x_2331_, 0);
lean_inc(v_val_2333_);
lean_dec_ref_known(v___x_2331_, 1);
v___y_2313_ = v___f_2329_;
v___y_2314_ = v_toCold_2325_;
v___y_2315_ = v_suppressElabErrors_2327_;
v___y_2316_ = v_ref_2330_;
v___y_2317_ = v___y_2323_;
v___y_2318_ = v___y_2324_;
v___y_2319_ = v_val_2333_;
goto v___jp_2312_;
}
}
v___jp_2335_:
{
uint8_t v___x_2337_; uint8_t v___x_2338_; 
v___x_2337_ = 1;
v___x_2338_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2243_, v___x_2337_);
if (v___x_2338_ == 0)
{
v___y_2323_ = v___y_2336_;
v___y_2324_ = v_severity_2243_;
goto v___jp_2322_;
}
else
{
lean_object* v___x_2339_; lean_object* v___x_2340_; uint8_t v___x_2341_; 
v___x_2339_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2245_);
v___x_2340_ = l_Lean_warningAsError;
v___x_2341_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5(v___x_2339_, v___x_2340_);
lean_dec_ref(v___x_2339_);
if (v___x_2341_ == 0)
{
v___y_2323_ = v___y_2336_;
v___y_2324_ = v_severity_2243_;
goto v___jp_2322_;
}
else
{
v___y_2323_ = v___y_2336_;
v___y_2324_ = v___x_2334_;
goto v___jp_2322_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5___boxed(lean_object* v_ref_2346_, lean_object* v_msgData_2347_, lean_object* v_severity_2348_, lean_object* v_isSilent_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_){
_start:
{
uint8_t v_severity_boxed_2353_; uint8_t v_isSilent_boxed_2354_; lean_object* v_res_2355_; 
v_severity_boxed_2353_ = lean_unbox(v_severity_2348_);
v_isSilent_boxed_2354_ = lean_unbox(v_isSilent_2349_);
v_res_2355_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5(v_ref_2346_, v_msgData_2347_, v_severity_boxed_2353_, v_isSilent_boxed_2354_, v___y_2350_, v___y_2351_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec(v_ref_2346_);
return v_res_2355_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_msgData_2356_, uint8_t v_severity_2357_, uint8_t v_isSilent_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_){
_start:
{
lean_object* v_ref_2362_; lean_object* v___x_2363_; 
v_ref_2362_ = lean_ctor_get(v___y_2359_, 2);
v___x_2363_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2_spec__5(v_ref_2362_, v_msgData_2356_, v_severity_2357_, v_isSilent_2358_, v___y_2359_, v___y_2360_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_msgData_2364_, lean_object* v_severity_2365_, lean_object* v_isSilent_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
uint8_t v_severity_boxed_2370_; uint8_t v_isSilent_boxed_2371_; lean_object* v_res_2372_; 
v_severity_boxed_2370_ = lean_unbox(v_severity_2365_);
v_isSilent_boxed_2371_ = lean_unbox(v_isSilent_2366_);
v_res_2372_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2(v_msgData_2364_, v_severity_boxed_2370_, v_isSilent_boxed_2371_, v___y_2367_, v___y_2368_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1(lean_object* v_msgData_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_){
_start:
{
uint8_t v___x_2377_; uint8_t v___x_2378_; lean_object* v___x_2379_; 
v___x_2377_ = 1;
v___x_2378_ = 0;
v___x_2379_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1_spec__2(v_msgData_2373_, v___x_2377_, v___x_2378_, v___y_2374_, v___y_2375_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1___boxed(lean_object* v_msgData_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1(v_msgData_2380_, v___y_2381_, v___y_2382_);
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
lean_object* v_ref_2389_; lean_object* v___x_2390_; lean_object* v_a_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2399_; 
v_ref_2389_ = lean_ctor_get(v___y_2386_, 2);
v___x_2390_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0(v_msg_2385_, v___y_2386_, v___y_2387_);
v_a_2391_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2393_ = v___x_2390_;
v_isShared_2394_ = v_isSharedCheck_2399_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_a_2391_);
lean_dec(v___x_2390_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2399_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2395_; lean_object* v___x_2397_; 
lean_inc(v_ref_2389_);
v___x_2395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2395_, 0, v_ref_2389_);
lean_ctor_set(v___x_2395_, 1, v_a_2391_);
if (v_isShared_2394_ == 0)
{
lean_ctor_set_tag(v___x_2393_, 1);
lean_ctor_set(v___x_2393_, 0, v___x_2395_);
v___x_2397_ = v___x_2393_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(1, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0___redArg(v_msg_2400_, v___y_2401_, v___y_2402_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
return v_res_2404_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__1_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; 
v___x_2406_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__0_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2407_ = l_Lean_stringToMessageData(v___x_2406_);
return v___x_2407_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__4_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2411_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__3_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2412_ = l_Lean_MessageData_ofFormat(v___x_2411_);
return v___x_2412_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2414_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__5_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2415_ = l_Lean_stringToMessageData(v___x_2414_);
return v___x_2415_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___x_2417_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2418_ = l_Lean_stringToMessageData(v___x_2417_);
return v___x_2418_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__10_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; 
v___x_2420_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2421_ = l_Lean_stringToMessageData(v___x_2420_);
return v___x_2421_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__13_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; 
v___x_2425_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__12_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2426_ = l_Lean_MessageData_ofFormat(v___x_2425_);
return v___x_2426_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__14_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___x_2427_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__13_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__13_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__13_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2428_ = l_Lean_MessageData_hint_x27(v___x_2427_);
return v___x_2428_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2430_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__15_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2431_ = l_Lean_stringToMessageData(v___x_2430_);
return v___x_2431_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__19_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2435_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__18_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2436_ = l_Lean_MessageData_ofFormat(v___x_2435_);
return v___x_2436_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__24_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2443_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__23_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2444_ = l_Lean_MessageData_ofFormat(v___x_2443_);
return v___x_2444_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__25_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; 
v___x_2445_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__24_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__24_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__24_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2446_, 0, v___x_2445_);
return v___x_2446_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___x_2447_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4_spec__10___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4_spec__10___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4_spec__10___redArg___closed__0);
v___x_2448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2447_);
return v___x_2448_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__27_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2449_ = lean_box(1);
v___x_2450_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_2451_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2452_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2452_, 0, v___x_2451_);
lean_ctor_set(v___x_2452_, 1, v___x_2450_);
lean_ctor_set(v___x_2452_, 2, v___x_2449_);
return v___x_2452_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2455_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_2456_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2457_ = lean_unsigned_to_nat(0u);
v___x_2458_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2457_);
lean_ctor_set(v___x_2458_, 1, v___x_2457_);
lean_ctor_set(v___x_2458_, 2, v___x_2457_);
lean_ctor_set(v___x_2458_, 3, v___x_2457_);
lean_ctor_set(v___x_2458_, 4, v___x_2456_);
lean_ctor_set(v___x_2458_, 5, v___x_2456_);
lean_ctor_set(v___x_2458_, 6, v___x_2456_);
lean_ctor_set(v___x_2458_, 7, v___x_2456_);
lean_ctor_set(v___x_2458_, 8, v___x_2456_);
lean_ctor_set(v___x_2458_, 9, v___x_2456_);
lean_ctor_set(v___x_2458_, 10, v___x_2456_);
lean_ctor_set(v___x_2458_, 11, v___x_2455_);
return v___x_2458_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2459_; 
v___x_2459_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4_spec__10___redArg();
return v___x_2459_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2460_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2461_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2462_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2461_);
lean_ctor_set(v___x_2462_, 1, v___x_2460_);
lean_ctor_set(v___x_2462_, 2, v___x_2460_);
lean_ctor_set(v___x_2462_, 3, v___x_2460_);
lean_ctor_set(v___x_2462_, 4, v___x_2460_);
lean_ctor_set(v___x_2462_, 5, v___x_2460_);
lean_ctor_set(v___x_2462_, 6, v___x_2460_);
return v___x_2462_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; 
v___x_2463_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2464_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2463_);
lean_ctor_set(v___x_2464_, 1, v___x_2463_);
lean_ctor_set(v___x_2464_, 2, v___x_2463_);
lean_ctor_set(v___x_2464_, 3, v___x_2463_);
lean_ctor_set(v___x_2464_, 4, v___x_2463_);
return v___x_2464_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2468_; lean_object* v___x_2469_; 
v___x_2468_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2469_ = l_Lean_MessageData_ofFormat(v___x_2468_);
return v___x_2469_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__37_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; 
v___x_2471_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__36_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2472_ = l_Lean_stringToMessageData(v___x_2471_);
return v___x_2472_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__39_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2474_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__38_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2475_ = l_Lean_stringToMessageData(v___x_2474_);
return v___x_2475_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2477_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__40_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2478_ = l_Lean_stringToMessageData(v___x_2477_);
return v___x_2478_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2480_; lean_object* v___x_2481_; 
v___x_2480_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2481_ = l_Lean_stringToMessageData(v___x_2480_);
return v___x_2481_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; 
v___x_2483_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2484_ = l_Lean_stringToMessageData(v___x_2483_);
return v___x_2484_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__47_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2486_; lean_object* v___x_2487_; 
v___x_2486_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2487_ = l_Lean_stringToMessageData(v___x_2486_);
return v___x_2487_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__49_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2489_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__48_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2490_ = l_Lean_stringToMessageData(v___x_2489_);
return v___x_2490_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__51_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2492_; lean_object* v___x_2493_; 
v___x_2492_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__50_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2493_ = l_Lean_stringToMessageData(v___x_2492_);
return v___x_2493_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__53_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2495_; lean_object* v___x_2496_; 
v___x_2495_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__52_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2496_ = l_Lean_stringToMessageData(v___x_2495_);
return v___x_2496_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__55_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; 
v___x_2498_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__54_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2499_ = l_Lean_stringToMessageData(v___x_2498_);
return v___x_2499_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__57_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2501_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__56_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2502_ = l_Lean_stringToMessageData(v___x_2501_);
return v___x_2502_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__59_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2504_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__58_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2505_ = l_Lean_stringToMessageData(v___x_2504_);
return v___x_2505_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__61_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2507_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__60_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2508_ = l_Lean_stringToMessageData(v___x_2507_);
return v___x_2508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(lean_object* v___x_2509_, lean_object* v___x_2510_, lean_object* v___f_2511_, uint8_t v___x_2512_, lean_object* v___x_2513_, lean_object* v___x_2514_, lean_object* v_a_2515_, lean_object* v_declName_2516_, lean_object* v_stx_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_){
_start:
{
lean_object* v___y_2522_; lean_object* v___y_2523_; lean_object* v___y_2524_; lean_object* v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v___y_2555_; lean_object* v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v___y_2560_; lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2589_; lean_object* v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2592_; lean_object* v___y_2593_; lean_object* v___y_2594_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2611_; lean_object* v_hint_2612_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v___y_2639_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; lean_object* v___x_2646_; uint8_t v___x_2647_; 
v___x_2646_ = l_Lean_Name_mkStr2(v___x_2509_, v___x_2510_);
lean_inc(v_stx_2517_);
v___x_2647_ = l_Lean_Syntax_isOfKind(v_stx_2517_, v___x_2646_);
lean_dec(v___x_2646_);
if (v___x_2647_ == 0)
{
lean_object* v___x_2648_; lean_object* v___x_2649_; 
lean_dec(v_stx_2517_);
lean_dec(v_declName_2516_);
lean_dec_ref(v___x_2514_);
lean_dec(v___x_2513_);
lean_dec_ref(v___f_2511_);
v___x_2648_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2649_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0___redArg(v___x_2648_, v___y_2518_, v___y_2519_);
return v___x_2649_;
}
else
{
lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2655_; lean_object* v___y_2656_; lean_object* v___y_2657_; lean_object* v___y_2658_; lean_object* v___y_2659_; lean_object* v___y_2660_; lean_object* v_val_2661_; lean_object* v___y_2686_; lean_object* v___y_2687_; lean_object* v___y_2688_; lean_object* v___y_2689_; lean_object* v___y_2690_; lean_object* v___y_2691_; lean_object* v___y_2692_; lean_object* v___y_2693_; lean_object* v___y_2698_; lean_object* v___y_2699_; lean_object* v___y_2700_; lean_object* v___y_2701_; lean_object* v___y_2702_; lean_object* v___y_2703_; lean_object* v___y_2704_; uint8_t v___y_2705_; lean_object* v___y_2706_; lean_object* v___y_2707_; lean_object* v___y_2754_; lean_object* v___y_2755_; lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v___y_2759_; lean_object* v___y_2760_; uint8_t v___y_2761_; lean_object* v_msg_2762_; lean_object* v___y_2763_; lean_object* v___y_2764_; lean_object* v___y_2775_; lean_object* v___y_2776_; lean_object* v___y_2777_; lean_object* v___y_2778_; lean_object* v___y_2779_; lean_object* v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v_a_2922_; lean_object* v___y_2940_; lean_object* v___y_2941_; lean_object* v___y_2942_; lean_object* v_since_x3f_2943_; lean_object* v___y_2944_; lean_object* v___y_2945_; lean_object* v___y_2961_; lean_object* v___y_2962_; lean_object* v___y_2963_; lean_object* v_typeChanged_x3f_2964_; lean_object* v___y_2965_; lean_object* v___y_2966_; lean_object* v___y_2978_; lean_object* v_text_x3f_2979_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v_id_x3f_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___x_3004_; uint8_t v___x_3005_; 
v___x_2650_ = lean_unsigned_to_nat(0u);
v___x_2651_ = lean_unsigned_to_nat(1u);
v___x_3004_ = l_Lean_Syntax_getArg(v_stx_2517_, v___x_2651_);
v___x_3005_ = l_Lean_Syntax_isNone(v___x_3004_);
if (v___x_3005_ == 0)
{
uint8_t v___x_3006_; 
lean_inc(v___x_3004_);
v___x_3006_ = l_Lean_Syntax_matchesNull(v___x_3004_, v___x_2651_);
if (v___x_3006_ == 0)
{
lean_object* v___x_3007_; lean_object* v___x_3008_; 
lean_dec(v___x_3004_);
lean_dec(v_stx_2517_);
lean_dec(v_declName_2516_);
lean_dec_ref(v___x_2514_);
lean_dec(v___x_2513_);
lean_dec_ref(v___f_2511_);
v___x_3007_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_3008_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0___redArg(v___x_3007_, v___y_2518_, v___y_2519_);
return v___x_3008_;
}
else
{
lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___x_3009_ = l_Lean_Syntax_getArg(v___x_3004_, v___x_2650_);
lean_dec(v___x_3004_);
v___x_3010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3010_, 0, v___x_3009_);
v_id_x3f_2992_ = v___x_3010_;
v___y_2993_ = v___y_2518_;
v___y_2994_ = v___y_2519_;
goto v___jp_2991_;
}
}
else
{
lean_object* v___x_3011_; 
lean_dec(v___x_3004_);
v___x_3011_ = lean_box(0);
v_id_x3f_2992_ = v___x_3011_;
v___y_2993_ = v___y_2518_;
v___y_2994_ = v___y_2519_;
goto v___jp_2991_;
}
v___jp_2652_:
{
lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; uint8_t v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; 
v___x_2662_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__19_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__19_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__19_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2663_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__21_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2664_ = lean_box(0);
v___x_2665_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__25_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__25_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__25_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2666_, 0, v___f_2511_);
v___x_2667_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2667_, 0, v___x_2663_);
lean_ctor_set(v___x_2667_, 1, v___x_2664_);
lean_ctor_set(v___x_2667_, 2, v___x_2664_);
lean_ctor_set(v___x_2667_, 3, v___x_2664_);
lean_ctor_set(v___x_2667_, 4, v___x_2665_);
lean_ctor_set(v___x_2667_, 5, v___x_2666_);
lean_inc(v_val_2661_);
v___x_2668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2668_, 0, v_val_2661_);
lean_ctor_set(v___x_2668_, 1, v_val_2661_);
v___x_2669_ = l_Lean_Syntax_ofRange(v___x_2668_, v___x_2647_);
v___x_2670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2669_);
v___x_2671_ = 4;
v___x_2672_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2672_, 0, v___x_2667_);
lean_ctor_set(v___x_2672_, 1, v___x_2670_);
lean_ctor_set(v___x_2672_, 2, v___x_2664_);
lean_ctor_set_uint8(v___x_2672_, sizeof(void*)*3, v___x_2671_);
v___x_2673_ = lean_mk_empty_array_with_capacity(v___x_2651_);
v___x_2674_ = lean_array_push(v___x_2673_, v___x_2672_);
v___x_2675_ = l_Lean_MessageData_hint(v___x_2662_, v___x_2674_, v___x_2664_, v___x_2664_, v___x_2512_, v___y_2660_, v___y_2655_);
lean_dec_ref(v___x_2674_);
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_object* v_a_2676_; 
v_a_2676_ = lean_ctor_get(v___x_2675_, 0);
lean_inc(v_a_2676_);
lean_dec_ref_known(v___x_2675_, 1);
v___y_2606_ = v___y_2653_;
v___y_2607_ = v___y_2654_;
v___y_2608_ = v___y_2656_;
v___y_2609_ = v___y_2657_;
v___y_2610_ = v___y_2658_;
v___y_2611_ = v___y_2659_;
v_hint_2612_ = v_a_2676_;
v___y_2613_ = v___y_2660_;
v___y_2614_ = v___y_2655_;
goto v___jp_2605_;
}
else
{
lean_object* v_a_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2684_; 
lean_dec(v___y_2659_);
lean_dec(v___y_2658_);
lean_dec(v___y_2657_);
lean_dec_ref(v___y_2656_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec(v_stx_2517_);
v_a_2677_ = lean_ctor_get(v___x_2675_, 0);
v_isSharedCheck_2684_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2679_ = v___x_2675_;
v_isShared_2680_ = v_isSharedCheck_2684_;
goto v_resetjp_2678_;
}
else
{
lean_inc(v_a_2677_);
lean_dec(v___x_2675_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2684_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
lean_object* v___x_2682_; 
if (v_isShared_2680_ == 0)
{
v___x_2682_ = v___x_2679_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v_a_2677_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
return v___x_2682_;
}
}
}
}
v___jp_2685_:
{
if (lean_obj_tag(v___y_2687_) == 0)
{
lean_dec_ref(v___f_2511_);
v___y_2637_ = v___y_2686_;
v___y_2638_ = v___y_2687_;
v___y_2639_ = v___y_2688_;
v___y_2640_ = v___y_2689_;
v___y_2641_ = v___y_2690_;
v___y_2642_ = v___y_2691_;
v___y_2643_ = v___y_2692_;
v___y_2644_ = v___y_2693_;
goto v___jp_2636_;
}
else
{
lean_object* v_val_2694_; lean_object* v___x_2695_; 
v_val_2694_ = lean_ctor_get(v___y_2687_, 0);
v___x_2695_ = l_Lean_Syntax_getTailPos_x3f(v_val_2694_, v___x_2647_);
if (lean_obj_tag(v___x_2695_) == 1)
{
lean_object* v_val_2696_; 
v_val_2696_ = lean_ctor_get(v___x_2695_, 0);
lean_inc(v_val_2696_);
lean_dec_ref_known(v___x_2695_, 1);
v___y_2653_ = v___y_2686_;
v___y_2654_ = v___y_2687_;
v___y_2655_ = v___y_2688_;
v___y_2656_ = v___y_2689_;
v___y_2657_ = v___y_2690_;
v___y_2658_ = v___y_2691_;
v___y_2659_ = v___y_2692_;
v___y_2660_ = v___y_2693_;
v_val_2661_ = v_val_2696_;
goto v___jp_2652_;
}
else
{
lean_dec(v___x_2695_);
lean_dec_ref(v___f_2511_);
v___y_2637_ = v___y_2686_;
v___y_2638_ = v___y_2687_;
v___y_2639_ = v___y_2688_;
v___y_2640_ = v___y_2689_;
v___y_2641_ = v___y_2690_;
v___y_2642_ = v___y_2691_;
v___y_2643_ = v___y_2692_;
v___y_2644_ = v___y_2693_;
goto v___jp_2636_;
}
}
}
v___jp_2697_:
{
lean_object* v___x_2708_; 
lean_inc_ref(v___y_2698_);
v___x_2708_ = l_Lean_Environment_find_x3f(v___y_2698_, v_declName_2516_, v___x_2512_);
if (lean_obj_tag(v___x_2708_) == 1)
{
lean_object* v_val_2709_; lean_object* v___x_2710_; 
v_val_2709_ = lean_ctor_get(v___x_2708_, 0);
lean_inc(v_val_2709_);
lean_dec_ref_known(v___x_2708_, 1);
v___x_2710_ = l_Lean_Environment_find_x3f(v___y_2698_, v___y_2704_, v___x_2512_);
if (lean_obj_tag(v___x_2710_) == 1)
{
lean_object* v_val_2711_; uint8_t v___x_2712_; uint8_t v___x_2713_; uint8_t v___x_2714_; lean_object* v___x_2715_; uint64_t v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; 
v_val_2711_ = lean_ctor_get(v___x_2710_, 0);
lean_inc(v_val_2711_);
lean_dec_ref_known(v___x_2710_, 1);
v___x_2712_ = 1;
v___x_2713_ = 0;
v___x_2714_ = 2;
v___x_2715_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_2715_, 0, v___x_2512_);
lean_ctor_set_uint8(v___x_2715_, 1, v___x_2512_);
lean_ctor_set_uint8(v___x_2715_, 2, v___x_2512_);
lean_ctor_set_uint8(v___x_2715_, 3, v___x_2512_);
lean_ctor_set_uint8(v___x_2715_, 4, v___x_2512_);
lean_ctor_set_uint8(v___x_2715_, 5, v___y_2705_);
lean_ctor_set_uint8(v___x_2715_, 6, v___y_2705_);
lean_ctor_set_uint8(v___x_2715_, 7, v___x_2512_);
lean_ctor_set_uint8(v___x_2715_, 8, v___y_2705_);
lean_ctor_set_uint8(v___x_2715_, 9, v___x_2712_);
lean_ctor_set_uint8(v___x_2715_, 10, v___x_2713_);
lean_ctor_set_uint8(v___x_2715_, 11, v___y_2705_);
lean_ctor_set_uint8(v___x_2715_, 12, v___y_2705_);
lean_ctor_set_uint8(v___x_2715_, 13, v___y_2705_);
lean_ctor_set_uint8(v___x_2715_, 14, v___x_2714_);
lean_ctor_set_uint8(v___x_2715_, 15, v___y_2705_);
lean_ctor_set_uint8(v___x_2715_, 16, v___y_2705_);
lean_ctor_set_uint8(v___x_2715_, 17, v___y_2705_);
lean_ctor_set_uint8(v___x_2715_, 18, v___y_2705_);
lean_ctor_set_uint8(v___x_2715_, 19, v___x_2512_);
v___x_2716_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2715_);
v___x_2717_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2717_, 0, v___x_2715_);
lean_ctor_set_uint64(v___x_2717_, sizeof(void*)*1, v___x_2716_);
v___x_2718_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_2719_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__27_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__27_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__27_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2720_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__28_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2721_ = lean_box(0);
lean_inc(v___x_2513_);
v___x_2722_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2722_, 0, v___x_2717_);
lean_ctor_set(v___x_2722_, 1, v___x_2513_);
lean_ctor_set(v___x_2722_, 2, v___x_2719_);
lean_ctor_set(v___x_2722_, 3, v___x_2720_);
lean_ctor_set(v___x_2722_, 4, v___x_2721_);
lean_ctor_set(v___x_2722_, 5, v___x_2650_);
lean_ctor_set(v___x_2722_, 6, v___x_2721_);
lean_ctor_set_uint8(v___x_2722_, sizeof(void*)*7, v___x_2512_);
lean_ctor_set_uint8(v___x_2722_, sizeof(void*)*7 + 1, v___x_2512_);
lean_ctor_set_uint8(v___x_2722_, sizeof(void*)*7 + 2, v___x_2512_);
lean_ctor_set_uint8(v___x_2722_, sizeof(void*)*7 + 3, v___x_2647_);
v___x_2723_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2724_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2725_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2726_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2723_);
lean_ctor_set(v___x_2726_, 1, v___x_2724_);
lean_ctor_set(v___x_2726_, 2, v___x_2513_);
lean_ctor_set(v___x_2726_, 3, v___x_2718_);
lean_ctor_set(v___x_2726_, 4, v___x_2725_);
v___x_2727_ = lean_st_mk_ref(v___x_2726_);
v___x_2728_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq(v_val_2709_, v_val_2711_, v___x_2722_, v___x_2727_, v___y_2706_, v___y_2707_);
lean_dec_ref_known(v___x_2722_, 7);
if (lean_obj_tag(v___x_2728_) == 0)
{
lean_object* v_a_2729_; lean_object* v___x_2730_; uint8_t v___x_2731_; 
v_a_2729_ = lean_ctor_get(v___x_2728_, 0);
lean_inc(v_a_2729_);
lean_dec_ref_known(v___x_2728_, 1);
v___x_2730_ = lean_st_ref_get(v___x_2727_);
lean_dec(v___x_2727_);
lean_dec(v___x_2730_);
v___x_2731_ = lean_unbox(v_a_2729_);
lean_dec(v_a_2729_);
if (v___x_2731_ == 0)
{
if (lean_obj_tag(v___y_2699_) == 0)
{
if (lean_obj_tag(v___y_2702_) == 0)
{
v___y_2686_ = v_val_2709_;
v___y_2687_ = v___y_2700_;
v___y_2688_ = v___y_2707_;
v___y_2689_ = v_val_2711_;
v___y_2690_ = v___y_2701_;
v___y_2691_ = v___y_2702_;
v___y_2692_ = v___y_2703_;
v___y_2693_ = v___y_2706_;
goto v___jp_2685_;
}
else
{
lean_object* v_val_2732_; lean_object* v___x_2733_; 
v_val_2732_ = lean_ctor_get(v___y_2702_, 0);
v___x_2733_ = l_Lean_Syntax_getTailPos_x3f(v_val_2732_, v___x_2647_);
if (lean_obj_tag(v___x_2733_) == 0)
{
v___y_2686_ = v_val_2709_;
v___y_2687_ = v___y_2700_;
v___y_2688_ = v___y_2707_;
v___y_2689_ = v_val_2711_;
v___y_2690_ = v___y_2701_;
v___y_2691_ = v___y_2702_;
v___y_2692_ = v___y_2703_;
v___y_2693_ = v___y_2706_;
goto v___jp_2685_;
}
else
{
lean_object* v_val_2734_; 
v_val_2734_ = lean_ctor_get(v___x_2733_, 0);
lean_inc(v_val_2734_);
lean_dec_ref_known(v___x_2733_, 1);
v___y_2653_ = v_val_2709_;
v___y_2654_ = v___y_2700_;
v___y_2655_ = v___y_2707_;
v___y_2656_ = v_val_2711_;
v___y_2657_ = v___y_2701_;
v___y_2658_ = v___y_2702_;
v___y_2659_ = v___y_2703_;
v___y_2660_ = v___y_2706_;
v_val_2661_ = v_val_2734_;
goto v___jp_2652_;
}
}
}
else
{
lean_dec_ref_known(v___y_2699_, 1);
lean_dec(v_val_2711_);
lean_dec(v_val_2709_);
lean_dec_ref(v___f_2511_);
v___y_2589_ = v___y_2700_;
v___y_2590_ = v___y_2701_;
v___y_2591_ = v___y_2702_;
v___y_2592_ = v___y_2703_;
v___y_2593_ = v___y_2706_;
v___y_2594_ = v___y_2707_;
goto v___jp_2588_;
}
}
else
{
lean_dec(v_val_2711_);
lean_dec(v_val_2709_);
lean_dec_ref(v___f_2511_);
if (lean_obj_tag(v___y_2699_) == 0)
{
v___y_2589_ = v___y_2700_;
v___y_2590_ = v___y_2701_;
v___y_2591_ = v___y_2702_;
v___y_2592_ = v___y_2703_;
v___y_2593_ = v___y_2706_;
v___y_2594_ = v___y_2707_;
goto v___jp_2588_;
}
else
{
lean_object* v___x_2735_; lean_object* v___x_2736_; 
lean_dec_ref_known(v___y_2699_, 1);
v___x_2735_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2736_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1(v___x_2735_, v___y_2706_, v___y_2707_);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_dec_ref_known(v___x_2736_, 1);
v___y_2589_ = v___y_2700_;
v___y_2590_ = v___y_2701_;
v___y_2591_ = v___y_2702_;
v___y_2592_ = v___y_2703_;
v___y_2593_ = v___y_2706_;
v___y_2594_ = v___y_2707_;
goto v___jp_2588_;
}
else
{
lean_object* v_a_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2744_; 
lean_dec(v___y_2703_);
lean_dec(v___y_2702_);
lean_dec(v___y_2701_);
lean_dec(v___y_2700_);
lean_dec(v_stx_2517_);
v_a_2737_ = lean_ctor_get(v___x_2736_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2736_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2739_ = v___x_2736_;
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_a_2737_);
lean_dec(v___x_2736_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2742_; 
if (v_isShared_2740_ == 0)
{
v___x_2742_ = v___x_2739_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_a_2737_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
}
}
}
}
}
}
else
{
lean_object* v_a_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2752_; 
lean_dec(v___x_2727_);
lean_dec(v_val_2711_);
lean_dec(v_val_2709_);
lean_dec(v___y_2703_);
lean_dec(v___y_2702_);
lean_dec(v___y_2701_);
lean_dec(v___y_2700_);
lean_dec(v___y_2699_);
lean_dec(v_stx_2517_);
lean_dec_ref(v___f_2511_);
v_a_2745_ = lean_ctor_get(v___x_2728_, 0);
v_isSharedCheck_2752_ = !lean_is_exclusive(v___x_2728_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2747_ = v___x_2728_;
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_a_2745_);
lean_dec(v___x_2728_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
lean_object* v___x_2750_; 
if (v_isShared_2748_ == 0)
{
v___x_2750_ = v___x_2747_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_a_2745_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
return v___x_2750_;
}
}
}
}
else
{
lean_dec(v___x_2710_);
lean_dec(v_val_2709_);
lean_dec(v___y_2699_);
lean_dec(v___x_2513_);
lean_dec_ref(v___f_2511_);
v___y_2589_ = v___y_2700_;
v___y_2590_ = v___y_2701_;
v___y_2591_ = v___y_2702_;
v___y_2592_ = v___y_2703_;
v___y_2593_ = v___y_2706_;
v___y_2594_ = v___y_2707_;
goto v___jp_2588_;
}
}
else
{
lean_dec(v___x_2708_);
lean_dec(v___y_2704_);
lean_dec(v___y_2699_);
lean_dec_ref(v___y_2698_);
lean_dec(v___x_2513_);
lean_dec_ref(v___f_2511_);
v___y_2589_ = v___y_2700_;
v___y_2590_ = v___y_2701_;
v___y_2591_ = v___y_2702_;
v___y_2592_ = v___y_2703_;
v___y_2593_ = v___y_2706_;
v___y_2594_ = v___y_2707_;
goto v___jp_2588_;
}
}
v___jp_2753_:
{
lean_object* v___x_2765_; 
v___x_2765_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1(v_msg_2762_, v___y_2763_, v___y_2764_);
if (lean_obj_tag(v___x_2765_) == 0)
{
lean_dec_ref_known(v___x_2765_, 1);
v___y_2698_ = v___y_2754_;
v___y_2699_ = v___y_2755_;
v___y_2700_ = v___y_2756_;
v___y_2701_ = v___y_2757_;
v___y_2702_ = v___y_2758_;
v___y_2703_ = v___y_2760_;
v___y_2704_ = v___y_2759_;
v___y_2705_ = v___y_2761_;
v___y_2706_ = v___y_2763_;
v___y_2707_ = v___y_2764_;
goto v___jp_2697_;
}
else
{
lean_object* v_a_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2773_; 
lean_dec(v___y_2760_);
lean_dec(v___y_2759_);
lean_dec(v___y_2758_);
lean_dec(v___y_2757_);
lean_dec(v___y_2756_);
lean_dec(v___y_2755_);
lean_dec_ref(v___y_2754_);
lean_dec(v_stx_2517_);
lean_dec(v_declName_2516_);
lean_dec(v___x_2513_);
lean_dec_ref(v___f_2511_);
v_a_2766_ = lean_ctor_get(v___x_2765_, 0);
v_isSharedCheck_2773_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2768_ = v___x_2765_;
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_a_2766_);
lean_dec(v___x_2765_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v___x_2771_; 
if (v_isShared_2769_ == 0)
{
v___x_2771_ = v___x_2768_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_a_2766_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
}
}
v___jp_2774_:
{
if (lean_obj_tag(v___y_2779_) == 1)
{
lean_object* v_val_2782_; lean_object* v___x_2783_; 
v_val_2782_ = lean_ctor_get(v___y_2779_, 0);
lean_inc(v_val_2782_);
v___x_2783_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2(v_val_2782_, v___x_2512_, v___y_2780_, v___y_2781_);
if (lean_obj_tag(v___x_2783_) == 0)
{
lean_object* v___x_2784_; lean_object* v_a_2785_; lean_object* v___x_2786_; uint8_t v___x_2787_; 
lean_dec_ref_known(v___x_2783_, 1);
v___x_2784_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3(v___y_2780_, v___y_2781_);
v_a_2785_ = lean_ctor_get(v___x_2784_, 0);
lean_inc(v_a_2785_);
lean_dec_ref(v___x_2784_);
v___x_2786_ = l_Lean_Linter_linter_deprecated;
v___x_2787_ = l_Lean_Linter_getLinterValue(v___x_2786_, v_a_2785_);
lean_dec(v_a_2785_);
if (v___x_2787_ == 0)
{
lean_dec(v___y_2775_);
lean_dec(v_declName_2516_);
lean_dec_ref(v___x_2514_);
lean_dec(v___x_2513_);
lean_dec_ref(v___f_2511_);
v___y_2589_ = v___y_2776_;
v___y_2590_ = v___y_2777_;
v___y_2591_ = v___y_2778_;
v___y_2592_ = v___y_2779_;
v___y_2593_ = v___y_2780_;
v___y_2594_ = v___y_2781_;
goto v___jp_2588_;
}
else
{
lean_object* v___x_2788_; lean_object* v_env_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; uint8_t v___x_2792_; 
lean_inc(v_val_2782_);
v___x_2788_ = lean_st_ref_get(v___y_2781_);
v_env_2789_ = lean_ctor_get(v___x_2788_, 0);
lean_inc_ref(v_env_2789_);
lean_dec(v___x_2788_);
v___x_2790_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2780_);
v___x_2791_ = l_Lean_Linter_linter_deprecated_deprecatedTarget;
v___x_2792_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__5(v___x_2790_, v___x_2791_);
lean_dec_ref(v___x_2790_);
if (v___x_2792_ == 0)
{
lean_dec_ref(v___x_2514_);
v___y_2698_ = v_env_2789_;
v___y_2699_ = v___y_2775_;
v___y_2700_ = v___y_2776_;
v___y_2701_ = v___y_2777_;
v___y_2702_ = v___y_2778_;
v___y_2703_ = v___y_2779_;
v___y_2704_ = v_val_2782_;
v___y_2705_ = v___x_2787_;
v___y_2706_ = v___y_2780_;
v___y_2707_ = v___y_2781_;
goto v___jp_2697_;
}
else
{
lean_object* v___x_2793_; 
lean_inc(v_val_2782_);
lean_inc_ref(v_env_2789_);
v___x_2793_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v___x_2514_, v_a_2515_, v___x_2512_, v_env_2789_, v_val_2782_);
if (lean_obj_tag(v___x_2793_) == 1)
{
lean_object* v_val_2794_; lean_object* v_name_2795_; lean_object* v_newName_x3f_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; 
v_val_2794_ = lean_ctor_get(v___x_2793_, 0);
lean_inc(v_val_2794_);
lean_dec_ref_known(v___x_2793_, 1);
v_name_2795_ = lean_ctor_get(v___x_2791_, 0);
v_newName_x3f_2796_ = lean_ctor_get(v_val_2794_, 0);
lean_inc(v_newName_x3f_2796_);
lean_dec(v_val_2794_);
v___x_2797_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__37_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__37_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__37_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
lean_inc(v_name_2795_);
v___x_2798_ = l_Lean_MessageData_ofName(v_name_2795_);
v___x_2799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2799_, 0, v___x_2797_);
lean_ctor_set(v___x_2799_, 1, v___x_2798_);
v___x_2800_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__39_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__39_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__39_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2799_);
lean_ctor_set(v___x_2801_, 1, v___x_2800_);
v___x_2802_ = l_Lean_MessageData_note(v___x_2801_);
if (lean_obj_tag(v_newName_x3f_2796_) == 0)
{
lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; 
v___x_2803_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
lean_inc(v_val_2782_);
v___x_2804_ = l_Lean_MessageData_ofConstName(v_val_2782_, v___x_2647_);
v___x_2805_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2803_);
lean_ctor_set(v___x_2805_, 1, v___x_2804_);
v___x_2806_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2807_, 0, v___x_2805_);
lean_ctor_set(v___x_2807_, 1, v___x_2806_);
lean_inc(v_declName_2516_);
v___x_2808_ = l_Lean_MessageData_ofConstName(v_declName_2516_, v___x_2647_);
v___x_2809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2809_, 0, v___x_2807_);
lean_ctor_set(v___x_2809_, 1, v___x_2808_);
v___x_2810_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2811_, 0, v___x_2809_);
lean_ctor_set(v___x_2811_, 1, v___x_2810_);
v___x_2812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2812_, 0, v___x_2811_);
lean_ctor_set(v___x_2812_, 1, v___x_2802_);
v___x_2813_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1(v___x_2812_, v___y_2780_, v___y_2781_);
if (lean_obj_tag(v___x_2813_) == 0)
{
lean_dec_ref_known(v___x_2813_, 1);
v___y_2698_ = v_env_2789_;
v___y_2699_ = v___y_2775_;
v___y_2700_ = v___y_2776_;
v___y_2701_ = v___y_2777_;
v___y_2702_ = v___y_2778_;
v___y_2703_ = v___y_2779_;
v___y_2704_ = v_val_2782_;
v___y_2705_ = v___x_2787_;
v___y_2706_ = v___y_2780_;
v___y_2707_ = v___y_2781_;
goto v___jp_2697_;
}
else
{
lean_object* v_a_2814_; lean_object* v___x_2816_; uint8_t v_isShared_2817_; uint8_t v_isSharedCheck_2821_; 
lean_dec_ref(v_env_2789_);
lean_dec_ref_known(v___y_2779_, 1);
lean_dec(v_val_2782_);
lean_dec(v___y_2778_);
lean_dec(v___y_2777_);
lean_dec(v___y_2776_);
lean_dec(v___y_2775_);
lean_dec(v_stx_2517_);
lean_dec(v_declName_2516_);
lean_dec(v___x_2513_);
lean_dec_ref(v___f_2511_);
v_a_2814_ = lean_ctor_get(v___x_2813_, 0);
v_isSharedCheck_2821_ = !lean_is_exclusive(v___x_2813_);
if (v_isSharedCheck_2821_ == 0)
{
v___x_2816_ = v___x_2813_;
v_isShared_2817_ = v_isSharedCheck_2821_;
goto v_resetjp_2815_;
}
else
{
lean_inc(v_a_2814_);
lean_dec(v___x_2813_);
v___x_2816_ = lean_box(0);
v_isShared_2817_ = v_isSharedCheck_2821_;
goto v_resetjp_2815_;
}
v_resetjp_2815_:
{
lean_object* v___x_2819_; 
if (v_isShared_2817_ == 0)
{
v___x_2819_ = v___x_2816_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v_a_2814_);
v___x_2819_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
return v___x_2819_;
}
}
}
}
else
{
lean_object* v_val_2822_; uint8_t v___x_2823_; 
v_val_2822_ = lean_ctor_get(v_newName_x3f_2796_, 0);
lean_inc(v_val_2822_);
lean_dec_ref_known(v_newName_x3f_2796_, 1);
v___x_2823_ = lean_name_eq(v_val_2822_, v_val_2782_);
if (v___x_2823_ == 0)
{
lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; 
v___x_2824_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
lean_inc(v_val_2782_);
v___x_2825_ = l_Lean_MessageData_ofConstName(v_val_2782_, v___x_2647_);
v___x_2826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2824_);
lean_ctor_set(v___x_2826_, 1, v___x_2825_);
v___x_2827_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__47_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__47_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__47_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2826_);
lean_ctor_set(v___x_2828_, 1, v___x_2827_);
lean_inc(v_val_2822_);
v___x_2829_ = l_Lean_MessageData_ofConstName(v_val_2822_, v___x_2647_);
lean_inc_ref_n(v___x_2829_, 2);
v___x_2830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2830_, 0, v___x_2828_);
lean_ctor_set(v___x_2830_, 1, v___x_2829_);
v___x_2831_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__49_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__49_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__49_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2832_, 0, v___x_2830_);
lean_ctor_set(v___x_2832_, 1, v___x_2831_);
lean_inc(v_declName_2516_);
v___x_2833_ = l_Lean_MessageData_ofConstName(v_declName_2516_, v___x_2647_);
v___x_2834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2834_, 0, v___x_2832_);
lean_ctor_set(v___x_2834_, 1, v___x_2833_);
v___x_2835_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__51_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__51_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__51_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2836_, 0, v___x_2834_);
lean_ctor_set(v___x_2836_, 1, v___x_2835_);
v___x_2837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2837_, 0, v___x_2836_);
lean_ctor_set(v___x_2837_, 1, v___x_2829_);
v___x_2838_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__53_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__53_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__53_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2839_, 0, v___x_2837_);
lean_ctor_set(v___x_2839_, 1, v___x_2838_);
v___x_2840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2840_, 0, v___x_2839_);
lean_ctor_set(v___x_2840_, 1, v___x_2802_);
if (lean_obj_tag(v___y_2776_) == 1)
{
lean_object* v_val_2841_; lean_object* v___x_2842_; 
v_val_2841_ = lean_ctor_get(v___y_2776_, 0);
v___x_2842_ = l_Lean_Syntax_getRange_x3f(v_val_2841_, v___x_2647_);
if (lean_obj_tag(v___x_2842_) == 0)
{
lean_dec_ref(v___x_2829_);
lean_dec(v_val_2822_);
v___y_2754_ = v_env_2789_;
v___y_2755_ = v___y_2775_;
v___y_2756_ = v___y_2776_;
v___y_2757_ = v___y_2777_;
v___y_2758_ = v___y_2778_;
v___y_2759_ = v_val_2782_;
v___y_2760_ = v___y_2779_;
v___y_2761_ = v___x_2787_;
v_msg_2762_ = v___x_2840_;
v___y_2763_ = v___y_2780_;
v___y_2764_ = v___y_2781_;
goto v___jp_2753_;
}
else
{
lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2905_; 
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2842_);
if (v_isSharedCheck_2905_ == 0)
{
lean_object* v_unused_2906_; 
v_unused_2906_ = lean_ctor_get(v___x_2842_, 0);
lean_dec(v_unused_2906_);
v___x_2844_ = v___x_2842_;
v_isShared_2845_ = v_isSharedCheck_2905_;
goto v_resetjp_2843_;
}
else
{
lean_dec(v___x_2842_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2905_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
uint8_t v___x_2846_; uint8_t v___x_2847_; uint8_t v___x_2848_; lean_object* v___x_2849_; uint64_t v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; 
v___x_2846_ = 1;
v___x_2847_ = 0;
v___x_2848_ = 2;
v___x_2849_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_2849_, 0, v___x_2823_);
lean_ctor_set_uint8(v___x_2849_, 1, v___x_2823_);
lean_ctor_set_uint8(v___x_2849_, 2, v___x_2823_);
lean_ctor_set_uint8(v___x_2849_, 3, v___x_2823_);
lean_ctor_set_uint8(v___x_2849_, 4, v___x_2823_);
lean_ctor_set_uint8(v___x_2849_, 5, v___x_2792_);
lean_ctor_set_uint8(v___x_2849_, 6, v___x_2792_);
lean_ctor_set_uint8(v___x_2849_, 7, v___x_2823_);
lean_ctor_set_uint8(v___x_2849_, 8, v___x_2792_);
lean_ctor_set_uint8(v___x_2849_, 9, v___x_2846_);
lean_ctor_set_uint8(v___x_2849_, 10, v___x_2847_);
lean_ctor_set_uint8(v___x_2849_, 11, v___x_2792_);
lean_ctor_set_uint8(v___x_2849_, 12, v___x_2792_);
lean_ctor_set_uint8(v___x_2849_, 13, v___x_2792_);
lean_ctor_set_uint8(v___x_2849_, 14, v___x_2848_);
lean_ctor_set_uint8(v___x_2849_, 15, v___x_2792_);
lean_ctor_set_uint8(v___x_2849_, 16, v___x_2792_);
lean_ctor_set_uint8(v___x_2849_, 17, v___x_2792_);
lean_ctor_set_uint8(v___x_2849_, 18, v___x_2792_);
lean_ctor_set_uint8(v___x_2849_, 19, v___x_2823_);
v___x_2850_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2849_);
v___x_2851_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2851_, 0, v___x_2849_);
lean_ctor_set_uint64(v___x_2851_, sizeof(void*)*1, v___x_2850_);
v___x_2852_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_2853_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__27_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__27_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__27_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2854_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__28_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_2855_ = lean_box(0);
lean_inc_n(v___x_2513_, 2);
v___x_2856_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2856_, 0, v___x_2851_);
lean_ctor_set(v___x_2856_, 1, v___x_2513_);
lean_ctor_set(v___x_2856_, 2, v___x_2853_);
lean_ctor_set(v___x_2856_, 3, v___x_2854_);
lean_ctor_set(v___x_2856_, 4, v___x_2855_);
lean_ctor_set(v___x_2856_, 5, v___x_2650_);
lean_ctor_set(v___x_2856_, 6, v___x_2855_);
lean_ctor_set_uint8(v___x_2856_, sizeof(void*)*7, v___x_2512_);
lean_ctor_set_uint8(v___x_2856_, sizeof(void*)*7 + 1, v___x_2512_);
lean_ctor_set_uint8(v___x_2856_, sizeof(void*)*7 + 2, v___x_2512_);
lean_ctor_set_uint8(v___x_2856_, sizeof(void*)*7 + 3, v___x_2647_);
v___x_2857_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2858_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2859_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2860_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2860_, 0, v___x_2857_);
lean_ctor_set(v___x_2860_, 1, v___x_2858_);
lean_ctor_set(v___x_2860_, 2, v___x_2513_);
lean_ctor_set(v___x_2860_, 3, v___x_2852_);
lean_ctor_set(v___x_2860_, 4, v___x_2859_);
v___x_2861_ = lean_st_mk_ref(v___x_2860_);
v___x_2862_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6(v_val_2822_, v___x_2512_, v___x_2856_, v___x_2861_, v___y_2780_, v___y_2781_);
lean_dec_ref_known(v___x_2856_, 7);
if (lean_obj_tag(v___x_2862_) == 0)
{
lean_object* v_a_2863_; lean_object* v___x_2864_; 
v_a_2863_ = lean_ctor_get(v___x_2862_, 0);
lean_inc(v_a_2863_);
lean_dec_ref_known(v___x_2862_, 1);
v___x_2864_ = lean_st_ref_get(v___x_2861_);
lean_dec(v___x_2861_);
lean_dec(v___x_2864_);
if (lean_obj_tag(v_a_2863_) == 1)
{
lean_object* v_val_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2896_; 
v_val_2865_ = lean_ctor_get(v_a_2863_, 0);
v_isSharedCheck_2896_ = !lean_is_exclusive(v_a_2863_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2867_ = v_a_2863_;
v_isShared_2868_ = v_isSharedCheck_2896_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_val_2865_);
lean_dec(v_a_2863_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2896_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2875_; 
v___x_2869_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__55_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__55_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__55_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2870_, 0, v___x_2869_);
lean_ctor_set(v___x_2870_, 1, v___x_2829_);
v___x_2871_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__57_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__57_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__57_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2870_);
lean_ctor_set(v___x_2872_, 1, v___x_2871_);
v___x_2873_ = l_Lean_Name_toString(v_val_2865_, v___x_2647_);
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 0, v___x_2873_);
v___x_2875_ = v___x_2844_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v___x_2873_);
v___x_2875_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
lean_object* v___x_2876_; uint8_t v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2882_; 
v___x_2876_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2875_);
lean_ctor_set(v___x_2876_, 1, v___x_2855_);
lean_ctor_set(v___x_2876_, 2, v___x_2855_);
lean_ctor_set(v___x_2876_, 3, v___x_2855_);
lean_ctor_set(v___x_2876_, 4, v___x_2855_);
lean_ctor_set(v___x_2876_, 5, v___x_2855_);
v___x_2877_ = 0;
v___x_2878_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2878_, 0, v___x_2876_);
lean_ctor_set(v___x_2878_, 1, v___x_2855_);
lean_ctor_set(v___x_2878_, 2, v___x_2855_);
lean_ctor_set_uint8(v___x_2878_, sizeof(void*)*3, v___x_2877_);
v___x_2879_ = lean_mk_empty_array_with_capacity(v___x_2651_);
v___x_2880_ = lean_array_push(v___x_2879_, v___x_2878_);
lean_inc(v_val_2841_);
if (v_isShared_2868_ == 0)
{
lean_ctor_set(v___x_2867_, 0, v_val_2841_);
v___x_2882_ = v___x_2867_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_val_2841_);
v___x_2882_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
lean_object* v___x_2883_; 
v___x_2883_ = l_Lean_MessageData_hint(v___x_2872_, v___x_2880_, v___x_2882_, v___x_2855_, v___x_2512_, v___y_2780_, v___y_2781_);
lean_dec_ref(v___x_2880_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_object* v_a_2884_; lean_object* v___x_2885_; 
v_a_2884_ = lean_ctor_get(v___x_2883_, 0);
lean_inc(v_a_2884_);
lean_dec_ref_known(v___x_2883_, 1);
v___x_2885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2885_, 0, v___x_2840_);
lean_ctor_set(v___x_2885_, 1, v_a_2884_);
v___y_2754_ = v_env_2789_;
v___y_2755_ = v___y_2775_;
v___y_2756_ = v___y_2776_;
v___y_2757_ = v___y_2777_;
v___y_2758_ = v___y_2778_;
v___y_2759_ = v_val_2782_;
v___y_2760_ = v___y_2779_;
v___y_2761_ = v___x_2787_;
v_msg_2762_ = v___x_2885_;
v___y_2763_ = v___y_2780_;
v___y_2764_ = v___y_2781_;
goto v___jp_2753_;
}
else
{
lean_object* v_a_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2893_; 
lean_dec_ref_known(v___y_2776_, 1);
lean_dec_ref_known(v___x_2840_, 2);
lean_dec_ref(v_env_2789_);
lean_dec(v_val_2782_);
lean_dec_ref_known(v___y_2779_, 1);
lean_dec(v___y_2778_);
lean_dec(v___y_2777_);
lean_dec(v___y_2775_);
lean_dec(v_stx_2517_);
lean_dec(v_declName_2516_);
lean_dec(v___x_2513_);
lean_dec_ref(v___f_2511_);
v_a_2886_ = lean_ctor_get(v___x_2883_, 0);
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2888_ = v___x_2883_;
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_a_2886_);
lean_dec(v___x_2883_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2891_; 
if (v_isShared_2889_ == 0)
{
v___x_2891_ = v___x_2888_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_a_2886_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2863_);
lean_del_object(v___x_2844_);
lean_dec_ref(v___x_2829_);
v___y_2754_ = v_env_2789_;
v___y_2755_ = v___y_2775_;
v___y_2756_ = v___y_2776_;
v___y_2757_ = v___y_2777_;
v___y_2758_ = v___y_2778_;
v___y_2759_ = v_val_2782_;
v___y_2760_ = v___y_2779_;
v___y_2761_ = v___x_2787_;
v_msg_2762_ = v___x_2840_;
v___y_2763_ = v___y_2780_;
v___y_2764_ = v___y_2781_;
goto v___jp_2753_;
}
}
else
{
lean_object* v_a_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2904_; 
lean_dec(v___x_2861_);
lean_del_object(v___x_2844_);
lean_dec_ref_known(v___y_2776_, 1);
lean_dec_ref_known(v___x_2840_, 2);
lean_dec_ref(v___x_2829_);
lean_dec_ref(v_env_2789_);
lean_dec(v_val_2782_);
lean_dec_ref_known(v___y_2779_, 1);
lean_dec(v___y_2778_);
lean_dec(v___y_2777_);
lean_dec(v___y_2775_);
lean_dec(v_stx_2517_);
lean_dec(v_declName_2516_);
lean_dec(v___x_2513_);
lean_dec_ref(v___f_2511_);
v_a_2897_ = lean_ctor_get(v___x_2862_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2899_ = v___x_2862_;
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_a_2897_);
lean_dec(v___x_2862_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v___x_2902_; 
if (v_isShared_2900_ == 0)
{
v___x_2902_ = v___x_2899_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_a_2897_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_2829_);
lean_dec(v_val_2822_);
v___y_2754_ = v_env_2789_;
v___y_2755_ = v___y_2775_;
v___y_2756_ = v___y_2776_;
v___y_2757_ = v___y_2777_;
v___y_2758_ = v___y_2778_;
v___y_2759_ = v_val_2782_;
v___y_2760_ = v___y_2779_;
v___y_2761_ = v___x_2787_;
v_msg_2762_ = v___x_2840_;
v___y_2763_ = v___y_2780_;
v___y_2764_ = v___y_2781_;
goto v___jp_2753_;
}
}
else
{
lean_dec(v_val_2822_);
lean_dec_ref(v___x_2802_);
v___y_2698_ = v_env_2789_;
v___y_2699_ = v___y_2775_;
v___y_2700_ = v___y_2776_;
v___y_2701_ = v___y_2777_;
v___y_2702_ = v___y_2778_;
v___y_2703_ = v___y_2779_;
v___y_2704_ = v_val_2782_;
v___y_2705_ = v___x_2787_;
v___y_2706_ = v___y_2780_;
v___y_2707_ = v___y_2781_;
goto v___jp_2697_;
}
}
}
else
{
lean_dec(v___x_2793_);
v___y_2698_ = v_env_2789_;
v___y_2699_ = v___y_2775_;
v___y_2700_ = v___y_2776_;
v___y_2701_ = v___y_2777_;
v___y_2702_ = v___y_2778_;
v___y_2703_ = v___y_2779_;
v___y_2704_ = v_val_2782_;
v___y_2705_ = v___x_2787_;
v___y_2706_ = v___y_2780_;
v___y_2707_ = v___y_2781_;
goto v___jp_2697_;
}
}
}
}
else
{
lean_object* v_a_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2914_; 
lean_dec_ref_known(v___y_2779_, 1);
lean_dec(v___y_2778_);
lean_dec(v___y_2777_);
lean_dec(v___y_2776_);
lean_dec(v___y_2775_);
lean_dec(v_stx_2517_);
lean_dec(v_declName_2516_);
lean_dec_ref(v___x_2514_);
lean_dec(v___x_2513_);
lean_dec_ref(v___f_2511_);
v_a_2907_ = lean_ctor_get(v___x_2783_, 0);
v_isSharedCheck_2914_ = !lean_is_exclusive(v___x_2783_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2909_ = v___x_2783_;
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_a_2907_);
lean_dec(v___x_2783_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v___x_2912_; 
if (v_isShared_2910_ == 0)
{
v___x_2912_ = v___x_2909_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_a_2907_);
v___x_2912_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
return v___x_2912_;
}
}
}
}
else
{
lean_dec(v___y_2775_);
lean_dec(v_declName_2516_);
lean_dec_ref(v___x_2514_);
lean_dec(v___x_2513_);
lean_dec_ref(v___f_2511_);
v___y_2589_ = v___y_2776_;
v___y_2590_ = v___y_2777_;
v___y_2591_ = v___y_2778_;
v___y_2592_ = v___y_2779_;
v___y_2593_ = v___y_2780_;
v___y_2594_ = v___y_2781_;
goto v___jp_2588_;
}
}
v___jp_2915_:
{
lean_object* v___x_2923_; uint8_t v___x_2924_; 
lean_inc(v_declName_2516_);
v___x_2923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2923_, 0, v_declName_2516_);
v___x_2924_ = l_instBEqOption_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__7(v_a_2922_, v___x_2923_);
lean_dec_ref_known(v___x_2923_, 1);
if (v___x_2924_ == 0)
{
v___y_2775_ = v___y_2916_;
v___y_2776_ = v___y_2917_;
v___y_2777_ = v___y_2918_;
v___y_2778_ = v___y_2919_;
v___y_2779_ = v_a_2922_;
v___y_2780_ = v___y_2920_;
v___y_2781_ = v___y_2921_;
goto v___jp_2774_;
}
else
{
lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v_a_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2938_; 
lean_dec(v_a_2922_);
lean_dec(v___y_2919_);
lean_dec(v___y_2918_);
lean_dec(v___y_2917_);
lean_dec(v___y_2916_);
lean_dec(v_stx_2517_);
lean_dec_ref(v___x_2514_);
lean_dec(v___x_2513_);
lean_dec_ref(v___f_2511_);
v___x_2925_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__59_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__59_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__59_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2926_ = l_Lean_MessageData_ofConstName(v_declName_2516_, v___x_2647_);
v___x_2927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2927_, 0, v___x_2925_);
lean_ctor_set(v___x_2927_, 1, v___x_2926_);
v___x_2928_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__61_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__61_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__61_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2929_, 0, v___x_2927_);
lean_ctor_set(v___x_2929_, 1, v___x_2928_);
v___x_2930_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0___redArg(v___x_2929_, v___y_2920_, v___y_2921_);
v_a_2931_ = lean_ctor_get(v___x_2930_, 0);
v_isSharedCheck_2938_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_2938_ == 0)
{
v___x_2933_ = v___x_2930_;
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_a_2931_);
lean_dec(v___x_2930_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___x_2936_; 
if (v_isShared_2934_ == 0)
{
v___x_2936_ = v___x_2933_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v_a_2931_);
v___x_2936_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
return v___x_2936_;
}
}
}
}
v___jp_2939_:
{
if (lean_obj_tag(v___y_2941_) == 0)
{
lean_object* v___x_2946_; 
v___x_2946_ = lean_box(0);
v___y_2916_ = v___y_2940_;
v___y_2917_ = v___y_2941_;
v___y_2918_ = v_since_x3f_2943_;
v___y_2919_ = v___y_2942_;
v___y_2920_ = v___y_2944_;
v___y_2921_ = v___y_2945_;
v_a_2922_ = v___x_2946_;
goto v___jp_2915_;
}
else
{
lean_object* v_val_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; 
v_val_2947_ = lean_ctor_get(v___y_2941_, 0);
v___x_2948_ = lean_box(0);
lean_inc(v_val_2947_);
v___x_2949_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_val_2947_, v___x_2948_, v___y_2944_, v___y_2945_);
if (lean_obj_tag(v___x_2949_) == 0)
{
lean_object* v_a_2950_; lean_object* v___x_2951_; 
v_a_2950_ = lean_ctor_get(v___x_2949_, 0);
lean_inc(v_a_2950_);
lean_dec_ref_known(v___x_2949_, 1);
v___x_2951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2951_, 0, v_a_2950_);
v___y_2916_ = v___y_2940_;
v___y_2917_ = v___y_2941_;
v___y_2918_ = v_since_x3f_2943_;
v___y_2919_ = v___y_2942_;
v___y_2920_ = v___y_2944_;
v___y_2921_ = v___y_2945_;
v_a_2922_ = v___x_2951_;
goto v___jp_2915_;
}
else
{
lean_object* v_a_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2959_; 
lean_dec_ref_known(v___y_2941_, 1);
lean_dec(v_since_x3f_2943_);
lean_dec(v___y_2942_);
lean_dec(v___y_2940_);
lean_dec(v_stx_2517_);
lean_dec(v_declName_2516_);
lean_dec_ref(v___x_2514_);
lean_dec(v___x_2513_);
lean_dec_ref(v___f_2511_);
v_a_2952_ = lean_ctor_get(v___x_2949_, 0);
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2949_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2954_ = v___x_2949_;
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_a_2952_);
lean_dec(v___x_2949_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2957_; 
if (v_isShared_2955_ == 0)
{
v___x_2957_ = v___x_2954_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_a_2952_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
return v___x_2957_;
}
}
}
}
}
v___jp_2960_:
{
lean_object* v___x_2967_; lean_object* v___x_2968_; uint8_t v___x_2969_; 
v___x_2967_ = lean_unsigned_to_nat(4u);
v___x_2968_ = l_Lean_Syntax_getArg(v_stx_2517_, v___x_2967_);
v___x_2969_ = l_Lean_Syntax_isNone(v___x_2968_);
if (v___x_2969_ == 0)
{
lean_object* v___x_2970_; uint8_t v___x_2971_; 
v___x_2970_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_2968_);
v___x_2971_ = l_Lean_Syntax_matchesNull(v___x_2968_, v___x_2970_);
if (v___x_2971_ == 0)
{
lean_object* v___x_2972_; lean_object* v___x_2973_; 
lean_dec(v___x_2968_);
lean_dec(v_typeChanged_x3f_2964_);
lean_dec(v___y_2962_);
lean_dec(v___y_2961_);
lean_dec(v_stx_2517_);
lean_dec(v_declName_2516_);
lean_dec_ref(v___x_2514_);
lean_dec(v___x_2513_);
lean_dec_ref(v___f_2511_);
v___x_2972_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2973_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0___redArg(v___x_2972_, v___y_2965_, v___y_2966_);
return v___x_2973_;
}
else
{
lean_object* v___x_2974_; lean_object* v___x_2975_; 
v___x_2974_ = l_Lean_Syntax_getArg(v___x_2968_, v___y_2963_);
lean_dec(v___x_2968_);
v___x_2975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2975_, 0, v___x_2974_);
v___y_2940_ = v_typeChanged_x3f_2964_;
v___y_2941_ = v___y_2961_;
v___y_2942_ = v___y_2962_;
v_since_x3f_2943_ = v___x_2975_;
v___y_2944_ = v___y_2965_;
v___y_2945_ = v___y_2966_;
goto v___jp_2939_;
}
}
else
{
lean_object* v___x_2976_; 
lean_dec(v___x_2968_);
v___x_2976_ = lean_box(0);
v___y_2940_ = v_typeChanged_x3f_2964_;
v___y_2941_ = v___y_2961_;
v___y_2942_ = v___y_2962_;
v_since_x3f_2943_ = v___x_2976_;
v___y_2944_ = v___y_2965_;
v___y_2945_ = v___y_2966_;
goto v___jp_2939_;
}
}
v___jp_2977_:
{
lean_object* v___x_2982_; lean_object* v___x_2983_; uint8_t v___x_2984_; 
v___x_2982_ = lean_unsigned_to_nat(3u);
v___x_2983_ = l_Lean_Syntax_getArg(v_stx_2517_, v___x_2982_);
v___x_2984_ = l_Lean_Syntax_isNone(v___x_2983_);
if (v___x_2984_ == 0)
{
uint8_t v___x_2985_; 
lean_inc(v___x_2983_);
v___x_2985_ = l_Lean_Syntax_matchesNull(v___x_2983_, v___x_2651_);
if (v___x_2985_ == 0)
{
lean_object* v___x_2986_; lean_object* v___x_2987_; 
lean_dec(v___x_2983_);
lean_dec(v_text_x3f_2979_);
lean_dec(v___y_2978_);
lean_dec(v_stx_2517_);
lean_dec(v_declName_2516_);
lean_dec_ref(v___x_2514_);
lean_dec(v___x_2513_);
lean_dec_ref(v___f_2511_);
v___x_2986_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2987_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0___redArg(v___x_2986_, v___y_2980_, v___y_2981_);
return v___x_2987_;
}
else
{
lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2988_ = l_Lean_Syntax_getArg(v___x_2983_, v___x_2650_);
lean_dec(v___x_2983_);
v___x_2989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2989_, 0, v___x_2988_);
v___y_2961_ = v___y_2978_;
v___y_2962_ = v_text_x3f_2979_;
v___y_2963_ = v___x_2982_;
v_typeChanged_x3f_2964_ = v___x_2989_;
v___y_2965_ = v___y_2980_;
v___y_2966_ = v___y_2981_;
goto v___jp_2960_;
}
}
else
{
lean_object* v___x_2990_; 
lean_dec(v___x_2983_);
v___x_2990_ = lean_box(0);
v___y_2961_ = v___y_2978_;
v___y_2962_ = v_text_x3f_2979_;
v___y_2963_ = v___x_2982_;
v_typeChanged_x3f_2964_ = v___x_2990_;
v___y_2965_ = v___y_2980_;
v___y_2966_ = v___y_2981_;
goto v___jp_2960_;
}
}
v___jp_2991_:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; uint8_t v___x_2997_; 
v___x_2995_ = lean_unsigned_to_nat(2u);
v___x_2996_ = l_Lean_Syntax_getArg(v_stx_2517_, v___x_2995_);
v___x_2997_ = l_Lean_Syntax_isNone(v___x_2996_);
if (v___x_2997_ == 0)
{
uint8_t v___x_2998_; 
lean_inc(v___x_2996_);
v___x_2998_ = l_Lean_Syntax_matchesNull(v___x_2996_, v___x_2651_);
if (v___x_2998_ == 0)
{
lean_object* v___x_2999_; lean_object* v___x_3000_; 
lean_dec(v___x_2996_);
lean_dec(v_id_x3f_2992_);
lean_dec(v_stx_2517_);
lean_dec(v_declName_2516_);
lean_dec_ref(v___x_2514_);
lean_dec(v___x_2513_);
lean_dec_ref(v___f_2511_);
v___x_2999_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_3000_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0___redArg(v___x_2999_, v___y_2993_, v___y_2994_);
return v___x_3000_;
}
else
{
lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_3001_ = l_Lean_Syntax_getArg(v___x_2996_, v___x_2650_);
lean_dec(v___x_2996_);
v___x_3002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3002_, 0, v___x_3001_);
v___y_2978_ = v_id_x3f_2992_;
v_text_x3f_2979_ = v___x_3002_;
v___y_2980_ = v___y_2993_;
v___y_2981_ = v___y_2994_;
goto v___jp_2977_;
}
}
else
{
lean_object* v___x_3003_; 
lean_dec(v___x_2996_);
v___x_3003_ = lean_box(0);
v___y_2978_ = v_id_x3f_2992_;
v_text_x3f_2979_ = v___x_3003_;
v___y_2980_ = v___y_2993_;
v___y_2981_ = v___y_2994_;
goto v___jp_2977_;
}
}
}
v___jp_2521_:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2525_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2525_, 0, v___y_2523_);
lean_ctor_set(v___x_2525_, 1, v___y_2524_);
lean_ctor_set(v___x_2525_, 2, v___y_2522_);
v___x_2526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2526_, 0, v___x_2525_);
return v___x_2526_;
}
v___jp_2527_:
{
if (lean_obj_tag(v___y_2528_) == 0)
{
lean_object* v___x_2533_; 
v___x_2533_ = l_Lean_Linter_mkSinceHint(v_stx_2517_, v___y_2531_, v___y_2532_);
if (lean_obj_tag(v___x_2533_) == 0)
{
lean_object* v_a_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; 
v_a_2534_ = lean_ctor_get(v___x_2533_, 0);
lean_inc(v_a_2534_);
lean_dec_ref_known(v___x_2533_, 1);
v___x_2535_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__1_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__1_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__1_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2535_);
lean_ctor_set(v___x_2536_, 1, v_a_2534_);
v___x_2537_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1(v___x_2536_, v___y_2531_, v___y_2532_);
if (lean_obj_tag(v___x_2537_) == 0)
{
lean_dec_ref_known(v___x_2537_, 1);
v___y_2522_ = v___y_2528_;
v___y_2523_ = v___y_2529_;
v___y_2524_ = v___y_2530_;
goto v___jp_2521_;
}
else
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2545_; 
lean_dec(v___y_2530_);
lean_dec(v___y_2529_);
v_a_2538_ = lean_ctor_get(v___x_2537_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2540_ = v___x_2537_;
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v___x_2537_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2543_; 
if (v_isShared_2541_ == 0)
{
v___x_2543_ = v___x_2540_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_a_2538_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
}
else
{
lean_object* v_a_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2553_; 
lean_dec(v___y_2530_);
lean_dec(v___y_2529_);
v_a_2546_ = lean_ctor_get(v___x_2533_, 0);
v_isSharedCheck_2553_ = !lean_is_exclusive(v___x_2533_);
if (v_isSharedCheck_2553_ == 0)
{
v___x_2548_ = v___x_2533_;
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_a_2546_);
lean_dec(v___x_2533_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v___x_2551_; 
if (v_isShared_2549_ == 0)
{
v___x_2551_ = v___x_2548_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v_a_2546_);
v___x_2551_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
return v___x_2551_;
}
}
}
}
else
{
lean_dec(v_stx_2517_);
v___y_2522_ = v___y_2528_;
v___y_2523_ = v___y_2529_;
v___y_2524_ = v___y_2530_;
goto v___jp_2521_;
}
}
v___jp_2554_:
{
if (lean_obj_tag(v___y_2556_) == 0)
{
if (lean_obj_tag(v___y_2559_) == 0)
{
lean_object* v___x_2561_; lean_object* v___x_2562_; 
v___x_2561_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__4_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__4_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__4_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2562_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1(v___x_2561_, v___y_2555_, v___y_2557_);
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_dec_ref_known(v___x_2562_, 1);
v___y_2528_ = v___y_2560_;
v___y_2529_ = v___y_2558_;
v___y_2530_ = v___y_2559_;
v___y_2531_ = v___y_2555_;
v___y_2532_ = v___y_2557_;
goto v___jp_2527_;
}
else
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2570_; 
lean_dec(v___y_2560_);
lean_dec(v___y_2558_);
lean_dec(v_stx_2517_);
v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2565_ = v___x_2562_;
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___x_2562_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2568_; 
if (v_isShared_2566_ == 0)
{
v___x_2568_ = v___x_2565_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_a_2563_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
}
else
{
v___y_2528_ = v___y_2560_;
v___y_2529_ = v___y_2558_;
v___y_2530_ = v___y_2559_;
v___y_2531_ = v___y_2555_;
v___y_2532_ = v___y_2557_;
goto v___jp_2527_;
}
}
else
{
lean_dec_ref_known(v___y_2556_, 1);
v___y_2528_ = v___y_2560_;
v___y_2529_ = v___y_2558_;
v___y_2530_ = v___y_2559_;
v___y_2531_ = v___y_2555_;
v___y_2532_ = v___y_2557_;
goto v___jp_2527_;
}
}
v___jp_2571_:
{
if (lean_obj_tag(v___y_2574_) == 0)
{
lean_object* v___x_2578_; 
v___x_2578_ = lean_box(0);
v___y_2555_ = v___y_2572_;
v___y_2556_ = v___y_2573_;
v___y_2557_ = v___y_2575_;
v___y_2558_ = v___y_2576_;
v___y_2559_ = v___y_2577_;
v___y_2560_ = v___x_2578_;
goto v___jp_2554_;
}
else
{
lean_object* v_val_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2587_; 
v_val_2579_ = lean_ctor_get(v___y_2574_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___y_2574_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2581_ = v___y_2574_;
v_isShared_2582_ = v_isSharedCheck_2587_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_val_2579_);
lean_dec(v___y_2574_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2587_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2583_; lean_object* v___x_2585_; 
v___x_2583_ = l_Lean_TSyntax_getString(v_val_2579_);
lean_dec(v_val_2579_);
if (v_isShared_2582_ == 0)
{
lean_ctor_set(v___x_2581_, 0, v___x_2583_);
v___x_2585_ = v___x_2581_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v___x_2583_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
v___y_2555_ = v___y_2572_;
v___y_2556_ = v___y_2573_;
v___y_2557_ = v___y_2575_;
v___y_2558_ = v___y_2576_;
v___y_2559_ = v___y_2577_;
v___y_2560_ = v___x_2585_;
goto v___jp_2554_;
}
}
}
}
v___jp_2588_:
{
if (lean_obj_tag(v___y_2591_) == 0)
{
lean_object* v___x_2595_; 
v___x_2595_ = lean_box(0);
v___y_2572_ = v___y_2593_;
v___y_2573_ = v___y_2589_;
v___y_2574_ = v___y_2590_;
v___y_2575_ = v___y_2594_;
v___y_2576_ = v___y_2592_;
v___y_2577_ = v___x_2595_;
goto v___jp_2571_;
}
else
{
lean_object* v_val_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2604_; 
v_val_2596_ = lean_ctor_get(v___y_2591_, 0);
v_isSharedCheck_2604_ = !lean_is_exclusive(v___y_2591_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2598_ = v___y_2591_;
v_isShared_2599_ = v_isSharedCheck_2604_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_val_2596_);
lean_dec(v___y_2591_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2604_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2600_; lean_object* v___x_2602_; 
v___x_2600_ = l_Lean_TSyntax_getString(v_val_2596_);
lean_dec(v_val_2596_);
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 0, v___x_2600_);
v___x_2602_ = v___x_2598_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v___x_2600_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
v___y_2572_ = v___y_2593_;
v___y_2573_ = v___y_2589_;
v___y_2574_ = v___y_2590_;
v___y_2575_ = v___y_2594_;
v___y_2576_ = v___y_2592_;
v___y_2577_ = v___x_2602_;
goto v___jp_2571_;
}
}
}
}
v___jp_2605_:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; 
v___x_2615_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2616_ = l_Lean_ConstantInfo_type(v___y_2608_);
lean_dec_ref(v___y_2608_);
v___x_2617_ = l_Lean_indentExpr(v___x_2616_);
v___x_2618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2618_, 0, v___x_2615_);
lean_ctor_set(v___x_2618_, 1, v___x_2617_);
v___x_2619_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2620_, 0, v___x_2618_);
lean_ctor_set(v___x_2620_, 1, v___x_2619_);
v___x_2621_ = l_Lean_ConstantInfo_type(v___y_2606_);
lean_dec_ref(v___y_2606_);
v___x_2622_ = l_Lean_indentExpr(v___x_2621_);
v___x_2623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2620_);
lean_ctor_set(v___x_2623_, 1, v___x_2622_);
v___x_2624_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__10_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__10_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__10_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_2625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2625_, 0, v___x_2623_);
lean_ctor_set(v___x_2625_, 1, v___x_2624_);
v___x_2626_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2626_, 0, v___x_2625_);
lean_ctor_set(v___x_2626_, 1, v_hint_2612_);
v___x_2627_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__1(v___x_2626_, v___y_2613_, v___y_2614_);
if (lean_obj_tag(v___x_2627_) == 0)
{
lean_dec_ref_known(v___x_2627_, 1);
v___y_2589_ = v___y_2607_;
v___y_2590_ = v___y_2609_;
v___y_2591_ = v___y_2610_;
v___y_2592_ = v___y_2611_;
v___y_2593_ = v___y_2613_;
v___y_2594_ = v___y_2614_;
goto v___jp_2588_;
}
else
{
lean_object* v_a_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2635_; 
lean_dec(v___y_2611_);
lean_dec(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec(v___y_2607_);
lean_dec(v_stx_2517_);
v_a_2628_ = lean_ctor_get(v___x_2627_, 0);
v_isSharedCheck_2635_ = !lean_is_exclusive(v___x_2627_);
if (v_isSharedCheck_2635_ == 0)
{
v___x_2630_ = v___x_2627_;
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_a_2628_);
lean_dec(v___x_2627_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2633_; 
if (v_isShared_2631_ == 0)
{
v___x_2633_ = v___x_2630_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v_a_2628_);
v___x_2633_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
return v___x_2633_;
}
}
}
}
v___jp_2636_:
{
lean_object* v___x_2645_; 
v___x_2645_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__14_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__14_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__14_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___y_2606_ = v___y_2637_;
v___y_2607_ = v___y_2638_;
v___y_2608_ = v___y_2640_;
v___y_2609_ = v___y_2641_;
v___y_2610_ = v___y_2642_;
v___y_2611_ = v___y_2643_;
v_hint_2612_ = v___x_2645_;
v___y_2613_ = v___y_2644_;
v___y_2614_ = v___y_2639_;
goto v___jp_2605_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2____boxed(lean_object* v___x_3012_, lean_object* v___x_3013_, lean_object* v___f_3014_, lean_object* v___x_3015_, lean_object* v___x_3016_, lean_object* v___x_3017_, lean_object* v_a_3018_, lean_object* v_declName_3019_, lean_object* v_stx_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_){
_start:
{
uint8_t v___x_47816__boxed_3024_; lean_object* v_res_3025_; 
v___x_47816__boxed_3024_ = lean_unbox(v___x_3015_);
v_res_3025_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(v___x_3012_, v___x_3013_, v___f_3014_, v___x_47816__boxed_3024_, v___x_3016_, v___x_3017_, v_a_3018_, v_declName_3019_, v_stx_3020_, v___y_3021_, v___y_3022_);
lean_dec(v___y_3022_);
lean_dec_ref(v___y_3021_);
lean_dec_ref(v_a_3018_);
return v_res_3025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3045_; lean_object* v___f_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; uint8_t v___x_3051_; lean_object* v___f_3052_; lean_object* v___x_3053_; 
v___f_3045_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___f_3046_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_3047_ = lean_box(1);
v___x_3048_ = ((lean_object*)(l_Lean_Linter_instInhabitedDeprecationEntry_default));
v___x_3049_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_));
v___x_3050_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_3051_ = 0;
v___f_3052_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_3053_ = l_Lean_registerParametricAttributeExt___redArg(v___x_3050_, v___x_3051_, v___f_3052_, v___x_3051_);
if (lean_obj_tag(v___x_3053_) == 0)
{
lean_object* v_a_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___f_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; 
v_a_3054_ = lean_ctor_get(v___x_3053_, 0);
lean_inc_n(v_a_3054_, 2);
lean_dec_ref_known(v___x_3053_, 1);
v___x_3055_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_));
v___x_3056_ = lean_box(v___x_3051_);
v___f_3057_ = lean_alloc_closure((void*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2____boxed), 12, 7);
lean_closure_set(v___f_3057_, 0, v___x_3049_);
lean_closure_set(v___f_3057_, 1, v___x_3055_);
lean_closure_set(v___f_3057_, 2, v___f_3045_);
lean_closure_set(v___f_3057_, 3, v___x_3056_);
lean_closure_set(v___f_3057_, 4, v___x_3047_);
lean_closure_set(v___f_3057_, 5, v___x_3048_);
lean_closure_set(v___f_3057_, 6, v_a_3054_);
v___x_3058_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_3059_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3059_, 0, v___x_3058_);
lean_ctor_set(v___x_3059_, 1, v___f_3057_);
lean_ctor_set(v___x_3059_, 2, v___f_3046_);
lean_ctor_set(v___x_3059_, 3, v___f_3052_);
lean_ctor_set_uint8(v___x_3059_, sizeof(void*)*4, v___x_3051_);
v___x_3060_ = l_Lean_registerParametricAttributeForExt___redArg(v___x_3059_, v_a_3054_);
return v___x_3060_;
}
else
{
lean_object* v_a_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3068_; 
v_a_3061_ = lean_ctor_get(v___x_3053_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_3053_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3063_ = v___x_3053_;
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_dec(v___x_3053_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3066_; 
if (v_isShared_3064_ == 0)
{
v___x_3066_ = v___x_3063_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_a_3061_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
return v___x_3066_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2____boxed(lean_object* v_a_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_();
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_3071_, lean_object* v_msg_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_){
_start:
{
lean_object* v___x_3076_; 
v___x_3076_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0___redArg(v_msg_3072_, v___y_3073_, v___y_3074_);
return v___x_3076_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_3077_, lean_object* v_msg_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_){
_start:
{
lean_object* v_res_3082_; 
v_res_3082_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__0(v_00_u03b1_3077_, v_msg_3078_, v___y_3079_, v___y_3080_);
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3079_);
return v_res_3082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3_spec__8(lean_object* v_o_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_){
_start:
{
lean_object* v___x_3087_; 
v___x_3087_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3_spec__8___redArg(v_o_3083_, v___y_3085_);
return v___x_3087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3_spec__8___boxed(lean_object* v_o_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_){
_start:
{
lean_object* v_res_3092_; 
v_res_3092_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__3_spec__8(v_o_3088_, v___y_3089_, v___y_3090_);
lean_dec(v___y_3090_);
lean_dec_ref(v___y_3089_);
return v_res_3092_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4_spec__10(lean_object* v_00_u03b2_3093_){
_start:
{
lean_object* v___x_3094_; 
v___x_3094_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
return v___x_3094_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4___redArg(){
_start:
{
lean_object* v___x_3096_; 
v___x_3096_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
return v___x_3096_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4___redArg___boxed(lean_object* v___dummy_3097_){
_start:
{
lean_object* v_res_3098_; 
v_res_3098_ = l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4___redArg();
return v_res_3098_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__4(lean_object* v_00_u03b2_3099_){
_start:
{
lean_object* v___x_3100_; 
v___x_3100_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
return v___x_3100_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6(lean_object* v_00_u03b2_3101_, lean_object* v_m_3102_, lean_object* v_a_3103_){
_start:
{
lean_object* v___x_3104_; 
v___x_3104_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6___redArg(v_m_3102_, v_a_3103_);
return v___x_3104_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6___boxed(lean_object* v_00_u03b2_3105_, lean_object* v_m_3106_, lean_object* v_a_3107_){
_start:
{
lean_object* v_res_3108_; 
v_res_3108_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6(v_00_u03b2_3105_, v_m_3106_, v_a_3107_);
lean_dec(v_a_3107_);
lean_dec_ref(v_m_3106_);
return v_res_3108_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8(lean_object* v_00_u03b2_3109_, lean_object* v_x_3110_, lean_object* v_x_3111_){
_start:
{
uint8_t v___x_3112_; 
v___x_3112_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg(v_x_3110_, v_x_3111_);
return v___x_3112_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_3113_, lean_object* v_x_3114_, lean_object* v_x_3115_){
_start:
{
uint8_t v_res_3116_; lean_object* v_r_3117_; 
v_res_3116_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8(v_00_u03b2_3113_, v_x_3114_, v_x_3115_);
lean_dec_ref(v_x_3115_);
lean_dec_ref(v_x_3114_);
v_r_3117_ = lean_box(v_res_3116_);
return v_r_3117_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6_spec__12(lean_object* v_00_u03b2_3118_, lean_object* v_a_3119_, lean_object* v_x_3120_){
_start:
{
lean_object* v___x_3121_; 
v___x_3121_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg(v_a_3119_, v_x_3120_);
return v___x_3121_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6_spec__12___boxed(lean_object* v_00_u03b2_3122_, lean_object* v_a_3123_, lean_object* v_x_3124_){
_start:
{
lean_object* v_res_3125_; 
v_res_3125_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__6_spec__12(v_00_u03b2_3122_, v_a_3123_, v_x_3124_);
lean_dec(v_x_3124_);
lean_dec(v_a_3123_);
return v_res_3125_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__19(lean_object* v_00_u03b4_3126_, lean_object* v_t_3127_, lean_object* v_k_3128_){
_start:
{
lean_object* v___x_3129_; 
v___x_3129_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__19___redArg(v_t_3127_, v_k_3128_);
return v___x_3129_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__19___boxed(lean_object* v_00_u03b4_3130_, lean_object* v_t_3131_, lean_object* v_k_3132_){
_start:
{
lean_object* v_res_3133_; 
v_res_3133_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__19(v_00_u03b4_3130_, v_t_3131_, v_k_3132_);
lean_dec(v_k_3132_);
lean_dec(v_t_3131_);
return v_res_3133_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14(lean_object* v_00_u03b2_3134_, lean_object* v_x_3135_, size_t v_x_3136_, lean_object* v_x_3137_){
_start:
{
uint8_t v___x_3138_; 
v___x_3138_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14___redArg(v_x_3135_, v_x_3136_, v_x_3137_);
return v___x_3138_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14___boxed(lean_object* v_00_u03b2_3139_, lean_object* v_x_3140_, lean_object* v_x_3141_, lean_object* v_x_3142_){
_start:
{
size_t v_x_49082__boxed_3143_; uint8_t v_res_3144_; lean_object* v_r_3145_; 
v_x_49082__boxed_3143_ = lean_unbox_usize(v_x_3141_);
lean_dec(v_x_3141_);
v_res_3144_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14(v_00_u03b2_3139_, v_x_3140_, v_x_49082__boxed_3143_, v_x_3142_);
lean_dec_ref(v_x_3142_);
lean_dec_ref(v_x_3140_);
v_r_3145_ = lean_box(v_res_3144_);
return v_r_3145_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22(lean_object* v_givenName_3146_, lean_object* v_auxDeclToFullName_3147_, lean_object* v___x_3148_, lean_object* v_givenNameView_3149_, lean_object* v_as_3150_, lean_object* v_i_3151_, lean_object* v_a_3152_){
_start:
{
lean_object* v___x_3153_; 
v___x_3153_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22___redArg(v_givenName_3146_, v_auxDeclToFullName_3147_, v___x_3148_, v_givenNameView_3149_, v_as_3150_, v_i_3151_);
return v___x_3153_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22___boxed(lean_object* v_givenName_3154_, lean_object* v_auxDeclToFullName_3155_, lean_object* v___x_3156_, lean_object* v_givenNameView_3157_, lean_object* v_as_3158_, lean_object* v_i_3159_, lean_object* v_a_3160_){
_start:
{
lean_object* v_res_3161_; 
v_res_3161_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__22(v_givenName_3154_, v_auxDeclToFullName_3155_, v___x_3156_, v_givenNameView_3157_, v_as_3158_, v_i_3159_, v_a_3160_);
lean_dec_ref(v_as_3158_);
lean_dec(v_auxDeclToFullName_3155_);
lean_dec(v_givenName_3154_);
return v_res_3161_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__25(lean_object* v_localDecl_x3f_3162_, lean_object* v_givenName_3163_, lean_object* v_as_3164_, lean_object* v_i_3165_, lean_object* v_a_3166_){
_start:
{
lean_object* v___x_3167_; 
v___x_3167_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__25___redArg(v_localDecl_x3f_3162_, v_givenName_3163_, v_as_3164_, v_i_3165_);
return v___x_3167_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__25___boxed(lean_object* v_localDecl_x3f_3168_, lean_object* v_givenName_3169_, lean_object* v_as_3170_, lean_object* v_i_3171_, lean_object* v_a_3172_){
_start:
{
lean_object* v_res_3173_; 
v_res_3173_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__25(v_localDecl_x3f_3168_, v_givenName_3169_, v_as_3170_, v_i_3171_, v_a_3172_);
lean_dec_ref(v_as_3170_);
lean_dec(v_givenName_3169_);
lean_dec(v_localDecl_x3f_3168_);
return v_res_3173_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__24_spec__32(lean_object* v_n_u2080_3174_, lean_object* v_filter_3175_, lean_object* v_view_x3f_3176_, lean_object* v_as_3177_, lean_object* v_as_x27_3178_, lean_object* v_b_3179_, lean_object* v_a_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_){
_start:
{
lean_object* v___x_3186_; 
v___x_3186_ = l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__24_spec__32___redArg(v_n_u2080_3174_, v_filter_3175_, v_view_x3f_3176_, v_as_x27_3178_, v_b_3179_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_);
return v___x_3186_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__24_spec__32___boxed(lean_object* v_n_u2080_3187_, lean_object* v_filter_3188_, lean_object* v_view_x3f_3189_, lean_object* v_as_3190_, lean_object* v_as_x27_3191_, lean_object* v_b_3192_, lean_object* v_a_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_){
_start:
{
lean_object* v_res_3199_; 
v_res_3199_ = l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__24_spec__32(v_n_u2080_3187_, v_filter_3188_, v_view_x3f_3189_, v_as_3190_, v_as_x27_3191_, v_b_3192_, v_a_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
lean_dec(v___y_3197_);
lean_dec_ref(v___y_3196_);
lean_dec(v___y_3195_);
lean_dec_ref(v___y_3194_);
lean_dec(v_as_x27_3191_);
lean_dec(v_as_3190_);
lean_dec(v_n_u2080_3187_);
return v_res_3199_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14_spec__19(lean_object* v_00_u03b2_3200_, lean_object* v_keys_3201_, lean_object* v_vals_3202_, lean_object* v_heq_3203_, lean_object* v_i_3204_, lean_object* v_k_3205_){
_start:
{
uint8_t v___x_3206_; 
v___x_3206_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14_spec__19___redArg(v_keys_3201_, v_i_3204_, v_k_3205_);
return v___x_3206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14_spec__19___boxed(lean_object* v_00_u03b2_3207_, lean_object* v_keys_3208_, lean_object* v_vals_3209_, lean_object* v_heq_3210_, lean_object* v_i_3211_, lean_object* v_k_3212_){
_start:
{
uint8_t v_res_3213_; lean_object* v_r_3214_; 
v_res_3213_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__14_spec__19(v_00_u03b2_3207_, v_keys_3208_, v_vals_3209_, v_heq_3210_, v_i_3211_, v_k_3212_);
lean_dec_ref(v_k_3212_);
lean_dec_ref(v_vals_3209_);
lean_dec_ref(v_keys_3208_);
v_r_3214_ = lean_box(v_res_3213_);
return v_r_3214_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23_spec__26(lean_object* v_givenName_3215_, lean_object* v_auxDeclToFullName_3216_, lean_object* v___x_3217_, lean_object* v_givenNameView_3218_, lean_object* v_as_3219_, lean_object* v_i_3220_, lean_object* v_a_3221_){
_start:
{
lean_object* v___x_3222_; 
v___x_3222_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23_spec__26___redArg(v_givenName_3215_, v_auxDeclToFullName_3216_, v___x_3217_, v_givenNameView_3218_, v_as_3219_, v_i_3220_);
return v___x_3222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23_spec__26___boxed(lean_object* v_givenName_3223_, lean_object* v_auxDeclToFullName_3224_, lean_object* v___x_3225_, lean_object* v_givenNameView_3226_, lean_object* v_as_3227_, lean_object* v_i_3228_, lean_object* v_a_3229_){
_start:
{
lean_object* v_res_3230_; 
v_res_3230_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__20_spec__23_spec__26(v_givenName_3223_, v_auxDeclToFullName_3224_, v___x_3225_, v_givenNameView_3226_, v_as_3227_, v_i_3228_, v_a_3229_);
lean_dec_ref(v_as_3227_);
lean_dec(v_auxDeclToFullName_3224_);
lean_dec(v_givenName_3223_);
return v_res_3230_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26_spec__30(lean_object* v_localDecl_x3f_3231_, lean_object* v_givenName_3232_, lean_object* v_as_3233_, lean_object* v_i_3234_, lean_object* v_a_3235_){
_start:
{
lean_object* v___x_3236_; 
v___x_3236_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26_spec__30___redArg(v_localDecl_x3f_3231_, v_givenName_3232_, v_as_3233_, v_i_3234_);
return v___x_3236_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26_spec__30___boxed(lean_object* v_localDecl_x3f_3237_, lean_object* v_givenName_3238_, lean_object* v_as_3239_, lean_object* v_i_3240_, lean_object* v_a_3241_){
_start:
{
lean_object* v_res_3242_; 
v_res_3242_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__21_spec__26_spec__30(v_localDecl_x3f_3237_, v_givenName_3238_, v_as_3239_, v_i_3240_, v_a_3241_);
lean_dec_ref(v_as_3239_);
lean_dec(v_givenName_3238_);
lean_dec(v_localDecl_x3f_3237_);
return v_res_3242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__39(lean_object* v_opt_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_){
_start:
{
lean_object* v___x_3249_; 
v___x_3249_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__39___redArg(v_opt_3243_, v___y_3246_);
return v___x_3249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__39___boxed(lean_object* v_opt_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_){
_start:
{
lean_object* v_res_3256_; 
v_res_3256_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__39(v_opt_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec_ref(v___y_3251_);
lean_dec_ref(v_opt_3250_);
return v_res_3256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__45(lean_object* v_opt_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_){
_start:
{
lean_object* v___x_3263_; 
v___x_3263_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__45___redArg(v_opt_3257_, v___y_3260_);
return v___x_3263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__45___boxed(lean_object* v_opt_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_){
_start:
{
lean_object* v_res_3270_; 
v_res_3270_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__14_spec__27_spec__36_spec__42_spec__45(v_opt_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_);
lean_dec(v___y_3268_);
lean_dec_ref(v___y_3267_);
lean_dec(v___y_3266_);
lean_dec_ref(v___y_3265_);
lean_dec_ref(v_opt_3264_);
return v_res_3270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___redArg___lam__0(lean_object* v_declName_3271_, lean_object* v_entry_3272_, lean_object* v_inst_3273_, lean_object* v_inst_3274_, lean_object* v_inst_3275_, lean_object* v_env_3276_){
_start:
{
lean_object* v___x_3277_; lean_object* v___x_3278_; 
v___x_3277_ = l_Lean_Linter_deprecatedAttr;
v___x_3278_ = l_Lean_ParametricAttribute_setParam___redArg(v___x_3277_, v_env_3276_, v_declName_3271_, v_entry_3272_);
if (lean_obj_tag(v___x_3278_) == 0)
{
lean_object* v_a_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3288_; 
lean_dec_ref(v_inst_3275_);
v_a_3279_ = lean_ctor_get(v___x_3278_, 0);
v_isSharedCheck_3288_ = !lean_is_exclusive(v___x_3278_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3281_ = v___x_3278_;
v_isShared_3282_ = v_isSharedCheck_3288_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_a_3279_);
lean_dec(v___x_3278_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3288_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
lean_object* v___x_3284_; 
if (v_isShared_3282_ == 0)
{
lean_ctor_set_tag(v___x_3281_, 3);
v___x_3284_ = v___x_3281_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v_a_3279_);
v___x_3284_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
lean_object* v___x_3285_; lean_object* v___x_3286_; 
v___x_3285_ = l_Lean_MessageData_ofFormat(v___x_3284_);
v___x_3286_ = l_Lean_throwError___redArg(v_inst_3273_, v_inst_3274_, v___x_3285_);
return v___x_3286_;
}
}
}
else
{
lean_object* v_a_3289_; lean_object* v___x_3290_; 
lean_dec_ref(v_inst_3274_);
lean_dec_ref(v_inst_3273_);
v_a_3289_ = lean_ctor_get(v___x_3278_, 0);
lean_inc(v_a_3289_);
lean_dec_ref_known(v___x_3278_, 1);
v___x_3290_ = l_Lean_setEnv___redArg(v_inst_3275_, v_a_3289_);
return v___x_3290_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___redArg(lean_object* v_inst_3291_, lean_object* v_inst_3292_, lean_object* v_inst_3293_, lean_object* v_declName_3294_, lean_object* v_entry_3295_){
_start:
{
lean_object* v_toBind_3296_; lean_object* v_getEnv_3297_; lean_object* v___f_3298_; lean_object* v___x_3299_; 
v_toBind_3296_ = lean_ctor_get(v_inst_3291_, 1);
lean_inc(v_toBind_3296_);
v_getEnv_3297_ = lean_ctor_get(v_inst_3292_, 0);
lean_inc(v_getEnv_3297_);
v___f_3298_ = lean_alloc_closure((void*)(l_Lean_Linter_setDeprecated___redArg___lam__0), 6, 5);
lean_closure_set(v___f_3298_, 0, v_declName_3294_);
lean_closure_set(v___f_3298_, 1, v_entry_3295_);
lean_closure_set(v___f_3298_, 2, v_inst_3291_);
lean_closure_set(v___f_3298_, 3, v_inst_3293_);
lean_closure_set(v___f_3298_, 4, v_inst_3292_);
v___x_3299_ = lean_apply_4(v_toBind_3296_, lean_box(0), lean_box(0), v_getEnv_3297_, v___f_3298_);
return v___x_3299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated(lean_object* v_m_3300_, lean_object* v_inst_3301_, lean_object* v_inst_3302_, lean_object* v_inst_3303_, lean_object* v_declName_3304_, lean_object* v_entry_3305_){
_start:
{
lean_object* v___x_3306_; 
v___x_3306_ = l_Lean_Linter_setDeprecated___redArg(v_inst_3301_, v_inst_3302_, v_inst_3303_, v_declName_3304_, v_entry_3305_);
return v___x_3306_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_isDeprecated(lean_object* v_env_3307_, lean_object* v_declName_3308_){
_start:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; 
v___x_3309_ = ((lean_object*)(l_Lean_Linter_instInhabitedDeprecationEntry_default));
v___x_3310_ = l_Lean_Linter_deprecatedAttr;
v___x_3311_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_3309_, v___x_3310_, v_env_3307_, v_declName_3308_);
if (lean_obj_tag(v___x_3311_) == 0)
{
uint8_t v___x_3312_; 
v___x_3312_ = 0;
return v___x_3312_;
}
else
{
uint8_t v___x_3313_; 
lean_dec_ref_known(v___x_3311_, 1);
v___x_3313_ = 1;
return v___x_3313_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_isDeprecated___boxed(lean_object* v_env_3314_, lean_object* v_declName_3315_){
_start:
{
uint8_t v_res_3316_; lean_object* v_r_3317_; 
v_res_3316_ = l_Lean_Linter_isDeprecated(v_env_3314_, v_declName_3315_);
v_r_3317_ = lean_box(v_res_3316_);
return v_r_3317_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_isDeprecationWarning___lam__0(lean_object* v_x_3318_){
_start:
{
lean_object* v___x_3319_; uint8_t v___x_3320_; 
v___x_3319_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_3320_ = lean_name_eq(v_x_3318_, v___x_3319_);
return v___x_3320_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_isDeprecationWarning___lam__0___boxed(lean_object* v_x_3321_){
_start:
{
uint8_t v_res_3322_; lean_object* v_r_3323_; 
v_res_3322_ = l_Lean_MessageData_isDeprecationWarning___lam__0(v_x_3321_);
lean_dec(v_x_3321_);
v_r_3323_ = lean_box(v_res_3322_);
return v_r_3323_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_isDeprecationWarning(lean_object* v_msg_3325_){
_start:
{
lean_object* v___f_3326_; uint8_t v___x_3327_; 
v___f_3326_ = ((lean_object*)(l_Lean_MessageData_isDeprecationWarning___closed__0));
v___x_3327_ = l_Lean_MessageData_hasTag(v___f_3326_, v_msg_3325_);
return v___x_3327_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_isDeprecationWarning___boxed(lean_object* v_msg_3328_){
_start:
{
uint8_t v_res_3329_; lean_object* v_r_3330_; 
v_res_3329_ = l_Lean_MessageData_isDeprecationWarning(v_msg_3328_);
v_r_3330_ = lean_box(v_res_3329_);
return v_r_3330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getDeprecatedNewName(lean_object* v_env_3331_, lean_object* v_declName_3332_){
_start:
{
lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
v___x_3333_ = ((lean_object*)(l_Lean_Linter_instInhabitedDeprecationEntry_default));
v___x_3334_ = l_Lean_Linter_deprecatedAttr;
v___x_3335_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_3333_, v___x_3334_, v_env_3331_, v_declName_3332_);
if (lean_obj_tag(v___x_3335_) == 0)
{
lean_object* v___x_3336_; 
v___x_3336_ = lean_box(0);
return v___x_3336_;
}
else
{
lean_object* v_val_3337_; lean_object* v_newName_x3f_3338_; 
v_val_3337_ = lean_ctor_get(v___x_3335_, 0);
lean_inc(v_val_3337_);
lean_dec_ref_known(v___x_3335_, 1);
v_newName_x3f_3338_ = lean_ctor_get(v_val_3337_, 0);
lean_inc(v_newName_x3f_3338_);
lean_dec(v_val_3337_);
return v_newName_x3f_3338_;
}
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0(lean_object* v_x_3339_, lean_object* v_x_3340_){
_start:
{
if (lean_obj_tag(v_x_3339_) == 0)
{
if (lean_obj_tag(v_x_3340_) == 0)
{
uint8_t v___x_3341_; 
v___x_3341_ = 1;
return v___x_3341_;
}
else
{
uint8_t v___x_3342_; 
v___x_3342_ = 0;
return v___x_3342_;
}
}
else
{
if (lean_obj_tag(v_x_3340_) == 0)
{
uint8_t v___x_3343_; 
v___x_3343_ = 0;
return v___x_3343_;
}
else
{
lean_object* v_head_3344_; lean_object* v_tail_3345_; lean_object* v_head_3346_; lean_object* v_tail_3347_; uint8_t v___x_3348_; 
v_head_3344_ = lean_ctor_get(v_x_3339_, 0);
v_tail_3345_ = lean_ctor_get(v_x_3339_, 1);
v_head_3346_ = lean_ctor_get(v_x_3340_, 0);
v_tail_3347_ = lean_ctor_get(v_x_3340_, 1);
v___x_3348_ = lean_string_dec_eq(v_head_3344_, v_head_3346_);
if (v___x_3348_ == 0)
{
return v___x_3348_;
}
else
{
v_x_3339_ = v_tail_3345_;
v_x_3340_ = v_tail_3347_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0___boxed(lean_object* v_x_3350_, lean_object* v_x_3351_){
_start:
{
uint8_t v_res_3352_; lean_object* v_r_3353_; 
v_res_3352_ = l_List_beq___at___00List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0(v_x_3350_, v_x_3351_);
lean_dec(v_x_3351_);
lean_dec(v_x_3350_);
v_r_3353_ = lean_box(v_res_3352_);
return v_r_3353_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0(lean_object* v_x_3354_, lean_object* v_x_3355_){
_start:
{
if (lean_obj_tag(v_x_3354_) == 0)
{
if (lean_obj_tag(v_x_3355_) == 0)
{
uint8_t v___x_3356_; 
v___x_3356_ = 1;
return v___x_3356_;
}
else
{
uint8_t v___x_3357_; 
v___x_3357_ = 0;
return v___x_3357_;
}
}
else
{
if (lean_obj_tag(v_x_3355_) == 0)
{
uint8_t v___x_3358_; 
v___x_3358_ = 0;
return v___x_3358_;
}
else
{
lean_object* v_head_3359_; lean_object* v_head_3360_; lean_object* v_tail_3361_; lean_object* v_tail_3362_; lean_object* v_fst_3363_; lean_object* v_snd_3364_; lean_object* v_fst_3365_; lean_object* v_snd_3366_; uint8_t v___x_3367_; 
v_head_3359_ = lean_ctor_get(v_x_3354_, 0);
v_head_3360_ = lean_ctor_get(v_x_3355_, 0);
v_tail_3361_ = lean_ctor_get(v_x_3354_, 1);
v_tail_3362_ = lean_ctor_get(v_x_3355_, 1);
v_fst_3363_ = lean_ctor_get(v_head_3359_, 0);
v_snd_3364_ = lean_ctor_get(v_head_3359_, 1);
v_fst_3365_ = lean_ctor_get(v_head_3360_, 0);
v_snd_3366_ = lean_ctor_get(v_head_3360_, 1);
v___x_3367_ = lean_name_eq(v_fst_3363_, v_fst_3365_);
if (v___x_3367_ == 0)
{
return v___x_3367_;
}
else
{
uint8_t v___x_3368_; 
v___x_3368_ = l_List_beq___at___00List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0(v_snd_3364_, v_snd_3366_);
if (v___x_3368_ == 0)
{
return v___x_3368_;
}
else
{
v_x_3354_ = v_tail_3361_;
v_x_3355_ = v_tail_3362_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0___boxed(lean_object* v_x_3370_, lean_object* v_x_3371_){
_start:
{
uint8_t v_res_3372_; lean_object* v_r_3373_; 
v_res_3372_ = l_List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0(v_x_3370_, v_x_3371_);
lean_dec(v_x_3371_);
lean_dec(v_x_3370_);
v_r_3373_ = lean_box(v_res_3372_);
return v_r_3373_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__1(void){
_start:
{
lean_object* v___x_3375_; lean_object* v___x_3376_; 
v___x_3375_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__0));
v___x_3376_ = l_Lean_stringToMessageData(v___x_3375_);
return v___x_3376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f(lean_object* v_declName_3377_, lean_object* v_newName_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_){
_start:
{
lean_object* v_ref_3384_; 
v_ref_3384_ = lean_ctor_get(v_a_3381_, 2);
if (lean_obj_tag(v_ref_3384_) == 3)
{
lean_object* v_val_3385_; uint8_t v___x_3386_; 
v_val_3385_ = lean_ctor_get(v_ref_3384_, 2);
v___x_3386_ = l_Lean_Name_hasMacroScopes(v_val_3385_);
if (v___x_3386_ == 0)
{
uint8_t v___x_3387_; lean_object* v___x_3388_; 
v___x_3387_ = 1;
v___x_3388_ = l_Lean_Syntax_getRange_x3f(v_ref_3384_, v___x_3387_);
if (lean_obj_tag(v___x_3388_) == 0)
{
lean_object* v___x_3389_; lean_object* v___x_3390_; 
lean_dec(v_newName_3378_);
lean_dec(v_declName_3377_);
v___x_3389_ = lean_box(0);
v___x_3390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3390_, 0, v___x_3389_);
return v___x_3390_;
}
else
{
lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3472_; 
v_isSharedCheck_3472_ = !lean_is_exclusive(v___x_3388_);
if (v_isSharedCheck_3472_ == 0)
{
lean_object* v_unused_3473_; 
v_unused_3473_ = lean_ctor_get(v___x_3388_, 0);
lean_dec(v_unused_3473_);
v___x_3392_ = v___x_3388_;
v_isShared_3393_ = v_isSharedCheck_3472_;
goto v_resetjp_3391_;
}
else
{
lean_dec(v___x_3388_);
v___x_3392_ = lean_box(0);
v_isShared_3393_ = v_isSharedCheck_3472_;
goto v_resetjp_3391_;
}
v_resetjp_3391_:
{
lean_object* v___x_3394_; 
lean_inc(v_val_3385_);
v___x_3394_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28(v_val_3385_, v___x_3387_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_);
if (lean_obj_tag(v___x_3394_) == 0)
{
lean_object* v_a_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3463_; 
v_a_3395_ = lean_ctor_get(v___x_3394_, 0);
v_isSharedCheck_3463_ = !lean_is_exclusive(v___x_3394_);
if (v_isSharedCheck_3463_ == 0)
{
v___x_3397_ = v___x_3394_;
v_isShared_3398_ = v_isSharedCheck_3463_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_a_3395_);
lean_dec(v___x_3394_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3463_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; uint8_t v___x_3402_; 
v___x_3399_ = lean_box(0);
v___x_3400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3400_, 0, v_declName_3377_);
lean_ctor_set(v___x_3400_, 1, v___x_3399_);
v___x_3401_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3401_, 0, v___x_3400_);
lean_ctor_set(v___x_3401_, 1, v___x_3399_);
v___x_3402_ = l_List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0(v_a_3395_, v___x_3401_);
lean_dec_ref_known(v___x_3401_, 2);
lean_dec(v_a_3395_);
if (v___x_3402_ == 0)
{
lean_object* v___x_3403_; lean_object* v___x_3405_; 
lean_del_object(v___x_3392_);
lean_dec(v_newName_3378_);
v___x_3403_ = lean_box(0);
if (v_isShared_3398_ == 0)
{
lean_ctor_set(v___x_3397_, 0, v___x_3403_);
v___x_3405_ = v___x_3397_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v___x_3403_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
else
{
lean_object* v___x_3407_; 
lean_del_object(v___x_3397_);
v___x_3407_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6(v_newName_3378_, v___x_3386_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_);
if (lean_obj_tag(v___x_3407_) == 0)
{
lean_object* v_a_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3454_; 
v_a_3408_ = lean_ctor_get(v___x_3407_, 0);
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3410_ = v___x_3407_;
v_isShared_3411_ = v_isSharedCheck_3454_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_a_3408_);
lean_dec(v___x_3407_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3454_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
if (lean_obj_tag(v_a_3408_) == 1)
{
lean_object* v_val_3412_; lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3449_; 
lean_del_object(v___x_3410_);
v_val_3412_ = lean_ctor_get(v_a_3408_, 0);
v_isSharedCheck_3449_ = !lean_is_exclusive(v_a_3408_);
if (v_isSharedCheck_3449_ == 0)
{
v___x_3414_ = v_a_3408_;
v_isShared_3415_ = v_isSharedCheck_3449_;
goto v_resetjp_3413_;
}
else
{
lean_inc(v_val_3412_);
lean_dec(v_a_3408_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3449_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; uint8_t v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3427_; 
v___x_3416_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__1, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__1_once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__1);
v___x_3417_ = l_Lean_Name_toString(v_val_3412_, v___x_3387_);
v___x_3418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3418_, 0, v___x_3417_);
v___x_3419_ = lean_box(0);
v___x_3420_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3420_, 0, v___x_3418_);
lean_ctor_set(v___x_3420_, 1, v___x_3419_);
lean_ctor_set(v___x_3420_, 2, v___x_3419_);
lean_ctor_set(v___x_3420_, 3, v___x_3419_);
lean_ctor_set(v___x_3420_, 4, v___x_3419_);
lean_ctor_set(v___x_3420_, 5, v___x_3419_);
v___x_3421_ = 0;
v___x_3422_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3422_, 0, v___x_3420_);
lean_ctor_set(v___x_3422_, 1, v___x_3419_);
lean_ctor_set(v___x_3422_, 2, v___x_3419_);
lean_ctor_set_uint8(v___x_3422_, sizeof(void*)*3, v___x_3421_);
v___x_3423_ = lean_unsigned_to_nat(1u);
v___x_3424_ = lean_mk_empty_array_with_capacity(v___x_3423_);
v___x_3425_ = lean_array_push(v___x_3424_, v___x_3422_);
lean_inc_ref(v_ref_3384_);
if (v_isShared_3415_ == 0)
{
lean_ctor_set(v___x_3414_, 0, v_ref_3384_);
v___x_3427_ = v___x_3414_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v_ref_3384_);
v___x_3427_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
lean_object* v___x_3428_; 
v___x_3428_ = l_Lean_MessageData_hint(v___x_3416_, v___x_3425_, v___x_3427_, v___x_3419_, v___x_3386_, v_a_3381_, v_a_3382_);
lean_dec_ref(v___x_3425_);
if (lean_obj_tag(v___x_3428_) == 0)
{
lean_object* v_a_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3439_; 
v_a_3429_ = lean_ctor_get(v___x_3428_, 0);
v_isSharedCheck_3439_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3439_ == 0)
{
v___x_3431_ = v___x_3428_;
v_isShared_3432_ = v_isSharedCheck_3439_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_a_3429_);
lean_dec(v___x_3428_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3439_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v___x_3434_; 
if (v_isShared_3393_ == 0)
{
lean_ctor_set(v___x_3392_, 0, v_a_3429_);
v___x_3434_ = v___x_3392_;
goto v_reusejp_3433_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v_a_3429_);
v___x_3434_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3433_;
}
v_reusejp_3433_:
{
lean_object* v___x_3436_; 
if (v_isShared_3432_ == 0)
{
lean_ctor_set(v___x_3431_, 0, v___x_3434_);
v___x_3436_ = v___x_3431_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v___x_3434_);
v___x_3436_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
return v___x_3436_;
}
}
}
}
else
{
lean_object* v_a_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3447_; 
lean_del_object(v___x_3392_);
v_a_3440_ = lean_ctor_get(v___x_3428_, 0);
v_isSharedCheck_3447_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3447_ == 0)
{
v___x_3442_ = v___x_3428_;
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_a_3440_);
lean_dec(v___x_3428_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v___x_3445_; 
if (v_isShared_3443_ == 0)
{
v___x_3445_ = v___x_3442_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v_a_3440_);
v___x_3445_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
return v___x_3445_;
}
}
}
}
}
}
else
{
lean_object* v___x_3450_; lean_object* v___x_3452_; 
lean_dec(v_a_3408_);
lean_del_object(v___x_3392_);
v___x_3450_ = lean_box(0);
if (v_isShared_3411_ == 0)
{
lean_ctor_set(v___x_3410_, 0, v___x_3450_);
v___x_3452_ = v___x_3410_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v___x_3450_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
return v___x_3452_;
}
}
}
}
else
{
lean_object* v_a_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3462_; 
lean_del_object(v___x_3392_);
v_a_3455_ = lean_ctor_get(v___x_3407_, 0);
v_isSharedCheck_3462_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3462_ == 0)
{
v___x_3457_ = v___x_3407_;
v_isShared_3458_ = v_isSharedCheck_3462_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_a_3455_);
lean_dec(v___x_3407_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3462_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
lean_object* v___x_3460_; 
if (v_isShared_3458_ == 0)
{
v___x_3460_ = v___x_3457_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_a_3455_);
v___x_3460_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
return v___x_3460_;
}
}
}
}
}
}
else
{
lean_object* v_a_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3471_; 
lean_del_object(v___x_3392_);
lean_dec(v_newName_3378_);
lean_dec(v_declName_3377_);
v_a_3464_ = lean_ctor_get(v___x_3394_, 0);
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3394_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3466_ = v___x_3394_;
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_a_3464_);
lean_dec(v___x_3394_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___x_3469_; 
if (v_isShared_3467_ == 0)
{
v___x_3469_ = v___x_3466_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v_a_3464_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
return v___x_3469_;
}
}
}
}
}
}
else
{
lean_object* v___x_3474_; lean_object* v___x_3475_; 
lean_dec(v_newName_3378_);
lean_dec(v_declName_3377_);
v___x_3474_ = lean_box(0);
v___x_3475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3475_, 0, v___x_3474_);
return v___x_3475_;
}
}
else
{
lean_object* v___x_3476_; lean_object* v___x_3477_; 
lean_dec(v_newName_3378_);
lean_dec(v_declName_3377_);
v___x_3476_ = lean_box(0);
v___x_3477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3477_, 0, v___x_3476_);
return v___x_3477_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___boxed(lean_object* v_declName_3478_, lean_object* v_newName_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_){
_start:
{
lean_object* v_res_3485_; 
v_res_3485_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f(v_declName_3478_, v_newName_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
lean_dec(v_a_3483_);
lean_dec_ref(v_a_3482_);
lean_dec(v_a_3481_);
lean_dec_ref(v_a_3480_);
return v_res_3485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(lean_object* v_o_3486_, lean_object* v___y_3487_){
_start:
{
lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v_env_3491_; lean_object* v___x_3492_; lean_object* v_toEnvExtension_3493_; lean_object* v_asyncMode_3494_; lean_object* v___x_3495_; uint8_t v___x_3496_; lean_object* v___x_3497_; lean_object* v_merged_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3506_; 
v___x_3489_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_3490_ = lean_st_ref_get(v___y_3487_);
v_env_3491_ = lean_ctor_get(v___x_3490_, 0);
lean_inc_ref(v_env_3491_);
lean_dec(v___x_3490_);
v___x_3492_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_3493_ = lean_ctor_get(v___x_3492_, 0);
v_asyncMode_3494_ = lean_ctor_get(v_toEnvExtension_3493_, 2);
v___x_3495_ = lean_box(0);
v___x_3496_ = 0;
v___x_3497_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3489_, v___x_3492_, v_env_3491_, v_asyncMode_3494_, v___x_3495_, v___x_3496_);
v_merged_3498_ = lean_ctor_get(v___x_3497_, 0);
v_isSharedCheck_3506_ = !lean_is_exclusive(v___x_3497_);
if (v_isSharedCheck_3506_ == 0)
{
lean_object* v_unused_3507_; 
v_unused_3507_ = lean_ctor_get(v___x_3497_, 1);
lean_dec(v_unused_3507_);
v___x_3500_ = v___x_3497_;
v_isShared_3501_ = v_isSharedCheck_3506_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_merged_3498_);
lean_dec(v___x_3497_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3506_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v___x_3503_; 
if (v_isShared_3501_ == 0)
{
lean_ctor_set(v___x_3500_, 1, v_merged_3498_);
lean_ctor_set(v___x_3500_, 0, v_o_3486_);
v___x_3503_ = v___x_3500_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v_o_3486_);
lean_ctor_set(v_reuseFailAlloc_3505_, 1, v_merged_3498_);
v___x_3503_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
lean_object* v___x_3504_; 
v___x_3504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3504_, 0, v___x_3503_);
return v___x_3504_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg___boxed(lean_object* v_o_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_){
_start:
{
lean_object* v_res_3511_; 
v_res_3511_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(v_o_3508_, v___y_3509_);
lean_dec(v___y_3509_);
return v_res_3511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0(lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_){
_start:
{
lean_object* v___x_3517_; lean_object* v___x_3518_; 
v___x_3517_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3514_);
v___x_3518_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(v___x_3517_, v___y_3515_);
return v___x_3518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0___boxed(lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_){
_start:
{
lean_object* v_res_3524_; 
v_res_3524_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0(v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_);
lean_dec(v___y_3522_);
lean_dec_ref(v___y_3521_);
lean_dec(v___y_3520_);
lean_dec_ref(v___y_3519_);
return v_res_3524_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__1(void){
_start:
{
lean_object* v___x_3526_; lean_object* v___x_3527_; 
v___x_3526_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__0));
v___x_3527_ = l_Lean_stringToMessageData(v___x_3526_);
return v___x_3527_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__3(void){
_start:
{
lean_object* v___x_3529_; lean_object* v___x_3530_; 
v___x_3529_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__2));
v___x_3530_ = l_Lean_stringToMessageData(v___x_3529_);
return v___x_3530_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__5(void){
_start:
{
lean_object* v___x_3532_; lean_object* v___x_3533_; 
v___x_3532_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__4));
v___x_3533_ = l_Lean_stringToMessageData(v___x_3532_);
return v___x_3533_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__7(void){
_start:
{
lean_object* v___x_3535_; lean_object* v___x_3536_; 
v___x_3535_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__6));
v___x_3536_ = l_Lean_stringToMessageData(v___x_3535_);
return v___x_3536_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__9(void){
_start:
{
lean_object* v___x_3538_; lean_object* v___x_3539_; 
v___x_3538_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__8));
v___x_3539_ = l_Lean_stringToMessageData(v___x_3538_);
return v___x_3539_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__11(void){
_start:
{
lean_object* v___x_3541_; lean_object* v___x_3542_; 
v___x_3541_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__10));
v___x_3542_ = l_Lean_stringToMessageData(v___x_3541_);
return v___x_3542_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__13(void){
_start:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; 
v___x_3544_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__12));
v___x_3545_ = l_Lean_stringToMessageData(v___x_3544_);
return v___x_3545_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__15(void){
_start:
{
lean_object* v___x_3547_; lean_object* v___x_3548_; 
v___x_3547_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__14));
v___x_3548_ = l_Lean_stringToMessageData(v___x_3547_);
return v___x_3548_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__17(void){
_start:
{
lean_object* v___x_3550_; lean_object* v___x_3551_; 
v___x_3550_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__16));
v___x_3551_ = l_Lean_stringToMessageData(v___x_3550_);
return v___x_3551_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__19(void){
_start:
{
lean_object* v___x_3553_; lean_object* v___x_3554_; 
v___x_3553_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__18));
v___x_3554_ = l_Lean_stringToMessageData(v___x_3553_);
return v___x_3554_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__21(void){
_start:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; 
v___x_3557_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__20));
v___x_3558_ = l_Lean_MessageData_ofFormat(v___x_3557_);
return v___x_3558_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__23(void){
_start:
{
lean_object* v___x_3560_; lean_object* v___x_3561_; 
v___x_3560_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__22));
v___x_3561_ = l_Lean_stringToMessageData(v___x_3560_);
return v___x_3561_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__25(void){
_start:
{
lean_object* v___x_3563_; lean_object* v___x_3564_; 
v___x_3563_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__24));
v___x_3564_ = l_Lean_stringToMessageData(v___x_3563_);
return v___x_3564_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__27(void){
_start:
{
lean_object* v___x_3566_; lean_object* v___x_3567_; 
v___x_3566_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__26));
v___x_3567_ = l_Lean_stringToMessageData(v___x_3566_);
return v___x_3567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkDeprecated(lean_object* v_declName_3568_, uint8_t v_allowSuggestion_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_){
_start:
{
lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v_a_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3740_; 
v___x_3575_ = ((lean_object*)(l_Lean_Linter_instInhabitedDeprecationEntry_default));
v___x_3576_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0(v_a_3570_, v_a_3571_, v_a_3572_, v_a_3573_);
v_a_3577_ = lean_ctor_get(v___x_3576_, 0);
v_isSharedCheck_3740_ = !lean_is_exclusive(v___x_3576_);
if (v_isSharedCheck_3740_ == 0)
{
v___x_3579_ = v___x_3576_;
v_isShared_3580_ = v_isSharedCheck_3740_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_a_3577_);
lean_dec(v___x_3576_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3740_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v___x_3581_; uint8_t v___x_3582_; lean_object* v_extraMsg_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; 
v___x_3581_ = l_Lean_Linter_linter_deprecated;
v___x_3582_ = l_Lean_Linter_getLinterValue(v___x_3581_, v_a_3577_);
lean_dec(v_a_3577_);
if (v___x_3582_ == 0)
{
lean_object* v___x_3598_; lean_object* v___x_3600_; 
lean_dec(v_declName_3568_);
v___x_3598_ = lean_box(0);
if (v_isShared_3580_ == 0)
{
lean_ctor_set(v___x_3579_, 0, v___x_3598_);
v___x_3600_ = v___x_3579_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v___x_3598_);
v___x_3600_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
return v___x_3600_;
}
}
else
{
lean_object* v___x_3602_; lean_object* v_env_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; 
v___x_3602_ = lean_st_ref_get(v_a_3573_);
v_env_3603_ = lean_ctor_get(v___x_3602_, 0);
lean_inc_ref(v_env_3603_);
lean_dec(v___x_3602_);
v___x_3604_ = l_Lean_Linter_deprecatedAttr;
lean_inc(v_declName_3568_);
v___x_3605_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_3575_, v___x_3604_, v_env_3603_, v_declName_3568_);
if (lean_obj_tag(v___x_3605_) == 1)
{
lean_object* v_val_3606_; lean_object* v_text_x3f_3607_; 
lean_del_object(v___x_3579_);
v_val_3606_ = lean_ctor_get(v___x_3605_, 0);
lean_inc(v_val_3606_);
lean_dec_ref_known(v___x_3605_, 1);
v_text_x3f_3607_ = lean_ctor_get(v_val_3606_, 1);
if (lean_obj_tag(v_text_x3f_3607_) == 0)
{
lean_object* v_newName_x3f_3608_; 
v_newName_x3f_3608_ = lean_ctor_get(v_val_3606_, 0);
lean_inc(v_newName_x3f_3608_);
lean_dec(v_val_3606_);
if (lean_obj_tag(v_newName_x3f_3608_) == 0)
{
lean_object* v___x_3609_; 
v___x_3609_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__2_spec__4___closed__9);
v_extraMsg_3584_ = v___x_3609_;
v___y_3585_ = v_a_3570_;
v___y_3586_ = v_a_3571_;
v___y_3587_ = v_a_3572_;
v___y_3588_ = v_a_3573_;
goto v___jp_3583_;
}
else
{
lean_object* v_val_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v_env_3617_; lean_object* v___x_3618_; uint8_t v___x_3619_; lean_object* v___x_3620_; 
v_val_3610_ = lean_ctor_get(v_newName_x3f_3608_, 0);
lean_inc_n(v_val_3610_, 2);
lean_dec_ref_known(v_newName_x3f_3608_, 1);
v___x_3611_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__3, &l_Lean_Linter_checkDeprecated___closed__3_once, _init_l_Lean_Linter_checkDeprecated___closed__3);
v___x_3612_ = l_Lean_MessageData_ofConstName(v_val_3610_, v___x_3582_);
lean_inc_ref(v___x_3612_);
v___x_3613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3613_, 0, v___x_3611_);
lean_ctor_set(v___x_3613_, 1, v___x_3612_);
v___x_3614_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__53_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__53_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__53_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_3615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3615_, 0, v___x_3613_);
lean_ctor_set(v___x_3615_, 1, v___x_3614_);
v___x_3616_ = lean_st_ref_get(v_a_3573_);
v_env_3617_ = lean_ctor_get(v___x_3616_, 0);
lean_inc_ref_n(v_env_3617_, 2);
lean_dec(v___x_3616_);
v___x_3618_ = l_Lean_Name_getPrefix(v_declName_3568_);
v___x_3619_ = 0;
lean_inc(v_declName_3568_);
v___x_3620_ = l_Lean_Environment_find_x3f(v_env_3617_, v_declName_3568_, v___x_3619_);
if (lean_obj_tag(v___x_3620_) == 1)
{
lean_object* v_val_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; 
v_val_3621_ = lean_ctor_get(v___x_3620_, 0);
lean_inc(v_val_3621_);
lean_dec_ref_known(v___x_3620_, 1);
v___x_3622_ = l_Lean_Name_getPrefix(v_val_3610_);
lean_inc(v_val_3610_);
lean_inc_ref(v_env_3617_);
v___x_3623_ = l_Lean_Environment_find_x3f(v_env_3617_, v_val_3610_, v___x_3619_);
if (lean_obj_tag(v___x_3623_) == 1)
{
lean_object* v_val_3624_; lean_object* v___x_3625_; 
v_val_3624_ = lean_ctor_get(v___x_3623_, 0);
lean_inc(v_val_3624_);
lean_dec_ref_known(v___x_3623_, 1);
v___x_3625_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq(v_val_3621_, v_val_3624_, v_a_3570_, v_a_3571_, v_a_3572_, v_a_3573_);
if (lean_obj_tag(v___x_3625_) == 0)
{
lean_object* v_a_3626_; lean_object* v_msg_3628_; lean_object* v___y_3629_; lean_object* v___y_3630_; lean_object* v___y_3631_; lean_object* v___y_3632_; lean_object* v___y_3647_; lean_object* v___y_3648_; lean_object* v___y_3649_; lean_object* v___y_3650_; lean_object* v___y_3651_; lean_object* v___y_3652_; lean_object* v___y_3667_; lean_object* v___y_3668_; lean_object* v___y_3669_; lean_object* v___y_3670_; lean_object* v___y_3671_; lean_object* v___y_3672_; lean_object* v_msg_3680_; lean_object* v___y_3681_; lean_object* v___y_3682_; lean_object* v___y_3683_; lean_object* v___y_3684_; uint8_t v___x_3712_; 
v_a_3626_ = lean_ctor_get(v___x_3625_, 0);
lean_inc(v_a_3626_);
lean_dec_ref_known(v___x_3625_, 1);
v___x_3712_ = lean_unbox(v_a_3626_);
if (v___x_3712_ == 0)
{
lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; 
v___x_3713_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_3714_ = l_Lean_ConstantInfo_type(v_val_3624_);
lean_dec(v_val_3624_);
v___x_3715_ = l_Lean_indentExpr(v___x_3714_);
v___x_3716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3716_, 0, v___x_3713_);
lean_ctor_set(v___x_3716_, 1, v___x_3715_);
v___x_3717_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_3718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3718_, 0, v___x_3716_);
lean_ctor_set(v___x_3718_, 1, v___x_3717_);
v___x_3719_ = l_Lean_ConstantInfo_type(v_val_3621_);
lean_dec(v_val_3621_);
v___x_3720_ = l_Lean_indentExpr(v___x_3719_);
v___x_3721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3721_, 0, v___x_3718_);
lean_ctor_set(v___x_3721_, 1, v___x_3720_);
v___x_3722_ = l_Lean_MessageData_note(v___x_3721_);
v___x_3723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3723_, 0, v___x_3615_);
lean_ctor_set(v___x_3723_, 1, v___x_3722_);
v_msg_3680_ = v___x_3723_;
v___y_3681_ = v_a_3570_;
v___y_3682_ = v_a_3571_;
v___y_3683_ = v_a_3572_;
v___y_3684_ = v_a_3573_;
goto v___jp_3679_;
}
else
{
lean_dec(v_val_3624_);
lean_dec(v_val_3621_);
v_msg_3680_ = v___x_3615_;
v___y_3681_ = v_a_3570_;
v___y_3682_ = v_a_3571_;
v___y_3683_ = v_a_3572_;
v___y_3684_ = v_a_3573_;
goto v___jp_3679_;
}
v___jp_3627_:
{
if (v_allowSuggestion_3569_ == 0)
{
lean_dec(v_a_3626_);
lean_dec(v_val_3610_);
v_extraMsg_3584_ = v_msg_3628_;
v___y_3585_ = v___y_3629_;
v___y_3586_ = v___y_3630_;
v___y_3587_ = v___y_3631_;
v___y_3588_ = v___y_3632_;
goto v___jp_3583_;
}
else
{
uint8_t v___x_3633_; 
v___x_3633_ = lean_unbox(v_a_3626_);
lean_dec(v_a_3626_);
if (v___x_3633_ == 0)
{
lean_dec(v_val_3610_);
v_extraMsg_3584_ = v_msg_3628_;
v___y_3585_ = v___y_3629_;
v___y_3586_ = v___y_3630_;
v___y_3587_ = v___y_3631_;
v___y_3588_ = v___y_3632_;
goto v___jp_3583_;
}
else
{
lean_object* v___x_3634_; 
lean_inc(v_declName_3568_);
v___x_3634_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f(v_declName_3568_, v_val_3610_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_);
if (lean_obj_tag(v___x_3634_) == 0)
{
lean_object* v_a_3635_; 
v_a_3635_ = lean_ctor_get(v___x_3634_, 0);
lean_inc(v_a_3635_);
lean_dec_ref_known(v___x_3634_, 1);
if (lean_obj_tag(v_a_3635_) == 1)
{
lean_object* v_val_3636_; lean_object* v___x_3637_; 
v_val_3636_ = lean_ctor_get(v_a_3635_, 0);
lean_inc(v_val_3636_);
lean_dec_ref_known(v_a_3635_, 1);
v___x_3637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3637_, 0, v_msg_3628_);
lean_ctor_set(v___x_3637_, 1, v_val_3636_);
v_extraMsg_3584_ = v___x_3637_;
v___y_3585_ = v___y_3629_;
v___y_3586_ = v___y_3630_;
v___y_3587_ = v___y_3631_;
v___y_3588_ = v___y_3632_;
goto v___jp_3583_;
}
else
{
lean_dec(v_a_3635_);
v_extraMsg_3584_ = v_msg_3628_;
v___y_3585_ = v___y_3629_;
v___y_3586_ = v___y_3630_;
v___y_3587_ = v___y_3631_;
v___y_3588_ = v___y_3632_;
goto v___jp_3583_;
}
}
else
{
lean_object* v_a_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3645_; 
lean_dec_ref(v_msg_3628_);
lean_dec(v_declName_3568_);
v_a_3638_ = lean_ctor_get(v___x_3634_, 0);
v_isSharedCheck_3645_ = !lean_is_exclusive(v___x_3634_);
if (v_isSharedCheck_3645_ == 0)
{
v___x_3640_ = v___x_3634_;
v_isShared_3641_ = v_isSharedCheck_3645_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_a_3638_);
lean_dec(v___x_3634_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3645_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
lean_object* v___x_3643_; 
if (v_isShared_3641_ == 0)
{
v___x_3643_ = v___x_3640_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v_a_3638_);
v___x_3643_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
return v___x_3643_;
}
}
}
}
}
}
v___jp_3646_:
{
lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; 
v___x_3653_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_3654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3654_, 0, v___x_3653_);
lean_ctor_set(v___x_3654_, 1, v___x_3612_);
v___x_3655_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__5, &l_Lean_Linter_checkDeprecated___closed__5_once, _init_l_Lean_Linter_checkDeprecated___closed__5);
v___x_3656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3656_, 0, v___x_3654_);
lean_ctor_set(v___x_3656_, 1, v___x_3655_);
v___x_3657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3657_, 0, v___x_3656_);
lean_ctor_set(v___x_3657_, 1, v___y_3652_);
v___x_3658_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__7, &l_Lean_Linter_checkDeprecated___closed__7_once, _init_l_Lean_Linter_checkDeprecated___closed__7);
v___x_3659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3659_, 0, v___x_3657_);
lean_ctor_set(v___x_3659_, 1, v___x_3658_);
v___x_3660_ = l_Lean_MessageData_ofName(v___x_3622_);
v___x_3661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3661_, 0, v___x_3659_);
lean_ctor_set(v___x_3661_, 1, v___x_3660_);
v___x_3662_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__9, &l_Lean_Linter_checkDeprecated___closed__9_once, _init_l_Lean_Linter_checkDeprecated___closed__9);
v___x_3663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3663_, 0, v___x_3661_);
lean_ctor_set(v___x_3663_, 1, v___x_3662_);
v___x_3664_ = l_Lean_MessageData_note(v___x_3663_);
v___x_3665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3665_, 0, v___y_3650_);
lean_ctor_set(v___x_3665_, 1, v___x_3664_);
v_msg_3628_ = v___x_3665_;
v___y_3629_ = v___y_3649_;
v___y_3630_ = v___y_3648_;
v___y_3631_ = v___y_3651_;
v___y_3632_ = v___y_3647_;
goto v___jp_3627_;
}
v___jp_3666_:
{
lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; 
v___x_3673_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__11, &l_Lean_Linter_checkDeprecated___closed__11_once, _init_l_Lean_Linter_checkDeprecated___closed__11);
v___x_3674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3674_, 0, v___x_3673_);
lean_ctor_set(v___x_3674_, 1, v___y_3672_);
v___x_3675_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__13, &l_Lean_Linter_checkDeprecated___closed__13_once, _init_l_Lean_Linter_checkDeprecated___closed__13);
v___x_3676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3676_, 0, v___x_3674_);
lean_ctor_set(v___x_3676_, 1, v___x_3675_);
v___x_3677_ = l_Lean_MessageData_note(v___x_3676_);
v___x_3678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3678_, 0, v___y_3670_);
lean_ctor_set(v___x_3678_, 1, v___x_3677_);
v_msg_3628_ = v___x_3678_;
v___y_3629_ = v___y_3669_;
v___y_3630_ = v___y_3668_;
v___y_3631_ = v___y_3671_;
v___y_3632_ = v___y_3667_;
goto v___jp_3627_;
}
v___jp_3679_:
{
uint8_t v___x_3685_; 
v___x_3685_ = l_Lean_Name_isAnonymous(v___x_3618_);
if (v___x_3685_ == 0)
{
uint8_t v___x_3686_; 
v___x_3686_ = lean_name_eq(v___x_3618_, v___x_3622_);
lean_dec(v___x_3618_);
if (v___x_3686_ == 0)
{
lean_dec(v___x_3622_);
lean_dec_ref(v_env_3617_);
lean_dec_ref(v___x_3612_);
if (lean_obj_tag(v_declName_3568_) == 1)
{
lean_object* v_str_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; 
v_str_3687_ = lean_ctor_get(v_declName_3568_, 1);
v___x_3688_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__15, &l_Lean_Linter_checkDeprecated___closed__15_once, _init_l_Lean_Linter_checkDeprecated___closed__15);
lean_inc_ref(v_str_3687_);
v___x_3689_ = l_Lean_stringToMessageData(v_str_3687_);
v___x_3690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3690_, 0, v___x_3688_);
lean_ctor_set(v___x_3690_, 1, v___x_3689_);
v___x_3691_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__17, &l_Lean_Linter_checkDeprecated___closed__17_once, _init_l_Lean_Linter_checkDeprecated___closed__17);
v___x_3692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3690_);
lean_ctor_set(v___x_3692_, 1, v___x_3691_);
lean_inc(v_val_3610_);
v___x_3693_ = l_Lean_MessageData_ofConstName(v_val_3610_, v___x_3685_);
v___x_3694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3694_, 0, v___x_3692_);
lean_ctor_set(v___x_3694_, 1, v___x_3693_);
v___x_3695_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__19, &l_Lean_Linter_checkDeprecated___closed__19_once, _init_l_Lean_Linter_checkDeprecated___closed__19);
v___x_3696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3696_, 0, v___x_3694_);
lean_ctor_set(v___x_3696_, 1, v___x_3695_);
v___y_3667_ = v___y_3684_;
v___y_3668_ = v___y_3682_;
v___y_3669_ = v___y_3681_;
v___y_3670_ = v_msg_3680_;
v___y_3671_ = v___y_3683_;
v___y_3672_ = v___x_3696_;
goto v___jp_3666_;
}
else
{
lean_object* v___x_3697_; 
v___x_3697_ = l_Lean_MessageData_nil;
v___y_3667_ = v___y_3684_;
v___y_3668_ = v___y_3682_;
v___y_3669_ = v___y_3681_;
v___y_3670_ = v_msg_3680_;
v___y_3671_ = v___y_3683_;
v___y_3672_ = v___x_3697_;
goto v___jp_3666_;
}
}
else
{
uint8_t v___x_3698_; 
lean_inc(v_declName_3568_);
lean_inc_ref(v_env_3617_);
v___x_3698_ = l_Lean_isProtected(v_env_3617_, v_declName_3568_);
if (v___x_3698_ == 0)
{
uint8_t v___x_3699_; 
lean_inc(v_val_3610_);
v___x_3699_ = l_Lean_isProtected(v_env_3617_, v_val_3610_);
if (v___x_3699_ == 0)
{
lean_dec(v___x_3622_);
lean_dec_ref(v___x_3612_);
v_msg_3628_ = v_msg_3680_;
v___y_3629_ = v___y_3681_;
v___y_3630_ = v___y_3682_;
v___y_3631_ = v___y_3683_;
v___y_3632_ = v___y_3684_;
goto v___jp_3627_;
}
else
{
lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; uint8_t v___x_3703_; 
lean_inc(v___x_3622_);
v___x_3700_ = l_Lean_Name_componentsRev(v___x_3622_);
v___x_3701_ = lean_unsigned_to_nat(1u);
v___x_3702_ = l_List_lengthTR___redArg(v___x_3700_);
v___x_3703_ = lean_nat_dec_lt(v___x_3701_, v___x_3702_);
lean_dec(v___x_3702_);
if (v___x_3703_ == 0)
{
lean_object* v___x_3704_; 
lean_dec(v___x_3700_);
v___x_3704_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__21, &l_Lean_Linter_checkDeprecated___closed__21_once, _init_l_Lean_Linter_checkDeprecated___closed__21);
v___y_3647_ = v___y_3684_;
v___y_3648_ = v___y_3682_;
v___y_3649_ = v___y_3681_;
v___y_3650_ = v_msg_3680_;
v___y_3651_ = v___y_3683_;
v___y_3652_ = v___x_3704_;
goto v___jp_3646_;
}
else
{
lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; 
v___x_3705_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__23, &l_Lean_Linter_checkDeprecated___closed__23_once, _init_l_Lean_Linter_checkDeprecated___closed__23);
v___x_3706_ = lean_unsigned_to_nat(0u);
v___x_3707_ = l_List_get___redArg(v___x_3700_, v___x_3706_);
lean_dec(v___x_3700_);
v___x_3708_ = l_Lean_MessageData_ofName(v___x_3707_);
v___x_3709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3709_, 0, v___x_3705_);
lean_ctor_set(v___x_3709_, 1, v___x_3708_);
v___x_3710_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__25, &l_Lean_Linter_checkDeprecated___closed__25_once, _init_l_Lean_Linter_checkDeprecated___closed__25);
v___x_3711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3711_, 0, v___x_3709_);
lean_ctor_set(v___x_3711_, 1, v___x_3710_);
v___y_3647_ = v___y_3684_;
v___y_3648_ = v___y_3682_;
v___y_3649_ = v___y_3681_;
v___y_3650_ = v_msg_3680_;
v___y_3651_ = v___y_3683_;
v___y_3652_ = v___x_3711_;
goto v___jp_3646_;
}
}
}
else
{
lean_dec(v___x_3622_);
lean_dec_ref(v_env_3617_);
lean_dec_ref(v___x_3612_);
v_msg_3628_ = v_msg_3680_;
v___y_3629_ = v___y_3681_;
v___y_3630_ = v___y_3682_;
v___y_3631_ = v___y_3683_;
v___y_3632_ = v___y_3684_;
goto v___jp_3627_;
}
}
}
else
{
lean_dec(v___x_3622_);
lean_dec(v___x_3618_);
lean_dec_ref(v_env_3617_);
lean_dec_ref(v___x_3612_);
v_msg_3628_ = v_msg_3680_;
v___y_3629_ = v___y_3681_;
v___y_3630_ = v___y_3682_;
v___y_3631_ = v___y_3683_;
v___y_3632_ = v___y_3684_;
goto v___jp_3627_;
}
}
}
else
{
lean_object* v_a_3724_; lean_object* v___x_3726_; uint8_t v_isShared_3727_; uint8_t v_isSharedCheck_3731_; 
lean_dec(v_val_3624_);
lean_dec(v___x_3622_);
lean_dec(v_val_3621_);
lean_dec(v___x_3618_);
lean_dec_ref(v_env_3617_);
lean_dec_ref_known(v___x_3615_, 2);
lean_dec_ref(v___x_3612_);
lean_dec(v_val_3610_);
lean_dec(v_declName_3568_);
v_a_3724_ = lean_ctor_get(v___x_3625_, 0);
v_isSharedCheck_3731_ = !lean_is_exclusive(v___x_3625_);
if (v_isSharedCheck_3731_ == 0)
{
v___x_3726_ = v___x_3625_;
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
else
{
lean_inc(v_a_3724_);
lean_dec(v___x_3625_);
v___x_3726_ = lean_box(0);
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
v_resetjp_3725_:
{
lean_object* v___x_3729_; 
if (v_isShared_3727_ == 0)
{
v___x_3729_ = v___x_3726_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v_a_3724_);
v___x_3729_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
return v___x_3729_;
}
}
}
}
else
{
lean_dec(v___x_3623_);
lean_dec(v___x_3622_);
lean_dec(v_val_3621_);
lean_dec(v___x_3618_);
lean_dec_ref(v_env_3617_);
lean_dec_ref(v___x_3612_);
lean_dec(v_val_3610_);
v_extraMsg_3584_ = v___x_3615_;
v___y_3585_ = v_a_3570_;
v___y_3586_ = v_a_3571_;
v___y_3587_ = v_a_3572_;
v___y_3588_ = v_a_3573_;
goto v___jp_3583_;
}
}
else
{
lean_dec(v___x_3620_);
lean_dec(v___x_3618_);
lean_dec_ref(v_env_3617_);
lean_dec_ref(v___x_3612_);
lean_dec(v_val_3610_);
v_extraMsg_3584_ = v___x_3615_;
v___y_3585_ = v_a_3570_;
v___y_3586_ = v_a_3571_;
v___y_3587_ = v_a_3572_;
v___y_3588_ = v_a_3573_;
goto v___jp_3583_;
}
}
}
else
{
lean_object* v_val_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; 
lean_inc_ref(v_text_x3f_3607_);
lean_dec(v_val_3606_);
v_val_3732_ = lean_ctor_get(v_text_x3f_3607_, 0);
lean_inc(v_val_3732_);
lean_dec_ref_known(v_text_x3f_3607_, 1);
v___x_3733_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__27, &l_Lean_Linter_checkDeprecated___closed__27_once, _init_l_Lean_Linter_checkDeprecated___closed__27);
v___x_3734_ = l_Lean_stringToMessageData(v_val_3732_);
v___x_3735_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3735_, 0, v___x_3733_);
lean_ctor_set(v___x_3735_, 1, v___x_3734_);
v_extraMsg_3584_ = v___x_3735_;
v___y_3585_ = v_a_3570_;
v___y_3586_ = v_a_3571_;
v___y_3587_ = v_a_3572_;
v___y_3588_ = v_a_3573_;
goto v___jp_3583_;
}
}
else
{
lean_object* v___x_3736_; lean_object* v___x_3738_; 
lean_dec(v___x_3605_);
lean_dec(v_declName_3568_);
v___x_3736_ = lean_box(0);
if (v_isShared_3580_ == 0)
{
lean_ctor_set(v___x_3579_, 0, v___x_3736_);
v___x_3738_ = v___x_3579_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v___x_3736_);
v___x_3738_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
return v___x_3738_;
}
}
}
v___jp_3583_:
{
lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; 
v___x_3589_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_));
v___x_3590_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2_);
v___x_3591_ = l_Lean_MessageData_ofConstName(v_declName_3568_, v___x_3582_);
v___x_3592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3592_, 0, v___x_3590_);
lean_ctor_set(v___x_3592_, 1, v___x_3591_);
v___x_3593_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__1, &l_Lean_Linter_checkDeprecated___closed__1_once, _init_l_Lean_Linter_checkDeprecated___closed__1);
v___x_3594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3594_, 0, v___x_3592_);
lean_ctor_set(v___x_3594_, 1, v___x_3593_);
v___x_3595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3595_, 0, v___x_3594_);
lean_ctor_set(v___x_3595_, 1, v_extraMsg_3584_);
v___x_3596_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3596_, 0, v___x_3589_);
lean_ctor_set(v___x_3596_, 1, v___x_3595_);
v___x_3597_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_182370376____hygCtx___hyg_2__spec__6_spec__13_spec__22_spec__28_spec__34_spec__40(v___x_3596_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_);
return v___x_3597_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkDeprecated___boxed(lean_object* v_declName_3741_, lean_object* v_allowSuggestion_3742_, lean_object* v_a_3743_, lean_object* v_a_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_){
_start:
{
uint8_t v_allowSuggestion_boxed_3748_; lean_object* v_res_3749_; 
v_allowSuggestion_boxed_3748_ = lean_unbox(v_allowSuggestion_3742_);
v_res_3749_ = l_Lean_Linter_checkDeprecated(v_declName_3741_, v_allowSuggestion_boxed_3748_, v_a_3743_, v_a_3744_, v_a_3745_, v_a_3746_);
lean_dec(v_a_3746_);
lean_dec_ref(v_a_3745_);
lean_dec(v_a_3744_);
lean_dec_ref(v_a_3743_);
return v_res_3749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0(lean_object* v_o_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_){
_start:
{
lean_object* v___x_3756_; 
v___x_3756_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(v_o_3750_, v___y_3754_);
return v___x_3756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___boxed(lean_object* v_o_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_){
_start:
{
lean_object* v_res_3763_; 
v_res_3763_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0(v_o_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_);
lean_dec(v___y_3761_);
lean_dec_ref(v___y_3760_);
lean_dec(v___y_3759_);
lean_dec_ref(v___y_3758_);
return v_res_3763_;
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
